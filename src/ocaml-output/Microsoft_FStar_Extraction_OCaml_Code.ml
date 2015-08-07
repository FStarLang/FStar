
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

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("All")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Map")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let rec in_ns = (fun ( x ) -> (match (x) with
| ([], _59_7) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_59_17, _59_19) -> begin
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
(match ((let _70_24494 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _70_24494))) with
| None -> begin
(outsupport ns)
end
| _59_31 -> begin
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
| _59_43 -> begin
(let _59_46 = x
in (match (_59_46) with
| (ns, x) -> begin
(let _70_24499 = (path_of_ns currentModule ns)
in (_70_24499, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _70_24502 = (Support.String.get s 0)
in (Support.Char.lowercase _70_24502)) <> (Support.String.get s 0))) with
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
(let _70_24509 = (let _70_24508 = (let _70_24507 = (ptsym_of_symbol s)
in (_70_24507)::[])
in (Support.List.append p _70_24508))
in (Support.String.concat "." _70_24509))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _59_57 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_57) with
| (p, s) -> begin
(let s = (match (((let _70_24514 = (Support.String.get s 0)
in (Support.Char.uppercase _70_24514)) <> (Support.String.get s 0))) with
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
| (y, _59_65, _59_67) -> begin
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
| (y, _59_75) -> begin
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
| (y, _59_83) -> begin
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
| (y, _59_91) -> begin
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
| (_59_132, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_59_136, _59_138) -> begin
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
| _59_156 -> begin
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
(let _70_24556 = (let _70_24555 = (encode_char c)
in (Support.String.strcat "\'" _70_24555))
in (Support.String.strcat _70_24556 "\'"))
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
in (let _70_24568 = (Support.All.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _70_24568)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _70_24571 = (let _70_24570 = (let _70_24569 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_24569 doc))
in (FSharp_Format.hbox _70_24570))
in (FSharp_Format.parens _70_24571))
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
| _59_198 -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _70_24574 = (let _70_24573 = (let _70_24572 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_24572 args))
in (FSharp_Format.hbox _70_24573))
in (FSharp_Format.parens _70_24574)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _70_24576 = (let _70_24575 = (as_standard_type name)
in (Support.Option.get _70_24575))
in (Support.Prims.snd _70_24576))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _70_24580 = (let _70_24579 = (let _70_24578 = (let _70_24577 = (FSharp_Format.text name)
in (_70_24577)::[])
in (args)::_70_24578)
in (FSharp_Format.reduce1 _70_24579))
in (FSharp_Format.hbox _70_24580))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, _59_204, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _70_24585 = (let _70_24584 = (let _70_24583 = (let _70_24582 = (let _70_24581 = (FSharp_Format.text " -> ")
in (_70_24581)::(d2)::[])
in (d1)::_70_24582)
in (FSharp_Format.reduce1 _70_24583))
in (FSharp_Format.hbox _70_24584))
in (maybe_paren outer t_prio_fun _70_24585))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _70_24590 = (let _70_24589 = (let _70_24588 = (let _70_24587 = (let _70_24586 = (FSharp_Format.text " ")
in (_70_24586)::(d1)::[])
in (d2)::_70_24587)
in (FSharp_Format.reduce1 _70_24588))
in (FSharp_Format.hbox _70_24589))
in (maybe_paren outer t_prio_fun _70_24590))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_24615 = (let _70_24614 = (let _70_24613 = (FSharp_Format.text "Obj.magic ")
in (_70_24613)::(doc)::[])
in (FSharp_Format.reduce _70_24614))
in (FSharp_Format.parens _70_24615)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _70_24619 = (let _70_24618 = (let _70_24617 = (FSharp_Format.text ";")
in (_70_24617)::(FSharp_Format.hardline)::[])
in (d)::_70_24618)
in (FSharp_Format.reduce _70_24619))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _70_24620 = (string_of_mlconstant c)
in (FSharp_Format.text _70_24620))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((x, _59_238)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _70_24621 = (ptsym currentModule path)
in (FSharp_Format.text _70_24621))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_250 ) -> (match (_59_250) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_24628 = (let _70_24627 = (let _70_24624 = (ptsym currentModule (path, name))
in (FSharp_Format.text _70_24624))
in (let _70_24626 = (let _70_24625 = (FSharp_Format.text "=")
in (_70_24625)::(doc)::[])
in (_70_24627)::_70_24626))
in (FSharp_Format.reduce1 _70_24628)))
end))
in (let _70_24631 = (let _70_24630 = (FSharp_Format.text "; ")
in (let _70_24629 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_24630 _70_24629)))
in (FSharp_Format.cbrackets _70_24631)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_24633 = (let _70_24632 = (as_standard_constructor ctor)
in (Support.Option.get _70_24632))
in (Support.Prims.snd _70_24633))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_24635 = (let _70_24634 = (as_standard_constructor ctor)
in (Support.Option.get _70_24634))
in (Support.Prims.snd _70_24635))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _70_24639 = (let _70_24638 = (FSharp_Format.parens x)
in (let _70_24637 = (let _70_24636 = (FSharp_Format.text "::")
in (_70_24636)::(xs)::[])
in (_70_24638)::_70_24637))
in (FSharp_Format.reduce _70_24639))
end
| (_59_269, _59_271) -> begin
(let _70_24645 = (let _70_24644 = (FSharp_Format.text name)
in (let _70_24643 = (let _70_24642 = (let _70_24641 = (let _70_24640 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_24640 args))
in (FSharp_Format.parens _70_24641))
in (_70_24642)::[])
in (_70_24644)::_70_24643))
in (FSharp_Format.reduce1 _70_24645))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _70_24647 = (let _70_24646 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_24646 docs))
in (FSharp_Format.parens _70_24647))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _70_24653 = (let _70_24652 = (let _70_24651 = (let _70_24650 = (let _70_24649 = (let _70_24648 = (FSharp_Format.text "in")
in (_70_24648)::(body)::[])
in (FSharp_Format.reduce1 _70_24649))
in (_70_24650)::[])
in (doc)::_70_24651)
in (FSharp_Format.combine FSharp_Format.hardline _70_24652))
in (FSharp_Format.parens _70_24653))))
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
| _59_321 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _70_24654 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _70_24654))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _70_24660 = (let _70_24659 = (let _70_24658 = (FSharp_Format.text ".")
in (let _70_24657 = (let _70_24656 = (let _70_24655 = (ptsym currentModule f)
in (FSharp_Format.text _70_24655))
in (_70_24656)::[])
in (_70_24658)::_70_24657))
in (e)::_70_24659)
in (FSharp_Format.reduce _70_24660))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _59_339 ) -> (match (_59_339) with
| ((x, _59_336), xt) -> begin
(let _70_24667 = (let _70_24666 = (FSharp_Format.text "(")
in (let _70_24665 = (let _70_24664 = (FSharp_Format.text x)
in (let _70_24663 = (let _70_24662 = (FSharp_Format.text ")")
in (_70_24662)::[])
in (_70_24664)::_70_24663))
in (_70_24666)::_70_24665))
in (FSharp_Format.reduce1 _70_24667))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _70_24673 = (let _70_24672 = (FSharp_Format.text "fun")
in (let _70_24671 = (let _70_24670 = (FSharp_Format.reduce1 ids)
in (let _70_24669 = (let _70_24668 = (FSharp_Format.text "->")
in (_70_24668)::(body)::[])
in (_70_24670)::_70_24669))
in (_70_24672)::_70_24671))
in (FSharp_Format.reduce1 _70_24673))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_24686 = (let _70_24685 = (let _70_24680 = (let _70_24679 = (FSharp_Format.text "if")
in (let _70_24678 = (let _70_24677 = (let _70_24676 = (FSharp_Format.text "then")
in (let _70_24675 = (let _70_24674 = (FSharp_Format.text "begin")
in (_70_24674)::[])
in (_70_24676)::_70_24675))
in (cond)::_70_24677)
in (_70_24679)::_70_24678))
in (FSharp_Format.reduce1 _70_24680))
in (let _70_24684 = (let _70_24683 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _70_24682 = (let _70_24681 = (FSharp_Format.text "end")
in (_70_24681)::[])
in (_70_24683)::_70_24682))
in (_70_24685)::_70_24684))
in (FSharp_Format.combine FSharp_Format.hardline _70_24686))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_24709 = (let _70_24708 = (let _70_24693 = (let _70_24692 = (FSharp_Format.text "if")
in (let _70_24691 = (let _70_24690 = (let _70_24689 = (FSharp_Format.text "then")
in (let _70_24688 = (let _70_24687 = (FSharp_Format.text "begin")
in (_70_24687)::[])
in (_70_24689)::_70_24688))
in (cond)::_70_24690)
in (_70_24692)::_70_24691))
in (FSharp_Format.reduce1 _70_24693))
in (let _70_24707 = (let _70_24706 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _70_24705 = (let _70_24704 = (let _70_24699 = (let _70_24698 = (FSharp_Format.text "end")
in (let _70_24697 = (let _70_24696 = (FSharp_Format.text "else")
in (let _70_24695 = (let _70_24694 = (FSharp_Format.text "begin")
in (_70_24694)::[])
in (_70_24696)::_70_24695))
in (_70_24698)::_70_24697))
in (FSharp_Format.reduce1 _70_24699))
in (let _70_24703 = (let _70_24702 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _70_24701 = (let _70_24700 = (FSharp_Format.text "end")
in (_70_24700)::[])
in (_70_24702)::_70_24701))
in (_70_24704)::_70_24703))
in (_70_24706)::_70_24705))
in (_70_24708)::_70_24707))
in (FSharp_Format.combine FSharp_Format.hardline _70_24709))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _70_24716 = (let _70_24715 = (let _70_24714 = (FSharp_Format.text "match")
in (let _70_24713 = (let _70_24712 = (FSharp_Format.parens cond)
in (let _70_24711 = (let _70_24710 = (FSharp_Format.text "with")
in (_70_24710)::[])
in (_70_24712)::_70_24711))
in (_70_24714)::_70_24713))
in (FSharp_Format.reduce1 _70_24715))
in (_70_24716)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _70_24721 = (let _70_24720 = (FSharp_Format.text "raise")
in (let _70_24719 = (let _70_24718 = (let _70_24717 = (ptctor currentModule exn)
in (FSharp_Format.text _70_24717))
in (_70_24718)::[])
in (_70_24720)::_70_24719))
in (FSharp_Format.reduce1 _70_24721))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _70_24730 = (let _70_24729 = (FSharp_Format.text "raise")
in (let _70_24728 = (let _70_24727 = (let _70_24722 = (ptctor currentModule exn)
in (FSharp_Format.text _70_24722))
in (let _70_24726 = (let _70_24725 = (let _70_24724 = (let _70_24723 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_24723 args))
in (FSharp_Format.parens _70_24724))
in (_70_24725)::[])
in (_70_24727)::_70_24726))
in (_70_24729)::_70_24728))
in (FSharp_Format.reduce1 _70_24730)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _70_24747 = (let _70_24746 = (let _70_24734 = (let _70_24733 = (FSharp_Format.text "try")
in (let _70_24732 = (let _70_24731 = (FSharp_Format.text "begin")
in (_70_24731)::[])
in (_70_24733)::_70_24732))
in (FSharp_Format.reduce1 _70_24734))
in (let _70_24745 = (let _70_24744 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_24743 = (let _70_24742 = (let _70_24738 = (let _70_24737 = (FSharp_Format.text "end")
in (let _70_24736 = (let _70_24735 = (FSharp_Format.text "with")
in (_70_24735)::[])
in (_70_24737)::_70_24736))
in (FSharp_Format.reduce1 _70_24738))
in (let _70_24741 = (let _70_24740 = (let _70_24739 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _70_24739))
in (_70_24740)::[])
in (_70_24742)::_70_24741))
in (_70_24744)::_70_24743))
in (_70_24746)::_70_24745))
in (FSharp_Format.combine FSharp_Format.hardline _70_24747))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _59_387 = (let _70_24752 = (as_bin_op p)
in (Support.Option.get _70_24752))
in (match (_59_387) with
| (_59_384, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _70_24755 = (let _70_24754 = (let _70_24753 = (FSharp_Format.text txt)
in (_70_24753)::(e2)::[])
in (e1)::_70_24754)
in (FSharp_Format.reduce1 _70_24755))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _59_397 = (let _70_24759 = (as_uni_op p)
in (Support.Option.get _70_24759))
in (match (_59_397) with
| (_59_395, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _70_24763 = (let _70_24762 = (FSharp_Format.text txt)
in (let _70_24761 = (let _70_24760 = (FSharp_Format.parens e1)
in (_70_24760)::[])
in (_70_24762)::_70_24761))
in (FSharp_Format.reduce1 _70_24763))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _70_24766 = (string_of_mlconstant c)
in (FSharp_Format.text _70_24766))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_414 ) -> (match (_59_414) with
| (name, p) -> begin
(let _70_24775 = (let _70_24774 = (let _70_24769 = (ptsym currentModule (path, name))
in (FSharp_Format.text _70_24769))
in (let _70_24773 = (let _70_24772 = (FSharp_Format.text "=")
in (let _70_24771 = (let _70_24770 = (doc_of_pattern currentModule p)
in (_70_24770)::[])
in (_70_24772)::_70_24771))
in (_70_24774)::_70_24773))
in (FSharp_Format.reduce1 _70_24775))
end))
in (let _70_24778 = (let _70_24777 = (FSharp_Format.text "; ")
in (let _70_24776 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_24777 _70_24776)))
in (FSharp_Format.cbrackets _70_24778)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_24780 = (let _70_24779 = (as_standard_constructor ctor)
in (Support.Option.get _70_24779))
in (Support.Prims.snd _70_24780))
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
(let _70_24782 = (let _70_24781 = (as_standard_constructor ctor)
in (Support.Option.get _70_24781))
in (Support.Prims.snd _70_24782))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _70_24785 = (let _70_24784 = (let _70_24783 = (FSharp_Format.text "::")
in (_70_24783)::(xs)::[])
in (x)::_70_24784)
in (FSharp_Format.reduce _70_24785))
end
| (_59_432, _59_434) -> begin
(let _70_24791 = (let _70_24790 = (FSharp_Format.text name)
in (let _70_24789 = (let _70_24788 = (let _70_24787 = (let _70_24786 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_24786 ps))
in (FSharp_Format.parens _70_24787))
in (_70_24788)::[])
in (_70_24790)::_70_24789))
in (FSharp_Format.reduce1 _70_24791))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _70_24793 = (let _70_24792 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_24792 ps))
in (FSharp_Format.parens _70_24793)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _70_24794 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _70_24794 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _59_448 ) -> (match (_59_448) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _70_24800 = (let _70_24799 = (FSharp_Format.text "|")
in (let _70_24798 = (let _70_24797 = (doc_of_pattern currentModule p)
in (_70_24797)::[])
in (_70_24799)::_70_24798))
in (FSharp_Format.reduce1 _70_24800))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _70_24806 = (let _70_24805 = (FSharp_Format.text "|")
in (let _70_24804 = (let _70_24803 = (doc_of_pattern currentModule p)
in (let _70_24802 = (let _70_24801 = (FSharp_Format.text "when")
in (_70_24801)::(c)::[])
in (_70_24803)::_70_24802))
in (_70_24805)::_70_24804))
in (FSharp_Format.reduce1 _70_24806)))
end)
in (let _70_24817 = (let _70_24816 = (let _70_24811 = (let _70_24810 = (let _70_24809 = (FSharp_Format.text "->")
in (let _70_24808 = (let _70_24807 = (FSharp_Format.text "begin")
in (_70_24807)::[])
in (_70_24809)::_70_24808))
in (case)::_70_24810)
in (FSharp_Format.reduce1 _70_24811))
in (let _70_24815 = (let _70_24814 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_24813 = (let _70_24812 = (FSharp_Format.text "end")
in (_70_24812)::[])
in (_70_24814)::_70_24813))
in (_70_24816)::_70_24815))
in (FSharp_Format.combine FSharp_Format.hardline _70_24817)))
end))
and doc_of_lets = (fun ( currentModule ) ( _59_457 ) -> (match (_59_457) with
| (rec_, lets) -> begin
(let for1 = (fun ( _59_464 ) -> (match (_59_464) with
| {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = name; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = tys; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = _59_461; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (Support.List.map (fun ( _59_470 ) -> (match (_59_470) with
| (x, _59_469) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _70_24828 = (let _70_24827 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _70_24826 = (let _70_24825 = (FSharp_Format.reduce1 ids)
in (let _70_24824 = (let _70_24823 = (FSharp_Format.text "=")
in (_70_24823)::(e)::[])
in (_70_24825)::_70_24824))
in (_70_24827)::_70_24826))
in (FSharp_Format.reduce1 _70_24828)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _70_24832 = (let _70_24831 = (FSharp_Format.text "let")
in (let _70_24830 = (let _70_24829 = (FSharp_Format.text "rec")
in (_70_24829)::[])
in (_70_24831)::_70_24830))
in (FSharp_Format.reduce1 _70_24832))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _70_24836 = (let _70_24835 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_70_24835)::(doc)::[])
in (FSharp_Format.reduce1 _70_24836))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( currentModule ) ( decls ) -> (let for1 = (fun ( _59_483 ) -> (match (_59_483) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
end
| _59_488 -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _70_24845 = (let _70_24844 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_24844 doc))
in (FSharp_Format.parens _70_24845)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _59_501 ) -> (match (_59_501) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _70_24852 = (let _70_24851 = (let _70_24850 = (FSharp_Format.text ":")
in (_70_24850)::(ty)::[])
in (name)::_70_24851)
in (FSharp_Format.reduce1 _70_24852))))
end))
in (let _70_24855 = (let _70_24854 = (FSharp_Format.text "; ")
in (let _70_24853 = (Support.List.map forfield fields)
in (FSharp_Format.combine _70_24854 _70_24853)))
in (FSharp_Format.cbrackets _70_24855)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _59_509 ) -> (match (_59_509) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _59_512 -> begin
(let tys = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _70_24858 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_24858 tys))
in (let _70_24862 = (let _70_24861 = (FSharp_Format.text name)
in (let _70_24860 = (let _70_24859 = (FSharp_Format.text "of")
in (_70_24859)::(tys)::[])
in (_70_24861)::_70_24860))
in (FSharp_Format.reduce1 _70_24862))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _70_24865 = (let _70_24864 = (FSharp_Format.text "|")
in (_70_24864)::(d)::[])
in (FSharp_Format.reduce1 _70_24865))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _70_24869 = (let _70_24868 = (let _70_24867 = (let _70_24866 = (ptsym currentModule ([], x))
in (FSharp_Format.text _70_24866))
in (_70_24867)::[])
in (tparams)::_70_24868)
in (FSharp_Format.reduce1 _70_24869))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _70_24874 = (let _70_24873 = (let _70_24872 = (let _70_24871 = (let _70_24870 = (FSharp_Format.text "=")
in (_70_24870)::[])
in (doc)::_70_24871)
in (FSharp_Format.reduce1 _70_24872))
in (_70_24873)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _70_24874)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _70_24879 = (let _70_24878 = (FSharp_Format.text "type")
in (let _70_24877 = (let _70_24876 = (let _70_24875 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _70_24875 doc))
in (_70_24876)::[])
in (_70_24878)::_70_24877))
in (FSharp_Format.reduce1 _70_24879))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _70_24899 = (let _70_24898 = (let _70_24891 = (let _70_24890 = (FSharp_Format.text "module")
in (let _70_24889 = (let _70_24888 = (FSharp_Format.text x)
in (let _70_24887 = (let _70_24886 = (FSharp_Format.text "=")
in (_70_24886)::[])
in (_70_24888)::_70_24887))
in (_70_24890)::_70_24889))
in (FSharp_Format.reduce1 _70_24891))
in (let _70_24897 = (let _70_24896 = (doc_of_sig currentModule subsig)
in (let _70_24895 = (let _70_24894 = (let _70_24893 = (let _70_24892 = (FSharp_Format.text "end")
in (_70_24892)::[])
in (FSharp_Format.reduce1 _70_24893))
in (_70_24894)::[])
in (_70_24896)::_70_24895))
in (_70_24898)::_70_24897))
in (FSharp_Format.combine FSharp_Format.hardline _70_24899))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _70_24903 = (let _70_24902 = (FSharp_Format.text "exception")
in (let _70_24901 = (let _70_24900 = (FSharp_Format.text x)
in (_70_24900)::[])
in (_70_24902)::_70_24901))
in (FSharp_Format.reduce1 _70_24903))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _70_24905 = (let _70_24904 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_24904 args))
in (FSharp_Format.parens _70_24905))
in (let _70_24911 = (let _70_24910 = (FSharp_Format.text "exception")
in (let _70_24909 = (let _70_24908 = (FSharp_Format.text x)
in (let _70_24907 = (let _70_24906 = (FSharp_Format.text "of")
in (_70_24906)::(args)::[])
in (_70_24908)::_70_24907))
in (_70_24910)::_70_24909))
in (FSharp_Format.reduce1 _70_24911))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val ((x, (_59_543, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _70_24917 = (let _70_24916 = (FSharp_Format.text "val")
in (let _70_24915 = (let _70_24914 = (FSharp_Format.text x)
in (let _70_24913 = (let _70_24912 = (FSharp_Format.text ": ")
in (_70_24912)::(ty)::[])
in (_70_24914)::_70_24913))
in (_70_24916)::_70_24915))
in (FSharp_Format.reduce1 _70_24917)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _70_24928 = (let _70_24927 = (FSharp_Format.text "exception")
in (let _70_24926 = (let _70_24925 = (FSharp_Format.text x)
in (_70_24925)::[])
in (_70_24927)::_70_24926))
in (FSharp_Format.reduce1 _70_24928))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _70_24930 = (let _70_24929 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_24929 args))
in (FSharp_Format.parens _70_24930))
in (let _70_24936 = (let _70_24935 = (FSharp_Format.text "exception")
in (let _70_24934 = (let _70_24933 = (FSharp_Format.text x)
in (let _70_24932 = (let _70_24931 = (FSharp_Format.text "of")
in (_70_24931)::(args)::[])
in (_70_24933)::_70_24932))
in (_70_24935)::_70_24934))
in (FSharp_Format.reduce1 _70_24936))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _70_24944 = (let _70_24943 = (FSharp_Format.text "let")
in (let _70_24942 = (let _70_24941 = (FSharp_Format.text "_")
in (let _70_24940 = (let _70_24939 = (FSharp_Format.text "=")
in (let _70_24938 = (let _70_24937 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_70_24937)::[])
in (_70_24939)::_70_24938))
in (_70_24941)::_70_24940))
in (_70_24943)::_70_24942))
in (FSharp_Format.reduce1 _70_24944))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _59_582 ) -> (match (_59_582) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _59_589 ) -> (match (_59_589) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _70_24963 = (let _70_24962 = (FSharp_Format.text "module")
in (let _70_24961 = (let _70_24960 = (FSharp_Format.text x)
in (let _70_24959 = (let _70_24958 = (FSharp_Format.text ":")
in (let _70_24957 = (let _70_24956 = (FSharp_Format.text "sig")
in (_70_24956)::[])
in (_70_24958)::_70_24957))
in (_70_24960)::_70_24959))
in (_70_24962)::_70_24961))
in (FSharp_Format.reduce1 _70_24963))
in (let tail = (let _70_24965 = (let _70_24964 = (FSharp_Format.text "end")
in (_70_24964)::[])
in (FSharp_Format.reduce1 _70_24965))
in (let doc = (Support.Option.map (fun ( _59_595 ) -> (match (_59_595) with
| (s, _59_594) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _70_24975 = (let _70_24974 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_24973 = (let _70_24972 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_24971 = (let _70_24970 = (FSharp_Format.reduce sub)
in (let _70_24969 = (let _70_24968 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_24968)::[])
in (_70_24970)::_70_24969))
in (_70_24972)::_70_24971))
in (_70_24974)::_70_24973))
in (FSharp_Format.reduce _70_24975)))))))
end))
and for1_mod = (fun ( istop ) ( _59_608 ) -> (match (_59_608) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _59_609 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _70_24985 = (match ((not (istop))) with
| true -> begin
(let _70_24984 = (FSharp_Format.text "module")
in (let _70_24983 = (let _70_24982 = (FSharp_Format.text x)
in (let _70_24981 = (let _70_24980 = (FSharp_Format.text "=")
in (let _70_24979 = (let _70_24978 = (FSharp_Format.text "struct")
in (_70_24978)::[])
in (_70_24980)::_70_24979))
in (_70_24982)::_70_24981))
in (_70_24984)::_70_24983))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _70_24985))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _70_24987 = (let _70_24986 = (FSharp_Format.text "end")
in (_70_24986)::[])
in (FSharp_Format.reduce1 _70_24987))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _59_616 ) -> (match (_59_616) with
| (_59_614, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _70_24997 = (let _70_24996 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_24995 = (let _70_24994 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_24993 = (let _70_24992 = (FSharp_Format.reduce sub)
in (let _70_24991 = (let _70_24990 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_24990)::[])
in (_70_24992)::_70_24991))
in (_70_24994)::_70_24993))
in (_70_24996)::_70_24995))
in (FSharp_Format.reduce _70_24997))))))))
end))
in (let docs = (Support.List.map (fun ( _59_627 ) -> (match (_59_627) with
| (x, s, m) -> begin
(let _70_24999 = (for1_mod true (x, s, m))
in (x, _70_24999))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))





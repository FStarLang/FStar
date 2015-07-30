
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
(match ((let _65_24111 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _65_24111))) with
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
(let _65_24116 = (path_of_ns currentModule ns)
in (_65_24116, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _65_24119 = (Support.String.get s 0)
in (Support.Char.lowercase _65_24119)) <> (Support.String.get s 0))) with
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
(let _65_24126 = (let _65_24125 = (let _65_24124 = (ptsym_of_symbol s)
in (_65_24124)::[])
in (Support.List.append p _65_24125))
in (Support.String.concat "." _65_24126))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _59_57 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_57) with
| (p, s) -> begin
(let s = (match (((let _65_24131 = (Support.String.get s 0)
in (Support.Char.uppercase _65_24131)) <> (Support.String.get s 0))) with
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
(let _65_24173 = (let _65_24172 = (encode_char c)
in (Support.String.strcat "\'" _65_24172))
in (Support.String.strcat _65_24173 "\'"))
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
in (let _65_24185 = (Support.Prims.pipe_left escape_tyvar (Microsoft_FStar_Backends_ML_Syntax.idsym x))
in (FSharp_Format.text _65_24185)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _65_24188 = (let _65_24187 = (let _65_24186 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_24186 doc))
in (FSharp_Format.hbox _65_24187))
in (FSharp_Format.parens _65_24188))
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
in (let _65_24191 = (let _65_24190 = (let _65_24189 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24189 args))
in (FSharp_Format.hbox _65_24190))
in (FSharp_Format.parens _65_24191)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _65_24193 = (let _65_24192 = (as_standard_type name)
in (Support.Option.get _65_24192))
in (Support.Prims.snd _65_24193))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _65_24197 = (let _65_24196 = (let _65_24195 = (let _65_24194 = (FSharp_Format.text name)
in (_65_24194)::[])
in (args)::_65_24195)
in (FSharp_Format.reduce1 _65_24196))
in (FSharp_Format.hbox _65_24197))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _65_24202 = (let _65_24201 = (let _65_24200 = (let _65_24199 = (let _65_24198 = (FSharp_Format.text " -> ")
in (_65_24198)::(d2)::[])
in (d1)::_65_24199)
in (FSharp_Format.reduce1 _65_24200))
in (FSharp_Format.hbox _65_24201))
in (maybe_paren outer t_prio_fun _65_24202))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _65_24207 = (let _65_24206 = (let _65_24205 = (let _65_24204 = (let _65_24203 = (FSharp_Format.text " ")
in (_65_24203)::(d1)::[])
in (d2)::_65_24204)
in (FSharp_Format.reduce1 _65_24205))
in (FSharp_Format.hbox _65_24206))
in (maybe_paren outer t_prio_fun _65_24207))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Backends_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_24232 = (let _65_24231 = (let _65_24230 = (FSharp_Format.text "Obj.magic ")
in (_65_24230)::(doc)::[])
in (FSharp_Format.reduce _65_24231))
in (FSharp_Format.parens _65_24232)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _65_24236 = (let _65_24235 = (let _65_24234 = (FSharp_Format.text ";")
in (_65_24234)::(FSharp_Format.hardline)::[])
in (d)::_65_24235)
in (FSharp_Format.reduce _65_24236))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _65_24237 = (string_of_mlconstant c)
in (FSharp_Format.text _65_24237))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _65_24238 = (ptsym currentModule path)
in (FSharp_Format.text _65_24238))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_250 ) -> (match (_59_250) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_24245 = (let _65_24244 = (let _65_24241 = (ptsym currentModule (path, name))
in (FSharp_Format.text _65_24241))
in (let _65_24243 = (let _65_24242 = (FSharp_Format.text "=")
in (_65_24242)::(doc)::[])
in (_65_24244)::_65_24243))
in (FSharp_Format.reduce1 _65_24245)))
end))
in (let _65_24248 = (let _65_24247 = (FSharp_Format.text "; ")
in (let _65_24246 = (Support.List.map for1 fields)
in (FSharp_Format.combine _65_24247 _65_24246)))
in (FSharp_Format.cbrackets _65_24248)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_24250 = (let _65_24249 = (as_standard_constructor ctor)
in (Support.Option.get _65_24249))
in (Support.Prims.snd _65_24250))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_24252 = (let _65_24251 = (as_standard_constructor ctor)
in (Support.Option.get _65_24251))
in (Support.Prims.snd _65_24252))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _65_24256 = (let _65_24255 = (FSharp_Format.parens x)
in (let _65_24254 = (let _65_24253 = (FSharp_Format.text "::")
in (_65_24253)::(xs)::[])
in (_65_24255)::_65_24254))
in (FSharp_Format.reduce _65_24256))
end
| (_, _) -> begin
(let _65_24262 = (let _65_24261 = (FSharp_Format.text name)
in (let _65_24260 = (let _65_24259 = (let _65_24258 = (let _65_24257 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24257 args))
in (FSharp_Format.parens _65_24258))
in (_65_24259)::[])
in (_65_24261)::_65_24260))
in (FSharp_Format.reduce1 _65_24262))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _65_24264 = (let _65_24263 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24263 docs))
in (FSharp_Format.parens _65_24264))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _65_24270 = (let _65_24269 = (let _65_24268 = (let _65_24267 = (let _65_24266 = (let _65_24265 = (FSharp_Format.text "in")
in (_65_24265)::(body)::[])
in (FSharp_Format.reduce1 _65_24266))
in (_65_24267)::[])
in (doc)::_65_24268)
in (FSharp_Format.combine FSharp_Format.hardline _65_24269))
in (FSharp_Format.parens _65_24270))))
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
in (let _65_24271 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _65_24271))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _65_24277 = (let _65_24276 = (let _65_24275 = (FSharp_Format.text ".")
in (let _65_24274 = (let _65_24273 = (let _65_24272 = (ptsym currentModule f)
in (FSharp_Format.text _65_24272))
in (_65_24273)::[])
in (_65_24275)::_65_24274))
in (e)::_65_24276)
in (FSharp_Format.reduce _65_24277))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _59_339 ) -> (match (_59_339) with
| ((x, _), xt) -> begin
(let _65_24284 = (let _65_24283 = (FSharp_Format.text "(")
in (let _65_24282 = (let _65_24281 = (FSharp_Format.text x)
in (let _65_24280 = (let _65_24279 = (FSharp_Format.text ")")
in (_65_24279)::[])
in (_65_24281)::_65_24280))
in (_65_24283)::_65_24282))
in (FSharp_Format.reduce1 _65_24284))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _65_24290 = (let _65_24289 = (FSharp_Format.text "fun")
in (let _65_24288 = (let _65_24287 = (FSharp_Format.reduce1 ids)
in (let _65_24286 = (let _65_24285 = (FSharp_Format.text "->")
in (_65_24285)::(body)::[])
in (_65_24287)::_65_24286))
in (_65_24289)::_65_24288))
in (FSharp_Format.reduce1 _65_24290))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _65_24303 = (let _65_24302 = (let _65_24297 = (let _65_24296 = (FSharp_Format.text "if")
in (let _65_24295 = (let _65_24294 = (let _65_24293 = (FSharp_Format.text "then")
in (let _65_24292 = (let _65_24291 = (FSharp_Format.text "begin")
in (_65_24291)::[])
in (_65_24293)::_65_24292))
in (cond)::_65_24294)
in (_65_24296)::_65_24295))
in (FSharp_Format.reduce1 _65_24297))
in (let _65_24301 = (let _65_24300 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _65_24299 = (let _65_24298 = (FSharp_Format.text "end")
in (_65_24298)::[])
in (_65_24300)::_65_24299))
in (_65_24302)::_65_24301))
in (FSharp_Format.combine FSharp_Format.hardline _65_24303))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _65_24326 = (let _65_24325 = (let _65_24310 = (let _65_24309 = (FSharp_Format.text "if")
in (let _65_24308 = (let _65_24307 = (let _65_24306 = (FSharp_Format.text "then")
in (let _65_24305 = (let _65_24304 = (FSharp_Format.text "begin")
in (_65_24304)::[])
in (_65_24306)::_65_24305))
in (cond)::_65_24307)
in (_65_24309)::_65_24308))
in (FSharp_Format.reduce1 _65_24310))
in (let _65_24324 = (let _65_24323 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _65_24322 = (let _65_24321 = (let _65_24316 = (let _65_24315 = (FSharp_Format.text "end")
in (let _65_24314 = (let _65_24313 = (FSharp_Format.text "else")
in (let _65_24312 = (let _65_24311 = (FSharp_Format.text "begin")
in (_65_24311)::[])
in (_65_24313)::_65_24312))
in (_65_24315)::_65_24314))
in (FSharp_Format.reduce1 _65_24316))
in (let _65_24320 = (let _65_24319 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _65_24318 = (let _65_24317 = (FSharp_Format.text "end")
in (_65_24317)::[])
in (_65_24319)::_65_24318))
in (_65_24321)::_65_24320))
in (_65_24323)::_65_24322))
in (_65_24325)::_65_24324))
in (FSharp_Format.combine FSharp_Format.hardline _65_24326))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _65_24333 = (let _65_24332 = (let _65_24331 = (FSharp_Format.text "match")
in (let _65_24330 = (let _65_24329 = (FSharp_Format.parens cond)
in (let _65_24328 = (let _65_24327 = (FSharp_Format.text "with")
in (_65_24327)::[])
in (_65_24329)::_65_24328))
in (_65_24331)::_65_24330))
in (FSharp_Format.reduce1 _65_24332))
in (_65_24333)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _65_24338 = (let _65_24337 = (FSharp_Format.text "raise")
in (let _65_24336 = (let _65_24335 = (let _65_24334 = (ptctor currentModule exn)
in (FSharp_Format.text _65_24334))
in (_65_24335)::[])
in (_65_24337)::_65_24336))
in (FSharp_Format.reduce1 _65_24338))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _65_24347 = (let _65_24346 = (FSharp_Format.text "raise")
in (let _65_24345 = (let _65_24344 = (let _65_24339 = (ptctor currentModule exn)
in (FSharp_Format.text _65_24339))
in (let _65_24343 = (let _65_24342 = (let _65_24341 = (let _65_24340 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24340 args))
in (FSharp_Format.parens _65_24341))
in (_65_24342)::[])
in (_65_24344)::_65_24343))
in (_65_24346)::_65_24345))
in (FSharp_Format.reduce1 _65_24347)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _65_24364 = (let _65_24363 = (let _65_24351 = (let _65_24350 = (FSharp_Format.text "try")
in (let _65_24349 = (let _65_24348 = (FSharp_Format.text "begin")
in (_65_24348)::[])
in (_65_24350)::_65_24349))
in (FSharp_Format.reduce1 _65_24351))
in (let _65_24362 = (let _65_24361 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_24360 = (let _65_24359 = (let _65_24355 = (let _65_24354 = (FSharp_Format.text "end")
in (let _65_24353 = (let _65_24352 = (FSharp_Format.text "with")
in (_65_24352)::[])
in (_65_24354)::_65_24353))
in (FSharp_Format.reduce1 _65_24355))
in (let _65_24358 = (let _65_24357 = (let _65_24356 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _65_24356))
in (_65_24357)::[])
in (_65_24359)::_65_24358))
in (_65_24361)::_65_24360))
in (_65_24363)::_65_24362))
in (FSharp_Format.combine FSharp_Format.hardline _65_24364))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _59_387 = (let _65_24369 = (as_bin_op p)
in (Support.Option.get _65_24369))
in (match (_59_387) with
| (_, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _65_24372 = (let _65_24371 = (let _65_24370 = (FSharp_Format.text txt)
in (_65_24370)::(e2)::[])
in (e1)::_65_24371)
in (FSharp_Format.reduce1 _65_24372))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _59_397 = (let _65_24376 = (as_uni_op p)
in (Support.Option.get _65_24376))
in (match (_59_397) with
| (_, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _65_24380 = (let _65_24379 = (FSharp_Format.text txt)
in (let _65_24378 = (let _65_24377 = (FSharp_Format.parens e1)
in (_65_24377)::[])
in (_65_24379)::_65_24378))
in (FSharp_Format.reduce1 _65_24380))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _65_24383 = (string_of_mlconstant c)
in (FSharp_Format.text _65_24383))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_414 ) -> (match (_59_414) with
| (name, p) -> begin
(let _65_24392 = (let _65_24391 = (let _65_24386 = (ptsym currentModule (path, name))
in (FSharp_Format.text _65_24386))
in (let _65_24390 = (let _65_24389 = (FSharp_Format.text "=")
in (let _65_24388 = (let _65_24387 = (doc_of_pattern currentModule p)
in (_65_24387)::[])
in (_65_24389)::_65_24388))
in (_65_24391)::_65_24390))
in (FSharp_Format.reduce1 _65_24392))
end))
in (let _65_24395 = (let _65_24394 = (FSharp_Format.text "; ")
in (let _65_24393 = (Support.List.map for1 fields)
in (FSharp_Format.combine _65_24394 _65_24393)))
in (FSharp_Format.cbrackets _65_24395)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_24397 = (let _65_24396 = (as_standard_constructor ctor)
in (Support.Option.get _65_24396))
in (Support.Prims.snd _65_24397))
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
(let _65_24399 = (let _65_24398 = (as_standard_constructor ctor)
in (Support.Option.get _65_24398))
in (Support.Prims.snd _65_24399))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _65_24402 = (let _65_24401 = (let _65_24400 = (FSharp_Format.text "::")
in (_65_24400)::(xs)::[])
in (x)::_65_24401)
in (FSharp_Format.reduce _65_24402))
end
| (_, _) -> begin
(let _65_24408 = (let _65_24407 = (FSharp_Format.text name)
in (let _65_24406 = (let _65_24405 = (let _65_24404 = (let _65_24403 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24403 ps))
in (FSharp_Format.parens _65_24404))
in (_65_24405)::[])
in (_65_24407)::_65_24406))
in (FSharp_Format.reduce1 _65_24408))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _65_24410 = (let _65_24409 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24409 ps))
in (FSharp_Format.parens _65_24410)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _65_24411 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _65_24411 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _59_448 ) -> (match (_59_448) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _65_24417 = (let _65_24416 = (FSharp_Format.text "|")
in (let _65_24415 = (let _65_24414 = (doc_of_pattern currentModule p)
in (_65_24414)::[])
in (_65_24416)::_65_24415))
in (FSharp_Format.reduce1 _65_24417))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _65_24423 = (let _65_24422 = (FSharp_Format.text "|")
in (let _65_24421 = (let _65_24420 = (doc_of_pattern currentModule p)
in (let _65_24419 = (let _65_24418 = (FSharp_Format.text "when")
in (_65_24418)::(c)::[])
in (_65_24420)::_65_24419))
in (_65_24422)::_65_24421))
in (FSharp_Format.reduce1 _65_24423)))
end)
in (let _65_24434 = (let _65_24433 = (let _65_24428 = (let _65_24427 = (let _65_24426 = (FSharp_Format.text "->")
in (let _65_24425 = (let _65_24424 = (FSharp_Format.text "begin")
in (_65_24424)::[])
in (_65_24426)::_65_24425))
in (case)::_65_24427)
in (FSharp_Format.reduce1 _65_24428))
in (let _65_24432 = (let _65_24431 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_24430 = (let _65_24429 = (FSharp_Format.text "end")
in (_65_24429)::[])
in (_65_24431)::_65_24430))
in (_65_24433)::_65_24432))
in (FSharp_Format.combine FSharp_Format.hardline _65_24434)))
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
in (let _65_24445 = (let _65_24444 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _65_24443 = (let _65_24442 = (FSharp_Format.reduce1 ids)
in (let _65_24441 = (let _65_24440 = (FSharp_Format.text "=")
in (_65_24440)::(e)::[])
in (_65_24442)::_65_24441))
in (_65_24444)::_65_24443))
in (FSharp_Format.reduce1 _65_24445)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _65_24449 = (let _65_24448 = (FSharp_Format.text "let")
in (let _65_24447 = (let _65_24446 = (FSharp_Format.text "rec")
in (_65_24446)::[])
in (_65_24448)::_65_24447))
in (FSharp_Format.reduce1 _65_24449))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _65_24453 = (let _65_24452 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_65_24452)::(doc)::[])
in (FSharp_Format.reduce1 _65_24453))) lets)
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
in (let _65_24462 = (let _65_24461 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24461 doc))
in (FSharp_Format.parens _65_24462)))
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
in (let _65_24469 = (let _65_24468 = (let _65_24467 = (FSharp_Format.text ":")
in (_65_24467)::(ty)::[])
in (name)::_65_24468)
in (FSharp_Format.reduce1 _65_24469))))
end))
in (let _65_24472 = (let _65_24471 = (FSharp_Format.text "; ")
in (let _65_24470 = (Support.List.map forfield fields)
in (FSharp_Format.combine _65_24471 _65_24470)))
in (FSharp_Format.cbrackets _65_24472)))
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
in (let tys = (let _65_24475 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_24475 tys))
in (let _65_24479 = (let _65_24478 = (FSharp_Format.text name)
in (let _65_24477 = (let _65_24476 = (FSharp_Format.text "of")
in (_65_24476)::(tys)::[])
in (_65_24478)::_65_24477))
in (FSharp_Format.reduce1 _65_24479))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _65_24482 = (let _65_24481 = (FSharp_Format.text "|")
in (_65_24481)::(d)::[])
in (FSharp_Format.reduce1 _65_24482))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _65_24486 = (let _65_24485 = (let _65_24484 = (let _65_24483 = (ptsym currentModule ([], x))
in (FSharp_Format.text _65_24483))
in (_65_24484)::[])
in (tparams)::_65_24485)
in (FSharp_Format.reduce1 _65_24486))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _65_24491 = (let _65_24490 = (let _65_24489 = (let _65_24488 = (let _65_24487 = (FSharp_Format.text "=")
in (_65_24487)::[])
in (doc)::_65_24488)
in (FSharp_Format.reduce1 _65_24489))
in (_65_24490)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _65_24491)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _65_24496 = (let _65_24495 = (FSharp_Format.text "type")
in (let _65_24494 = (let _65_24493 = (let _65_24492 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _65_24492 doc))
in (_65_24493)::[])
in (_65_24495)::_65_24494))
in (FSharp_Format.reduce1 _65_24496))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _65_24516 = (let _65_24515 = (let _65_24508 = (let _65_24507 = (FSharp_Format.text "module")
in (let _65_24506 = (let _65_24505 = (FSharp_Format.text x)
in (let _65_24504 = (let _65_24503 = (FSharp_Format.text "=")
in (_65_24503)::[])
in (_65_24505)::_65_24504))
in (_65_24507)::_65_24506))
in (FSharp_Format.reduce1 _65_24508))
in (let _65_24514 = (let _65_24513 = (doc_of_sig currentModule subsig)
in (let _65_24512 = (let _65_24511 = (let _65_24510 = (let _65_24509 = (FSharp_Format.text "end")
in (_65_24509)::[])
in (FSharp_Format.reduce1 _65_24510))
in (_65_24511)::[])
in (_65_24513)::_65_24512))
in (_65_24515)::_65_24514))
in (FSharp_Format.combine FSharp_Format.hardline _65_24516))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _65_24520 = (let _65_24519 = (FSharp_Format.text "exception")
in (let _65_24518 = (let _65_24517 = (FSharp_Format.text x)
in (_65_24517)::[])
in (_65_24519)::_65_24518))
in (FSharp_Format.reduce1 _65_24520))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _65_24522 = (let _65_24521 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_24521 args))
in (FSharp_Format.parens _65_24522))
in (let _65_24528 = (let _65_24527 = (FSharp_Format.text "exception")
in (let _65_24526 = (let _65_24525 = (FSharp_Format.text x)
in (let _65_24524 = (let _65_24523 = (FSharp_Format.text "of")
in (_65_24523)::(args)::[])
in (_65_24525)::_65_24524))
in (_65_24527)::_65_24526))
in (FSharp_Format.reduce1 _65_24528))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _65_24534 = (let _65_24533 = (FSharp_Format.text "val")
in (let _65_24532 = (let _65_24531 = (FSharp_Format.text x)
in (let _65_24530 = (let _65_24529 = (FSharp_Format.text ": ")
in (_65_24529)::(ty)::[])
in (_65_24531)::_65_24530))
in (_65_24533)::_65_24532))
in (FSharp_Format.reduce1 _65_24534)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _65_24545 = (let _65_24544 = (FSharp_Format.text "exception")
in (let _65_24543 = (let _65_24542 = (FSharp_Format.text x)
in (_65_24542)::[])
in (_65_24544)::_65_24543))
in (FSharp_Format.reduce1 _65_24545))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _65_24547 = (let _65_24546 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_24546 args))
in (FSharp_Format.parens _65_24547))
in (let _65_24553 = (let _65_24552 = (FSharp_Format.text "exception")
in (let _65_24551 = (let _65_24550 = (FSharp_Format.text x)
in (let _65_24549 = (let _65_24548 = (FSharp_Format.text "of")
in (_65_24548)::(args)::[])
in (_65_24550)::_65_24549))
in (_65_24552)::_65_24551))
in (FSharp_Format.reduce1 _65_24553))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _65_24561 = (let _65_24560 = (FSharp_Format.text "let")
in (let _65_24559 = (let _65_24558 = (FSharp_Format.text "_")
in (let _65_24557 = (let _65_24556 = (FSharp_Format.text "=")
in (let _65_24555 = (let _65_24554 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_65_24554)::[])
in (_65_24556)::_65_24555))
in (_65_24558)::_65_24557))
in (_65_24560)::_65_24559))
in (FSharp_Format.reduce1 _65_24561))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _59_582 ) -> (match (_59_582) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _59_589 ) -> (match (_59_589) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _65_24580 = (let _65_24579 = (FSharp_Format.text "module")
in (let _65_24578 = (let _65_24577 = (FSharp_Format.text x)
in (let _65_24576 = (let _65_24575 = (FSharp_Format.text ":")
in (let _65_24574 = (let _65_24573 = (FSharp_Format.text "sig")
in (_65_24573)::[])
in (_65_24575)::_65_24574))
in (_65_24577)::_65_24576))
in (_65_24579)::_65_24578))
in (FSharp_Format.reduce1 _65_24580))
in (let tail = (let _65_24582 = (let _65_24581 = (FSharp_Format.text "end")
in (_65_24581)::[])
in (FSharp_Format.reduce1 _65_24582))
in (let doc = (Support.Option.map (fun ( _59_595 ) -> (match (_59_595) with
| (s, _) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _65_24592 = (let _65_24591 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _65_24590 = (let _65_24589 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _65_24588 = (let _65_24587 = (FSharp_Format.reduce sub)
in (let _65_24586 = (let _65_24585 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_65_24585)::[])
in (_65_24587)::_65_24586))
in (_65_24589)::_65_24588))
in (_65_24591)::_65_24590))
in (FSharp_Format.reduce _65_24592)))))))
end))
and for1_mod = (fun ( istop ) ( _59_608 ) -> (match (_59_608) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _59_609 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _65_24602 = (match ((not (istop))) with
| true -> begin
(let _65_24601 = (FSharp_Format.text "module")
in (let _65_24600 = (let _65_24599 = (FSharp_Format.text x)
in (let _65_24598 = (let _65_24597 = (FSharp_Format.text "=")
in (let _65_24596 = (let _65_24595 = (FSharp_Format.text "struct")
in (_65_24595)::[])
in (_65_24597)::_65_24596))
in (_65_24599)::_65_24598))
in (_65_24601)::_65_24600))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _65_24602))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _65_24604 = (let _65_24603 = (FSharp_Format.text "end")
in (_65_24603)::[])
in (FSharp_Format.reduce1 _65_24604))
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
in (let _65_24614 = (let _65_24613 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _65_24612 = (let _65_24611 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _65_24610 = (let _65_24609 = (FSharp_Format.reduce sub)
in (let _65_24608 = (let _65_24607 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_65_24607)::[])
in (_65_24609)::_65_24608))
in (_65_24611)::_65_24610))
in (_65_24613)::_65_24612))
in (FSharp_Format.reduce _65_24614))))))))
end))
in (let docs = (Support.List.map (fun ( _59_627 ) -> (match (_59_627) with
| (x, s, m) -> begin
(let _65_24616 = (for1_mod true (x, s, m))
in (x, _65_24616))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Backends_ML_Util.flatten_mlpath env.Microsoft_FStar_Backends_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Backends_ML_Util.flatten_mlpath env.Microsoft_FStar_Backends_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))





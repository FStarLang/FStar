
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

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "mod"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "!"))::(("exit", "exit"))::(("failwith", "failwith"))::(("raise", "raise"))::[]

let prim_types = (("char", "char"))::(("bool", "bool"))::(("string", "string"))::(("unit", "unit"))::(("ref", "ref"))::(("array", "array"))::(("option", "option"))::(("list", "list"))::(("int", "int"))::(("int64", "Int64.t"))::[]

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ( ns ) -> (ns = ("Support")::("Prims")::[]))

let as_bin_op = (fun ( _67_6 ) -> (match (_67_6) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _67_12 ) -> (match (_67_12) with
| (y, _67_9, _67_11) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun ( p ) -> ((as_bin_op p) <> None))

let as_uni_op = (fun ( _67_16 ) -> (match (_67_16) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _67_20 ) -> (match (_67_20) with
| (y, _67_19) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun ( p ) -> ((as_uni_op p) <> None))

let as_standard_type = (fun ( _67_24 ) -> (match (_67_24) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _67_28 ) -> (match (_67_28) with
| (y, _67_27) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun ( p ) -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun ( _67_32 ) -> (match (_67_32) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _67_36 ) -> (match (_67_36) with
| (y, _67_35) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun ( p ) -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun ( _67_40 ) ( inner ) ( doc ) -> (match (_67_40) with
| (outer, side) -> begin
(let noparens = (fun ( _inner ) ( _outer ) ( side ) -> (let _67_49 = _inner
in (match (_67_49) with
| (pi, fi) -> begin
(let _67_52 = _outer
in (match (_67_52) with
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
| (_67_76, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_67_80, _67_82) -> begin
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
| _67_100 -> begin
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
(let _70_26003 = (let _70_26002 = (encode_char c)
in (Support.String.strcat "\'" _70_26002))
in (Support.String.strcat _70_26003 "\'"))
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
in (let doc = (let _70_26010 = (let _70_26009 = (let _70_26008 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_26008 doc))
in (FSharp_Format.hbox _70_26009))
in (FSharp_Format.parens _70_26010))
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
| _67_139 -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let _70_26013 = (let _70_26012 = (let _70_26011 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_26011 args))
in (FSharp_Format.hbox _70_26012))
in (FSharp_Format.parens _70_26013)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _70_26015 = (let _70_26014 = (as_standard_type name)
in (Support.Option.get _70_26014))
in (Support.Prims.snd _70_26015))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptsym name)
end)
in (let _70_26019 = (let _70_26018 = (let _70_26017 = (let _70_26016 = (FSharp_Format.text name)
in (_70_26016)::[])
in (args)::_70_26017)
in (FSharp_Format.reduce1 _70_26018))
in (FSharp_Format.hbox _70_26019))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _67_145, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _70_26024 = (let _70_26023 = (let _70_26022 = (let _70_26021 = (let _70_26020 = (FSharp_Format.text " -> ")
in (_70_26020)::(d2)::[])
in (d1)::_70_26021)
in (FSharp_Format.reduce1 _70_26022))
in (FSharp_Format.hbox _70_26023))
in (maybe_paren outer t_prio_fun _70_26024))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _70_26029 = (let _70_26028 = (let _70_26027 = (let _70_26026 = (let _70_26025 = (FSharp_Format.text " ")
in (_70_26025)::(d1)::[])
in (d2)::_70_26026)
in (FSharp_Format.reduce1 _70_26027))
in (FSharp_Format.hbox _70_26028))
in (maybe_paren outer t_prio_fun _70_26029))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))

let rec doc_of_expr = (fun ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_26039 = (let _70_26038 = (let _70_26037 = (FSharp_Format.text "Obj.magic ")
in (_70_26037)::(doc)::[])
in (FSharp_Format.reduce _70_26038))
in (FSharp_Format.parens _70_26039)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _70_26043 = (let _70_26042 = (let _70_26041 = (FSharp_Format.text ";")
in (_70_26041)::(FSharp_Format.hardline)::[])
in (d)::_70_26042)
in (FSharp_Format.reduce _70_26043))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _70_26044 = (string_of_mlconstant c)
in (FSharp_Format.text _70_26044))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _67_175)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _70_26045 = (Microsoft_FStar_Backends_ML_Syntax.ptsym path)
in (FSharp_Format.text _70_26045))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _67_187 ) -> (match (_67_187) with
| (name, e) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_26052 = (let _70_26051 = (let _70_26048 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _70_26048))
in (let _70_26050 = (let _70_26049 = (FSharp_Format.text "=")
in (_70_26049)::(doc)::[])
in (_70_26051)::_70_26050))
in (FSharp_Format.reduce1 _70_26052)))
end))
in (let _70_26055 = (let _70_26054 = (FSharp_Format.text "; ")
in (let _70_26053 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_26054 _70_26053)))
in (FSharp_Format.cbrackets _70_26055)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_26057 = (let _70_26056 = (as_standard_constructor ctor)
in (Support.Option.get _70_26056))
in (Support.Prims.snd _70_26057))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_26059 = (let _70_26058 = (as_standard_constructor ctor)
in (Support.Option.get _70_26058))
in (Support.Prims.snd _70_26059))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _70_26063 = (let _70_26062 = (FSharp_Format.parens x)
in (let _70_26061 = (let _70_26060 = (FSharp_Format.text "::")
in (_70_26060)::(xs)::[])
in (_70_26062)::_70_26061))
in (FSharp_Format.reduce _70_26063))
end
| (_67_206, _67_208) -> begin
(let _70_26069 = (let _70_26068 = (FSharp_Format.text name)
in (let _70_26067 = (let _70_26066 = (let _70_26065 = (let _70_26064 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_26064 args))
in (FSharp_Format.parens _70_26065))
in (_70_26066)::[])
in (_70_26068)::_70_26067))
in (FSharp_Format.reduce1 _70_26069))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (let _70_26071 = (let _70_26070 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_26070 docs))
in (FSharp_Format.parens _70_26071))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets (rec_, lets))
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let _70_26077 = (let _70_26076 = (let _70_26075 = (let _70_26074 = (let _70_26073 = (let _70_26072 = (FSharp_Format.text "in")
in (_70_26072)::(body)::[])
in (FSharp_Format.reduce1 _70_26073))
in (_70_26074)::[])
in (doc)::_70_26075)
in (FSharp_Format.combine FSharp_Format.hardline _70_26076))
in (FSharp_Format.parens _70_26077))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(let _67_237 = (let _70_26078 = (as_bin_op p)
in (Support.Option.get _70_26078))
in (match (_67_237) with
| (_67_234, prio, txt) -> begin
(let e1 = (doc_of_expr (prio, Left) e1)
in (let e2 = (doc_of_expr (prio, Right) e2)
in (let doc = (let _70_26081 = (let _70_26080 = (let _70_26079 = (FSharp_Format.text txt)
in (_70_26079)::(e2)::[])
in (e1)::_70_26080)
in (FSharp_Format.reduce1 _70_26081))
in (FSharp_Format.parens doc))))
end))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(let _67_249 = (let _70_26082 = (as_uni_op p)
in (Support.Option.get _70_26082))
in (match (_67_249) with
| (_67_247, txt) -> begin
(let e1 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let doc = (let _70_26086 = (let _70_26085 = (FSharp_Format.text txt)
in (let _70_26084 = (let _70_26083 = (FSharp_Format.parens e1)
in (_70_26083)::[])
in (_70_26085)::_70_26084))
in (FSharp_Format.reduce1 _70_26086))
in (FSharp_Format.parens doc)))
end))
end
| _67_253 -> begin
(let e = (doc_of_expr (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr (e_app_prio, IRight)) args)
in (let _70_26087 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _70_26087))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let doc = (let _70_26093 = (let _70_26092 = (let _70_26091 = (FSharp_Format.text ".")
in (let _70_26090 = (let _70_26089 = (let _70_26088 = (Microsoft_FStar_Backends_ML_Syntax.ptsym f)
in (FSharp_Format.text _70_26088))
in (_70_26089)::[])
in (_70_26091)::_70_26090))
in (e)::_70_26092)
in (FSharp_Format.reduce _70_26093))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _67_271 ) -> (match (_67_271) with
| ((x, _67_268), xt) -> begin
(let _70_26106 = (let _70_26105 = (FSharp_Format.text "(")
in (let _70_26104 = (let _70_26103 = (FSharp_Format.text x)
in (let _70_26102 = (let _70_26101 = (match (xt) with
| Some (xxt) -> begin
(let _70_26098 = (let _70_26097 = (FSharp_Format.text " : ")
in (let _70_26096 = (let _70_26095 = (doc_of_mltype outer xxt)
in (_70_26095)::[])
in (_70_26097)::_70_26096))
in (FSharp_Format.reduce1 _70_26098))
end
| _67_275 -> begin
(FSharp_Format.text "")
end)
in (let _70_26100 = (let _70_26099 = (FSharp_Format.text ")")
in (_70_26099)::[])
in (_70_26101)::_70_26100))
in (_70_26103)::_70_26102))
in (_70_26105)::_70_26104))
in (FSharp_Format.reduce1 _70_26106))
end)) ids)
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let doc = (let _70_26112 = (let _70_26111 = (FSharp_Format.text "fun")
in (let _70_26110 = (let _70_26109 = (FSharp_Format.reduce1 ids)
in (let _70_26108 = (let _70_26107 = (FSharp_Format.text "->")
in (_70_26107)::(body)::[])
in (_70_26109)::_70_26108))
in (_70_26111)::_70_26110))
in (FSharp_Format.reduce1 _70_26112))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_26125 = (let _70_26124 = (let _70_26119 = (let _70_26118 = (FSharp_Format.text "if")
in (let _70_26117 = (let _70_26116 = (let _70_26115 = (FSharp_Format.text "then")
in (let _70_26114 = (let _70_26113 = (FSharp_Format.text "begin")
in (_70_26113)::[])
in (_70_26115)::_70_26114))
in (cond)::_70_26116)
in (_70_26118)::_70_26117))
in (FSharp_Format.reduce1 _70_26119))
in (let _70_26123 = (let _70_26122 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _70_26121 = (let _70_26120 = (FSharp_Format.text "end")
in (_70_26120)::[])
in (_70_26122)::_70_26121))
in (_70_26124)::_70_26123))
in (FSharp_Format.combine FSharp_Format.hardline _70_26125))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_26148 = (let _70_26147 = (let _70_26132 = (let _70_26131 = (FSharp_Format.text "if")
in (let _70_26130 = (let _70_26129 = (let _70_26128 = (FSharp_Format.text "then")
in (let _70_26127 = (let _70_26126 = (FSharp_Format.text "begin")
in (_70_26126)::[])
in (_70_26128)::_70_26127))
in (cond)::_70_26129)
in (_70_26131)::_70_26130))
in (FSharp_Format.reduce1 _70_26132))
in (let _70_26146 = (let _70_26145 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _70_26144 = (let _70_26143 = (let _70_26138 = (let _70_26137 = (FSharp_Format.text "end")
in (let _70_26136 = (let _70_26135 = (FSharp_Format.text "else")
in (let _70_26134 = (let _70_26133 = (FSharp_Format.text "begin")
in (_70_26133)::[])
in (_70_26135)::_70_26134))
in (_70_26137)::_70_26136))
in (FSharp_Format.reduce1 _70_26138))
in (let _70_26142 = (let _70_26141 = (doc_of_expr (min_op_prec, NonAssoc) e2)
in (let _70_26140 = (let _70_26139 = (FSharp_Format.text "end")
in (_70_26139)::[])
in (_70_26141)::_70_26140))
in (_70_26143)::_70_26142))
in (_70_26145)::_70_26144))
in (_70_26147)::_70_26146))
in (FSharp_Format.combine FSharp_Format.hardline _70_26148))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map doc_of_branch pats)
in (let doc = (let _70_26155 = (let _70_26154 = (let _70_26153 = (FSharp_Format.text "match")
in (let _70_26152 = (let _70_26151 = (FSharp_Format.parens cond)
in (let _70_26150 = (let _70_26149 = (FSharp_Format.text "with")
in (_70_26149)::[])
in (_70_26151)::_70_26150))
in (_70_26153)::_70_26152))
in (FSharp_Format.reduce1 _70_26154))
in (_70_26155)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _70_26160 = (let _70_26159 = (FSharp_Format.text "raise")
in (let _70_26158 = (let _70_26157 = (let _70_26156 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _70_26156))
in (_70_26157)::[])
in (_70_26159)::_70_26158))
in (FSharp_Format.reduce1 _70_26160))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let _70_26169 = (let _70_26168 = (FSharp_Format.text "raise")
in (let _70_26167 = (let _70_26166 = (let _70_26161 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _70_26161))
in (let _70_26165 = (let _70_26164 = (let _70_26163 = (let _70_26162 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_26162 args))
in (FSharp_Format.parens _70_26163))
in (_70_26164)::[])
in (_70_26166)::_70_26165))
in (_70_26168)::_70_26167))
in (FSharp_Format.reduce1 _70_26169)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _70_26186 = (let _70_26185 = (let _70_26173 = (let _70_26172 = (FSharp_Format.text "try")
in (let _70_26171 = (let _70_26170 = (FSharp_Format.text "begin")
in (_70_26170)::[])
in (_70_26172)::_70_26171))
in (FSharp_Format.reduce1 _70_26173))
in (let _70_26184 = (let _70_26183 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_26182 = (let _70_26181 = (let _70_26177 = (let _70_26176 = (FSharp_Format.text "end")
in (let _70_26175 = (let _70_26174 = (FSharp_Format.text "with")
in (_70_26174)::[])
in (_70_26176)::_70_26175))
in (FSharp_Format.reduce1 _70_26177))
in (let _70_26180 = (let _70_26179 = (let _70_26178 = (Support.List.map doc_of_branch pats)
in (FSharp_Format.combine FSharp_Format.hardline _70_26178))
in (_70_26179)::[])
in (_70_26181)::_70_26180))
in (_70_26183)::_70_26182))
in (_70_26185)::_70_26184))
in (FSharp_Format.combine FSharp_Format.hardline _70_26186))
end))
and doc_of_pattern = (fun ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _70_26188 = (string_of_mlconstant c)
in (FSharp_Format.text _70_26188))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _67_328 ) -> (match (_67_328) with
| (name, p) -> begin
(let _70_26197 = (let _70_26196 = (let _70_26191 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _70_26191))
in (let _70_26195 = (let _70_26194 = (FSharp_Format.text "=")
in (let _70_26193 = (let _70_26192 = (doc_of_pattern p)
in (_70_26192)::[])
in (_70_26194)::_70_26193))
in (_70_26196)::_70_26195))
in (FSharp_Format.reduce1 _70_26197))
end))
in (let _70_26200 = (let _70_26199 = (FSharp_Format.text "; ")
in (let _70_26198 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_26199 _70_26198)))
in (FSharp_Format.cbrackets _70_26200)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_26202 = (let _70_26201 = (as_standard_constructor ctor)
in (Support.Option.get _70_26201))
in (Support.Prims.snd _70_26202))
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
(let _70_26204 = (let _70_26203 = (as_standard_constructor ctor)
in (Support.Option.get _70_26203))
in (Support.Prims.snd _70_26204))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _70_26207 = (let _70_26206 = (let _70_26205 = (FSharp_Format.text "::")
in (_70_26205)::(xs)::[])
in (x)::_70_26206)
in (FSharp_Format.reduce _70_26207))
end
| (_67_346, _67_348) -> begin
(let _70_26213 = (let _70_26212 = (FSharp_Format.text name)
in (let _70_26211 = (let _70_26210 = (let _70_26209 = (let _70_26208 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_26208 ps))
in (FSharp_Format.parens _70_26209))
in (_70_26210)::[])
in (_70_26212)::_70_26211))
in (FSharp_Format.reduce1 _70_26213))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let _70_26215 = (let _70_26214 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_26214 ps))
in (FSharp_Format.parens _70_26215)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _70_26216 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _70_26216 ps))))
end))
and doc_of_branch = (fun ( _67_361 ) -> (match (_67_361) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _70_26221 = (let _70_26220 = (FSharp_Format.text "|")
in (let _70_26219 = (let _70_26218 = (doc_of_pattern p)
in (_70_26218)::[])
in (_70_26220)::_70_26219))
in (FSharp_Format.reduce1 _70_26221))
end
| Some (c) -> begin
(let c = (doc_of_expr (min_op_prec, NonAssoc) c)
in (let _70_26227 = (let _70_26226 = (FSharp_Format.text "|")
in (let _70_26225 = (let _70_26224 = (doc_of_pattern p)
in (let _70_26223 = (let _70_26222 = (FSharp_Format.text "when")
in (_70_26222)::(c)::[])
in (_70_26224)::_70_26223))
in (_70_26226)::_70_26225))
in (FSharp_Format.reduce1 _70_26227)))
end)
in (let _70_26238 = (let _70_26237 = (let _70_26232 = (let _70_26231 = (let _70_26230 = (FSharp_Format.text "->")
in (let _70_26229 = (let _70_26228 = (FSharp_Format.text "begin")
in (_70_26228)::[])
in (_70_26230)::_70_26229))
in (case)::_70_26231)
in (FSharp_Format.reduce1 _70_26232))
in (let _70_26236 = (let _70_26235 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_26234 = (let _70_26233 = (FSharp_Format.text "end")
in (_70_26233)::[])
in (_70_26235)::_70_26234))
in (_70_26237)::_70_26236))
in (FSharp_Format.combine FSharp_Format.hardline _70_26238)))
end))
and doc_of_lets = (fun ( _67_369 ) -> (match (_67_369) with
| (rec_, lets) -> begin
(let for1 = (fun ( _67_375 ) -> (match (_67_375) with
| (name, tys, ids, e) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let ids = (Support.List.map (fun ( _67_380 ) -> (match (_67_380) with
| (x, _67_379) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _70_26248 = (let _70_26247 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _70_26246 = (let _70_26245 = (FSharp_Format.reduce1 ids)
in (let _70_26244 = (let _70_26243 = (FSharp_Format.text "=")
in (_70_26243)::(e)::[])
in (_70_26245)::_70_26244))
in (_70_26247)::_70_26246))
in (FSharp_Format.reduce1 _70_26248))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _70_26252 = (let _70_26251 = (FSharp_Format.text "let")
in (let _70_26250 = (let _70_26249 = (FSharp_Format.text "rec")
in (_70_26249)::[])
in (_70_26251)::_70_26250))
in (FSharp_Format.reduce1 _70_26252))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _70_26256 = (let _70_26255 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_70_26255)::(doc)::[])
in (FSharp_Format.reduce1 _70_26256))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( decls ) -> (let for1 = (fun ( _67_392 ) -> (match (_67_392) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))
end
| _67_397 -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))) tparams)
in (let _70_26263 = (let _70_26262 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_26262 doc))
in (FSharp_Format.parens _70_26263)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _67_410 ) -> (match (_67_410) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _70_26270 = (let _70_26269 = (let _70_26268 = (FSharp_Format.text ":")
in (_70_26268)::(ty)::[])
in (name)::_70_26269)
in (FSharp_Format.reduce1 _70_26270))))
end))
in (let _70_26273 = (let _70_26272 = (FSharp_Format.text "; ")
in (let _70_26271 = (Support.List.map forfield fields)
in (FSharp_Format.combine _70_26272 _70_26271)))
in (FSharp_Format.cbrackets _70_26273)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _67_418 ) -> (match (_67_418) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _67_421 -> begin
(let tys = (Support.List.map (doc_of_mltype (t_prio_tpl, Left)) tys)
in (let tys = (let _70_26276 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_26276 tys))
in (let _70_26280 = (let _70_26279 = (FSharp_Format.text name)
in (let _70_26278 = (let _70_26277 = (FSharp_Format.text "of")
in (_70_26277)::(tys)::[])
in (_70_26279)::_70_26278))
in (FSharp_Format.reduce1 _70_26280))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _70_26283 = (let _70_26282 = (FSharp_Format.text "|")
in (_70_26282)::(d)::[])
in (FSharp_Format.reduce1 _70_26283))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _70_26287 = (let _70_26286 = (let _70_26285 = (let _70_26284 = (Microsoft_FStar_Backends_ML_Syntax.ptsym ([], x))
in (FSharp_Format.text _70_26284))
in (_70_26285)::[])
in (tparams)::_70_26286)
in (FSharp_Format.reduce1 _70_26287))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _70_26292 = (let _70_26291 = (let _70_26290 = (let _70_26289 = (let _70_26288 = (FSharp_Format.text "=")
in (_70_26288)::[])
in (doc)::_70_26289)
in (FSharp_Format.reduce1 _70_26290))
in (_70_26291)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _70_26292)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _70_26297 = (let _70_26296 = (FSharp_Format.text "type")
in (let _70_26295 = (let _70_26294 = (let _70_26293 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _70_26293 doc))
in (_70_26294)::[])
in (_70_26296)::_70_26295))
in (FSharp_Format.reduce1 _70_26297))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _70_26314 = (let _70_26313 = (let _70_26306 = (let _70_26305 = (FSharp_Format.text "module")
in (let _70_26304 = (let _70_26303 = (FSharp_Format.text x)
in (let _70_26302 = (let _70_26301 = (FSharp_Format.text "=")
in (_70_26301)::[])
in (_70_26303)::_70_26302))
in (_70_26305)::_70_26304))
in (FSharp_Format.reduce1 _70_26306))
in (let _70_26312 = (let _70_26311 = (doc_of_sig subsig)
in (let _70_26310 = (let _70_26309 = (let _70_26308 = (let _70_26307 = (FSharp_Format.text "end")
in (_70_26307)::[])
in (FSharp_Format.reduce1 _70_26308))
in (_70_26309)::[])
in (_70_26311)::_70_26310))
in (_70_26313)::_70_26312))
in (FSharp_Format.combine FSharp_Format.hardline _70_26314))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _70_26318 = (let _70_26317 = (FSharp_Format.text "exception")
in (let _70_26316 = (let _70_26315 = (FSharp_Format.text x)
in (_70_26315)::[])
in (_70_26317)::_70_26316))
in (FSharp_Format.reduce1 _70_26318))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _70_26320 = (let _70_26319 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_26319 args))
in (FSharp_Format.parens _70_26320))
in (let _70_26326 = (let _70_26325 = (FSharp_Format.text "exception")
in (let _70_26324 = (let _70_26323 = (FSharp_Format.text x)
in (let _70_26322 = (let _70_26321 = (FSharp_Format.text "of")
in (_70_26321)::(args)::[])
in (_70_26323)::_70_26322))
in (_70_26325)::_70_26324))
in (FSharp_Format.reduce1 _70_26326))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_67_451, ty))) -> begin
(let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _70_26332 = (let _70_26331 = (FSharp_Format.text "val")
in (let _70_26330 = (let _70_26329 = (FSharp_Format.text x)
in (let _70_26328 = (let _70_26327 = (FSharp_Format.text ": ")
in (_70_26327)::(ty)::[])
in (_70_26329)::_70_26328))
in (_70_26331)::_70_26330))
in (FSharp_Format.reduce1 _70_26332)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl decls)
end))
and doc_of_sig = (fun ( s ) -> (let docs = (Support.List.map doc_of_sig1 s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _70_26340 = (let _70_26339 = (FSharp_Format.text "exception")
in (let _70_26338 = (let _70_26337 = (FSharp_Format.text x)
in (_70_26337)::[])
in (_70_26339)::_70_26338))
in (FSharp_Format.reduce1 _70_26340))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _70_26342 = (let _70_26341 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_26341 args))
in (FSharp_Format.parens _70_26342))
in (let _70_26348 = (let _70_26347 = (FSharp_Format.text "exception")
in (let _70_26346 = (let _70_26345 = (FSharp_Format.text x)
in (let _70_26344 = (let _70_26343 = (FSharp_Format.text "of")
in (_70_26343)::(args)::[])
in (_70_26345)::_70_26344))
in (_70_26347)::_70_26346))
in (FSharp_Format.reduce1 _70_26348))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _70_26356 = (let _70_26355 = (FSharp_Format.text "let")
in (let _70_26354 = (let _70_26353 = (FSharp_Format.text "_")
in (let _70_26352 = (let _70_26351 = (FSharp_Format.text "=")
in (let _70_26350 = (let _70_26349 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (_70_26349)::[])
in (_70_26351)::_70_26350))
in (_70_26353)::_70_26352))
in (_70_26355)::_70_26354))
in (FSharp_Format.reduce1 _70_26356))
end))

let doc_of_mod = (fun ( m ) -> (let docs = (Support.List.map doc_of_mod1 m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _67_487 ) -> (match (_67_487) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _67_494 ) -> (match (_67_494) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _70_26373 = (let _70_26372 = (FSharp_Format.text "module")
in (let _70_26371 = (let _70_26370 = (FSharp_Format.text x)
in (let _70_26369 = (let _70_26368 = (FSharp_Format.text ":")
in (let _70_26367 = (let _70_26366 = (FSharp_Format.text "sig")
in (_70_26366)::[])
in (_70_26368)::_70_26367))
in (_70_26370)::_70_26369))
in (_70_26372)::_70_26371))
in (FSharp_Format.reduce1 _70_26373))
in (let tail = (let _70_26375 = (let _70_26374 = (FSharp_Format.text "end")
in (_70_26374)::[])
in (FSharp_Format.reduce1 _70_26375))
in (let doc = (Support.Option.map (fun ( _67_500 ) -> (match (_67_500) with
| (s, _67_499) -> begin
(doc_of_sig s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _70_26385 = (let _70_26384 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_26383 = (let _70_26382 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_26381 = (let _70_26380 = (FSharp_Format.reduce sub)
in (let _70_26379 = (let _70_26378 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_26378)::[])
in (_70_26380)::_70_26379))
in (_70_26382)::_70_26381))
in (_70_26384)::_70_26383))
in (FSharp_Format.reduce _70_26385)))))))
end))
and for1_mod = (fun ( istop ) ( _67_513 ) -> (match (_67_513) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _67_514 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _70_26395 = (match ((not (istop))) with
| true -> begin
(let _70_26394 = (FSharp_Format.text "module")
in (let _70_26393 = (let _70_26392 = (FSharp_Format.text x)
in (let _70_26391 = (let _70_26390 = (FSharp_Format.text "=")
in (let _70_26389 = (let _70_26388 = (FSharp_Format.text "struct")
in (_70_26388)::[])
in (_70_26390)::_70_26389))
in (_70_26392)::_70_26391))
in (_70_26394)::_70_26393))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _70_26395))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _70_26397 = (let _70_26396 = (FSharp_Format.text "end")
in (_70_26396)::[])
in (FSharp_Format.reduce1 _70_26397))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _67_521 ) -> (match (_67_521) with
| (_67_519, m) -> begin
(doc_of_mod m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _70_26407 = (let _70_26406 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_26405 = (let _70_26404 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_26403 = (let _70_26402 = (FSharp_Format.reduce sub)
in (let _70_26401 = (let _70_26400 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_26400)::[])
in (_70_26402)::_70_26401))
in (_70_26404)::_70_26403))
in (_70_26406)::_70_26405))
in (FSharp_Format.reduce _70_26407))))))))
end))
in (let docs = (Support.List.map (fun ( _67_532 ) -> (match (_67_532) with
| (x, s, m) -> begin
(let _70_26409 = (for1_mod true (x, s, m))
in (x, _70_26409))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))





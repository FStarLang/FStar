
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

let as_bin_op = (fun ( _65_6 ) -> (match (_65_6) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _65_12 ) -> (match (_65_12) with
| (y, _65_9, _65_11) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun ( p ) -> ((as_bin_op p) <> None))

let as_uni_op = (fun ( _65_16 ) -> (match (_65_16) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _65_20 ) -> (match (_65_20) with
| (y, _65_19) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun ( p ) -> ((as_uni_op p) <> None))

let as_standard_type = (fun ( _65_24 ) -> (match (_65_24) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _65_28 ) -> (match (_65_28) with
| (y, _65_27) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun ( p ) -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun ( _65_32 ) -> (match (_65_32) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _65_36 ) -> (match (_65_36) with
| (y, _65_35) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun ( p ) -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun ( _65_40 ) ( inner ) ( doc ) -> (match (_65_40) with
| (outer, side) -> begin
(let noparens = (fun ( _inner ) ( _outer ) ( side ) -> (let _65_49 = _inner
in (match (_65_49) with
| (pi, fi) -> begin
(let _65_52 = _outer
in (match (_65_52) with
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
| (_65_76, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_65_80, _65_82) -> begin
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
| _65_100 -> begin
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
(let _68_25883 = (let _68_25882 = (encode_char c)
in (Support.String.strcat "\'" _68_25882))
in (Support.String.strcat _68_25883 "\'"))
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
in (let doc = (let _68_25890 = (let _68_25889 = (let _68_25888 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_25888 doc))
in (FSharp_Format.hbox _68_25889))
in (FSharp_Format.parens _68_25890))
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
| _65_139 -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let _68_25893 = (let _68_25892 = (let _68_25891 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_25891 args))
in (FSharp_Format.hbox _68_25892))
in (FSharp_Format.parens _68_25893)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _68_25895 = (let _68_25894 = (as_standard_type name)
in (Support.Option.get _68_25894))
in (Support.Prims.snd _68_25895))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptsym name)
end)
in (let _68_25899 = (let _68_25898 = (let _68_25897 = (let _68_25896 = (FSharp_Format.text name)
in (_68_25896)::[])
in (args)::_68_25897)
in (FSharp_Format.reduce1 _68_25898))
in (FSharp_Format.hbox _68_25899))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _65_145, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _68_25904 = (let _68_25903 = (let _68_25902 = (let _68_25901 = (let _68_25900 = (FSharp_Format.text " -> ")
in (_68_25900)::(d2)::[])
in (d1)::_68_25901)
in (FSharp_Format.reduce1 _68_25902))
in (FSharp_Format.hbox _68_25903))
in (maybe_paren outer t_prio_fun _68_25904))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _68_25909 = (let _68_25908 = (let _68_25907 = (let _68_25906 = (let _68_25905 = (FSharp_Format.text " ")
in (_68_25905)::(d1)::[])
in (d2)::_68_25906)
in (FSharp_Format.reduce1 _68_25907))
in (FSharp_Format.hbox _68_25908))
in (maybe_paren outer t_prio_fun _68_25909))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))

let rec doc_of_expr = (fun ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _68_25919 = (let _68_25918 = (let _68_25917 = (FSharp_Format.text "Obj.magic ")
in (_68_25917)::(doc)::[])
in (FSharp_Format.reduce _68_25918))
in (FSharp_Format.parens _68_25919)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _68_25923 = (let _68_25922 = (let _68_25921 = (FSharp_Format.text ";")
in (_68_25921)::(FSharp_Format.hardline)::[])
in (d)::_68_25922)
in (FSharp_Format.reduce _68_25923))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _68_25924 = (string_of_mlconstant c)
in (FSharp_Format.text _68_25924))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _65_175)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _68_25925 = (Microsoft_FStar_Backends_ML_Syntax.ptsym path)
in (FSharp_Format.text _68_25925))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _65_187 ) -> (match (_65_187) with
| (name, e) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _68_25932 = (let _68_25931 = (let _68_25928 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _68_25928))
in (let _68_25930 = (let _68_25929 = (FSharp_Format.text "=")
in (_68_25929)::(doc)::[])
in (_68_25931)::_68_25930))
in (FSharp_Format.reduce1 _68_25932)))
end))
in (let _68_25935 = (let _68_25934 = (FSharp_Format.text "; ")
in (let _68_25933 = (Support.List.map for1 fields)
in (FSharp_Format.combine _68_25934 _68_25933)))
in (FSharp_Format.cbrackets _68_25935)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_25937 = (let _68_25936 = (as_standard_constructor ctor)
in (Support.Option.get _68_25936))
in (Support.Prims.snd _68_25937))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_25939 = (let _68_25938 = (as_standard_constructor ctor)
in (Support.Option.get _68_25938))
in (Support.Prims.snd _68_25939))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _68_25943 = (let _68_25942 = (FSharp_Format.parens x)
in (let _68_25941 = (let _68_25940 = (FSharp_Format.text "::")
in (_68_25940)::(xs)::[])
in (_68_25942)::_68_25941))
in (FSharp_Format.reduce _68_25943))
end
| (_65_206, _65_208) -> begin
(let _68_25949 = (let _68_25948 = (FSharp_Format.text name)
in (let _68_25947 = (let _68_25946 = (let _68_25945 = (let _68_25944 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_25944 args))
in (FSharp_Format.parens _68_25945))
in (_68_25946)::[])
in (_68_25948)::_68_25947))
in (FSharp_Format.reduce1 _68_25949))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (let _68_25951 = (let _68_25950 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_25950 docs))
in (FSharp_Format.parens _68_25951))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets (rec_, lets))
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let _68_25957 = (let _68_25956 = (let _68_25955 = (let _68_25954 = (let _68_25953 = (let _68_25952 = (FSharp_Format.text "in")
in (_68_25952)::(body)::[])
in (FSharp_Format.reduce1 _68_25953))
in (_68_25954)::[])
in (doc)::_68_25955)
in (FSharp_Format.combine FSharp_Format.hardline _68_25956))
in (FSharp_Format.parens _68_25957))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(let _65_237 = (let _68_25958 = (as_bin_op p)
in (Support.Option.get _68_25958))
in (match (_65_237) with
| (_65_234, prio, txt) -> begin
(let e1 = (doc_of_expr (prio, Left) e1)
in (let e2 = (doc_of_expr (prio, Right) e2)
in (let doc = (let _68_25961 = (let _68_25960 = (let _68_25959 = (FSharp_Format.text txt)
in (_68_25959)::(e2)::[])
in (e1)::_68_25960)
in (FSharp_Format.reduce1 _68_25961))
in (FSharp_Format.parens doc))))
end))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(let _65_249 = (let _68_25962 = (as_uni_op p)
in (Support.Option.get _68_25962))
in (match (_65_249) with
| (_65_247, txt) -> begin
(let e1 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let doc = (let _68_25966 = (let _68_25965 = (FSharp_Format.text txt)
in (let _68_25964 = (let _68_25963 = (FSharp_Format.parens e1)
in (_68_25963)::[])
in (_68_25965)::_68_25964))
in (FSharp_Format.reduce1 _68_25966))
in (FSharp_Format.parens doc)))
end))
end
| _65_253 -> begin
(let e = (doc_of_expr (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr (e_app_prio, IRight)) args)
in (let _68_25967 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _68_25967))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let doc = (let _68_25973 = (let _68_25972 = (let _68_25971 = (FSharp_Format.text ".")
in (let _68_25970 = (let _68_25969 = (let _68_25968 = (Microsoft_FStar_Backends_ML_Syntax.ptsym f)
in (FSharp_Format.text _68_25968))
in (_68_25969)::[])
in (_68_25971)::_68_25970))
in (e)::_68_25972)
in (FSharp_Format.reduce _68_25973))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _65_271 ) -> (match (_65_271) with
| ((x, _65_268), xt) -> begin
(let _68_25986 = (let _68_25985 = (FSharp_Format.text "(")
in (let _68_25984 = (let _68_25983 = (FSharp_Format.text x)
in (let _68_25982 = (let _68_25981 = (match (xt) with
| Some (xxt) -> begin
(let _68_25978 = (let _68_25977 = (FSharp_Format.text " : ")
in (let _68_25976 = (let _68_25975 = (doc_of_mltype outer xxt)
in (_68_25975)::[])
in (_68_25977)::_68_25976))
in (FSharp_Format.reduce1 _68_25978))
end
| _65_275 -> begin
(FSharp_Format.text "")
end)
in (let _68_25980 = (let _68_25979 = (FSharp_Format.text ")")
in (_68_25979)::[])
in (_68_25981)::_68_25980))
in (_68_25983)::_68_25982))
in (_68_25985)::_68_25984))
in (FSharp_Format.reduce1 _68_25986))
end)) ids)
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let doc = (let _68_25992 = (let _68_25991 = (FSharp_Format.text "fun")
in (let _68_25990 = (let _68_25989 = (FSharp_Format.reduce1 ids)
in (let _68_25988 = (let _68_25987 = (FSharp_Format.text "->")
in (_68_25987)::(body)::[])
in (_68_25989)::_68_25988))
in (_68_25991)::_68_25990))
in (FSharp_Format.reduce1 _68_25992))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _68_26005 = (let _68_26004 = (let _68_25999 = (let _68_25998 = (FSharp_Format.text "if")
in (let _68_25997 = (let _68_25996 = (let _68_25995 = (FSharp_Format.text "then")
in (let _68_25994 = (let _68_25993 = (FSharp_Format.text "begin")
in (_68_25993)::[])
in (_68_25995)::_68_25994))
in (cond)::_68_25996)
in (_68_25998)::_68_25997))
in (FSharp_Format.reduce1 _68_25999))
in (let _68_26003 = (let _68_26002 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _68_26001 = (let _68_26000 = (FSharp_Format.text "end")
in (_68_26000)::[])
in (_68_26002)::_68_26001))
in (_68_26004)::_68_26003))
in (FSharp_Format.combine FSharp_Format.hardline _68_26005))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _68_26028 = (let _68_26027 = (let _68_26012 = (let _68_26011 = (FSharp_Format.text "if")
in (let _68_26010 = (let _68_26009 = (let _68_26008 = (FSharp_Format.text "then")
in (let _68_26007 = (let _68_26006 = (FSharp_Format.text "begin")
in (_68_26006)::[])
in (_68_26008)::_68_26007))
in (cond)::_68_26009)
in (_68_26011)::_68_26010))
in (FSharp_Format.reduce1 _68_26012))
in (let _68_26026 = (let _68_26025 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _68_26024 = (let _68_26023 = (let _68_26018 = (let _68_26017 = (FSharp_Format.text "end")
in (let _68_26016 = (let _68_26015 = (FSharp_Format.text "else")
in (let _68_26014 = (let _68_26013 = (FSharp_Format.text "begin")
in (_68_26013)::[])
in (_68_26015)::_68_26014))
in (_68_26017)::_68_26016))
in (FSharp_Format.reduce1 _68_26018))
in (let _68_26022 = (let _68_26021 = (doc_of_expr (min_op_prec, NonAssoc) e2)
in (let _68_26020 = (let _68_26019 = (FSharp_Format.text "end")
in (_68_26019)::[])
in (_68_26021)::_68_26020))
in (_68_26023)::_68_26022))
in (_68_26025)::_68_26024))
in (_68_26027)::_68_26026))
in (FSharp_Format.combine FSharp_Format.hardline _68_26028))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map doc_of_branch pats)
in (let doc = (let _68_26035 = (let _68_26034 = (let _68_26033 = (FSharp_Format.text "match")
in (let _68_26032 = (let _68_26031 = (FSharp_Format.parens cond)
in (let _68_26030 = (let _68_26029 = (FSharp_Format.text "with")
in (_68_26029)::[])
in (_68_26031)::_68_26030))
in (_68_26033)::_68_26032))
in (FSharp_Format.reduce1 _68_26034))
in (_68_26035)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _68_26040 = (let _68_26039 = (FSharp_Format.text "raise")
in (let _68_26038 = (let _68_26037 = (let _68_26036 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _68_26036))
in (_68_26037)::[])
in (_68_26039)::_68_26038))
in (FSharp_Format.reduce1 _68_26040))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let _68_26049 = (let _68_26048 = (FSharp_Format.text "raise")
in (let _68_26047 = (let _68_26046 = (let _68_26041 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _68_26041))
in (let _68_26045 = (let _68_26044 = (let _68_26043 = (let _68_26042 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_26042 args))
in (FSharp_Format.parens _68_26043))
in (_68_26044)::[])
in (_68_26046)::_68_26045))
in (_68_26048)::_68_26047))
in (FSharp_Format.reduce1 _68_26049)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _68_26066 = (let _68_26065 = (let _68_26053 = (let _68_26052 = (FSharp_Format.text "try")
in (let _68_26051 = (let _68_26050 = (FSharp_Format.text "begin")
in (_68_26050)::[])
in (_68_26052)::_68_26051))
in (FSharp_Format.reduce1 _68_26053))
in (let _68_26064 = (let _68_26063 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _68_26062 = (let _68_26061 = (let _68_26057 = (let _68_26056 = (FSharp_Format.text "end")
in (let _68_26055 = (let _68_26054 = (FSharp_Format.text "with")
in (_68_26054)::[])
in (_68_26056)::_68_26055))
in (FSharp_Format.reduce1 _68_26057))
in (let _68_26060 = (let _68_26059 = (let _68_26058 = (Support.List.map doc_of_branch pats)
in (FSharp_Format.combine FSharp_Format.hardline _68_26058))
in (_68_26059)::[])
in (_68_26061)::_68_26060))
in (_68_26063)::_68_26062))
in (_68_26065)::_68_26064))
in (FSharp_Format.combine FSharp_Format.hardline _68_26066))
end))
and doc_of_pattern = (fun ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _68_26068 = (string_of_mlconstant c)
in (FSharp_Format.text _68_26068))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _65_328 ) -> (match (_65_328) with
| (name, p) -> begin
(let _68_26077 = (let _68_26076 = (let _68_26071 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _68_26071))
in (let _68_26075 = (let _68_26074 = (FSharp_Format.text "=")
in (let _68_26073 = (let _68_26072 = (doc_of_pattern p)
in (_68_26072)::[])
in (_68_26074)::_68_26073))
in (_68_26076)::_68_26075))
in (FSharp_Format.reduce1 _68_26077))
end))
in (let _68_26080 = (let _68_26079 = (FSharp_Format.text "; ")
in (let _68_26078 = (Support.List.map for1 fields)
in (FSharp_Format.combine _68_26079 _68_26078)))
in (FSharp_Format.cbrackets _68_26080)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_26082 = (let _68_26081 = (as_standard_constructor ctor)
in (Support.Option.get _68_26081))
in (Support.Prims.snd _68_26082))
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
(let _68_26084 = (let _68_26083 = (as_standard_constructor ctor)
in (Support.Option.get _68_26083))
in (Support.Prims.snd _68_26084))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _68_26087 = (let _68_26086 = (let _68_26085 = (FSharp_Format.text "::")
in (_68_26085)::(xs)::[])
in (x)::_68_26086)
in (FSharp_Format.reduce _68_26087))
end
| (_65_346, _65_348) -> begin
(let _68_26093 = (let _68_26092 = (FSharp_Format.text name)
in (let _68_26091 = (let _68_26090 = (let _68_26089 = (let _68_26088 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_26088 ps))
in (FSharp_Format.parens _68_26089))
in (_68_26090)::[])
in (_68_26092)::_68_26091))
in (FSharp_Format.reduce1 _68_26093))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let _68_26095 = (let _68_26094 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_26094 ps))
in (FSharp_Format.parens _68_26095)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _68_26096 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _68_26096 ps))))
end))
and doc_of_branch = (fun ( _65_361 ) -> (match (_65_361) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _68_26101 = (let _68_26100 = (FSharp_Format.text "|")
in (let _68_26099 = (let _68_26098 = (doc_of_pattern p)
in (_68_26098)::[])
in (_68_26100)::_68_26099))
in (FSharp_Format.reduce1 _68_26101))
end
| Some (c) -> begin
(let c = (doc_of_expr (min_op_prec, NonAssoc) c)
in (let _68_26107 = (let _68_26106 = (FSharp_Format.text "|")
in (let _68_26105 = (let _68_26104 = (doc_of_pattern p)
in (let _68_26103 = (let _68_26102 = (FSharp_Format.text "when")
in (_68_26102)::(c)::[])
in (_68_26104)::_68_26103))
in (_68_26106)::_68_26105))
in (FSharp_Format.reduce1 _68_26107)))
end)
in (let _68_26118 = (let _68_26117 = (let _68_26112 = (let _68_26111 = (let _68_26110 = (FSharp_Format.text "->")
in (let _68_26109 = (let _68_26108 = (FSharp_Format.text "begin")
in (_68_26108)::[])
in (_68_26110)::_68_26109))
in (case)::_68_26111)
in (FSharp_Format.reduce1 _68_26112))
in (let _68_26116 = (let _68_26115 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _68_26114 = (let _68_26113 = (FSharp_Format.text "end")
in (_68_26113)::[])
in (_68_26115)::_68_26114))
in (_68_26117)::_68_26116))
in (FSharp_Format.combine FSharp_Format.hardline _68_26118)))
end))
and doc_of_lets = (fun ( _65_369 ) -> (match (_65_369) with
| (rec_, lets) -> begin
(let for1 = (fun ( _65_375 ) -> (match (_65_375) with
| (name, tys, ids, e) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let ids = (Support.List.map (fun ( _65_380 ) -> (match (_65_380) with
| (x, _65_379) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _68_26128 = (let _68_26127 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _68_26126 = (let _68_26125 = (FSharp_Format.reduce1 ids)
in (let _68_26124 = (let _68_26123 = (FSharp_Format.text "=")
in (_68_26123)::(e)::[])
in (_68_26125)::_68_26124))
in (_68_26127)::_68_26126))
in (FSharp_Format.reduce1 _68_26128))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _68_26132 = (let _68_26131 = (FSharp_Format.text "let")
in (let _68_26130 = (let _68_26129 = (FSharp_Format.text "rec")
in (_68_26129)::[])
in (_68_26131)::_68_26130))
in (FSharp_Format.reduce1 _68_26132))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _68_26136 = (let _68_26135 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_68_26135)::(doc)::[])
in (FSharp_Format.reduce1 _68_26136))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( decls ) -> (let for1 = (fun ( _65_392 ) -> (match (_65_392) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))
end
| _65_397 -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))) tparams)
in (let _68_26143 = (let _68_26142 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_26142 doc))
in (FSharp_Format.parens _68_26143)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _65_410 ) -> (match (_65_410) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _68_26150 = (let _68_26149 = (let _68_26148 = (FSharp_Format.text ":")
in (_68_26148)::(ty)::[])
in (name)::_68_26149)
in (FSharp_Format.reduce1 _68_26150))))
end))
in (let _68_26153 = (let _68_26152 = (FSharp_Format.text "; ")
in (let _68_26151 = (Support.List.map forfield fields)
in (FSharp_Format.combine _68_26152 _68_26151)))
in (FSharp_Format.cbrackets _68_26153)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _65_418 ) -> (match (_65_418) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _65_421 -> begin
(let tys = (Support.List.map (doc_of_mltype (t_prio_tpl, Left)) tys)
in (let tys = (let _68_26156 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_26156 tys))
in (let _68_26160 = (let _68_26159 = (FSharp_Format.text name)
in (let _68_26158 = (let _68_26157 = (FSharp_Format.text "of")
in (_68_26157)::(tys)::[])
in (_68_26159)::_68_26158))
in (FSharp_Format.reduce1 _68_26160))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _68_26163 = (let _68_26162 = (FSharp_Format.text "|")
in (_68_26162)::(d)::[])
in (FSharp_Format.reduce1 _68_26163))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _68_26167 = (let _68_26166 = (let _68_26165 = (let _68_26164 = (Microsoft_FStar_Backends_ML_Syntax.ptsym ([], x))
in (FSharp_Format.text _68_26164))
in (_68_26165)::[])
in (tparams)::_68_26166)
in (FSharp_Format.reduce1 _68_26167))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _68_26172 = (let _68_26171 = (let _68_26170 = (let _68_26169 = (let _68_26168 = (FSharp_Format.text "=")
in (_68_26168)::[])
in (doc)::_68_26169)
in (FSharp_Format.reduce1 _68_26170))
in (_68_26171)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _68_26172)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _68_26177 = (let _68_26176 = (FSharp_Format.text "type")
in (let _68_26175 = (let _68_26174 = (let _68_26173 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _68_26173 doc))
in (_68_26174)::[])
in (_68_26176)::_68_26175))
in (FSharp_Format.reduce1 _68_26177))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _68_26194 = (let _68_26193 = (let _68_26186 = (let _68_26185 = (FSharp_Format.text "module")
in (let _68_26184 = (let _68_26183 = (FSharp_Format.text x)
in (let _68_26182 = (let _68_26181 = (FSharp_Format.text "=")
in (_68_26181)::[])
in (_68_26183)::_68_26182))
in (_68_26185)::_68_26184))
in (FSharp_Format.reduce1 _68_26186))
in (let _68_26192 = (let _68_26191 = (doc_of_sig subsig)
in (let _68_26190 = (let _68_26189 = (let _68_26188 = (let _68_26187 = (FSharp_Format.text "end")
in (_68_26187)::[])
in (FSharp_Format.reduce1 _68_26188))
in (_68_26189)::[])
in (_68_26191)::_68_26190))
in (_68_26193)::_68_26192))
in (FSharp_Format.combine FSharp_Format.hardline _68_26194))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _68_26198 = (let _68_26197 = (FSharp_Format.text "exception")
in (let _68_26196 = (let _68_26195 = (FSharp_Format.text x)
in (_68_26195)::[])
in (_68_26197)::_68_26196))
in (FSharp_Format.reduce1 _68_26198))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _68_26200 = (let _68_26199 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_26199 args))
in (FSharp_Format.parens _68_26200))
in (let _68_26206 = (let _68_26205 = (FSharp_Format.text "exception")
in (let _68_26204 = (let _68_26203 = (FSharp_Format.text x)
in (let _68_26202 = (let _68_26201 = (FSharp_Format.text "of")
in (_68_26201)::(args)::[])
in (_68_26203)::_68_26202))
in (_68_26205)::_68_26204))
in (FSharp_Format.reduce1 _68_26206))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_65_451, ty))) -> begin
(let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _68_26212 = (let _68_26211 = (FSharp_Format.text "val")
in (let _68_26210 = (let _68_26209 = (FSharp_Format.text x)
in (let _68_26208 = (let _68_26207 = (FSharp_Format.text ": ")
in (_68_26207)::(ty)::[])
in (_68_26209)::_68_26208))
in (_68_26211)::_68_26210))
in (FSharp_Format.reduce1 _68_26212)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl decls)
end))
and doc_of_sig = (fun ( s ) -> (let docs = (Support.List.map doc_of_sig1 s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _68_26220 = (let _68_26219 = (FSharp_Format.text "exception")
in (let _68_26218 = (let _68_26217 = (FSharp_Format.text x)
in (_68_26217)::[])
in (_68_26219)::_68_26218))
in (FSharp_Format.reduce1 _68_26220))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _68_26222 = (let _68_26221 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_26221 args))
in (FSharp_Format.parens _68_26222))
in (let _68_26228 = (let _68_26227 = (FSharp_Format.text "exception")
in (let _68_26226 = (let _68_26225 = (FSharp_Format.text x)
in (let _68_26224 = (let _68_26223 = (FSharp_Format.text "of")
in (_68_26223)::(args)::[])
in (_68_26225)::_68_26224))
in (_68_26227)::_68_26226))
in (FSharp_Format.reduce1 _68_26228))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _68_26236 = (let _68_26235 = (FSharp_Format.text "let")
in (let _68_26234 = (let _68_26233 = (FSharp_Format.text "_")
in (let _68_26232 = (let _68_26231 = (FSharp_Format.text "=")
in (let _68_26230 = (let _68_26229 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (_68_26229)::[])
in (_68_26231)::_68_26230))
in (_68_26233)::_68_26232))
in (_68_26235)::_68_26234))
in (FSharp_Format.reduce1 _68_26236))
end))

let doc_of_mod = (fun ( m ) -> (let docs = (Support.List.map doc_of_mod1 m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _65_487 ) -> (match (_65_487) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _65_494 ) -> (match (_65_494) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _68_26253 = (let _68_26252 = (FSharp_Format.text "module")
in (let _68_26251 = (let _68_26250 = (FSharp_Format.text x)
in (let _68_26249 = (let _68_26248 = (FSharp_Format.text ":")
in (let _68_26247 = (let _68_26246 = (FSharp_Format.text "sig")
in (_68_26246)::[])
in (_68_26248)::_68_26247))
in (_68_26250)::_68_26249))
in (_68_26252)::_68_26251))
in (FSharp_Format.reduce1 _68_26253))
in (let tail = (let _68_26255 = (let _68_26254 = (FSharp_Format.text "end")
in (_68_26254)::[])
in (FSharp_Format.reduce1 _68_26255))
in (let doc = (Support.Option.map (fun ( _65_500 ) -> (match (_65_500) with
| (s, _65_499) -> begin
(doc_of_sig s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _68_26265 = (let _68_26264 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _68_26263 = (let _68_26262 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _68_26261 = (let _68_26260 = (FSharp_Format.reduce sub)
in (let _68_26259 = (let _68_26258 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_68_26258)::[])
in (_68_26260)::_68_26259))
in (_68_26262)::_68_26261))
in (_68_26264)::_68_26263))
in (FSharp_Format.reduce _68_26265)))))))
end))
and for1_mod = (fun ( istop ) ( _65_513 ) -> (match (_65_513) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _65_514 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _68_26275 = (match ((not (istop))) with
| true -> begin
(let _68_26274 = (FSharp_Format.text "module")
in (let _68_26273 = (let _68_26272 = (FSharp_Format.text x)
in (let _68_26271 = (let _68_26270 = (FSharp_Format.text "=")
in (let _68_26269 = (let _68_26268 = (FSharp_Format.text "struct")
in (_68_26268)::[])
in (_68_26270)::_68_26269))
in (_68_26272)::_68_26271))
in (_68_26274)::_68_26273))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _68_26275))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _68_26277 = (let _68_26276 = (FSharp_Format.text "end")
in (_68_26276)::[])
in (FSharp_Format.reduce1 _68_26277))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _65_521 ) -> (match (_65_521) with
| (_65_519, m) -> begin
(doc_of_mod m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _68_26287 = (let _68_26286 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _68_26285 = (let _68_26284 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _68_26283 = (let _68_26282 = (FSharp_Format.reduce sub)
in (let _68_26281 = (let _68_26280 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_68_26280)::[])
in (_68_26282)::_68_26281))
in (_68_26284)::_68_26283))
in (_68_26286)::_68_26285))
in (FSharp_Format.reduce _68_26287))))))))
end))
in (let docs = (Support.List.map (fun ( _65_532 ) -> (match (_65_532) with
| (x, s, m) -> begin
(let _68_26289 = (for1_mod true (x, s, m))
in (x, _68_26289))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))





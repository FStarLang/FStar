
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

type fixity =
| Prefix
| Postfix
| Infix of assoc

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

let is_prims_ns = (fun ns -> (ns = ("Support")::("Prims")::[]))

let as_bin_op = (fun _522914 -> (match (_522914) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(Support.List.tryFind (fun _522920 -> (match (_522920) with
| (y, _, _) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

let is_bin_op = (fun p -> ((as_bin_op p) <> None))

let as_uni_op = (fun _522924 -> (match (_522924) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(Support.List.tryFind (fun _522928 -> (match (_522928) with
| (y, _) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

let is_uni_op = (fun p -> ((as_uni_op p) <> None))

let as_standard_type = (fun _522932 -> (match (_522932) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(Support.List.tryFind (fun _522936 -> (match (_522936) with
| (y, _) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

let is_standard_type = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun _522940 -> (match (_522940) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(Support.List.tryFind (fun _522944 -> (match (_522944) with
| (y, _) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

let is_standard_constructor = (fun p -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun _522948 inner doc -> (match (_522948) with
| (outer, side) -> begin
(let noparens = (fun _inner _outer side -> (let _522957 = _inner
in (match (_522957) with
| (pi, fi) -> begin
(let _522960 = _outer
in (match (_522960) with
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
in if (noparens inner outer side) then begin
doc
end else begin
(FSharp_Format.parens doc)
end)
end))

let ocaml_u8_codepoint = (fun i -> if ((Support.Microsoft.FStar.Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Support.String.strcat "\\x" (Support.Microsoft.FStar.Util.hex_string_of_byte i))
end)

let encode_char = (fun c -> if ((Support.Microsoft.FStar.Util.int_of_char c) > 127) then begin
(let bytes = (Support.Microsoft.FStar.Util.string_of_char c)
in (let bytes = (Support.Microsoft.FStar.Util.unicode_of_string bytes)
in (Support.Microsoft.FStar.Bytes.f_encode ocaml_u8_codepoint bytes)))
end else begin
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
end)

let string_of_mlconstant = (fun sctt -> (match (sctt) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Unit -> begin
"()"
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Bool (true) -> begin
"true"
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Bool (false) -> begin
"false"
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Char (c) -> begin
(Support.String.strcat (Support.String.strcat "\'" (encode_char c)) "\'")
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Byte (c) -> begin
(Support.String.strcat (Support.String.strcat "\'" (ocaml_u8_codepoint c)) "\'")
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Int32 (i) -> begin
(Support.Microsoft.FStar.Util.string_of_int32 i)
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Int64 (i) -> begin
(Support.String.strcat (Support.Microsoft.FStar.Util.string_of_int64 i) "L")
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Float (d) -> begin
(Support.Microsoft.FStar.Util.string_of_float d)
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_Bytes (bytes) -> begin
(let bytes = (Support.Microsoft.FStar.Bytes.f_encode ocaml_u8_codepoint bytes)
in (Support.String.strcat (Support.String.strcat "\"" bytes) "\""))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLC_String (chars) -> begin
(let chars = (Support.String.collect encode_char chars)
in (Support.String.strcat (Support.String.strcat "\"" chars) "\""))
end))

let rec doc_of_expr = (fun outer e -> (match (e) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun d -> (FSharp_Format.reduce ((d)::((FSharp_Format.text ";"))::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Const (c) -> begin
(FSharp_Format.text (string_of_mlconstant c))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Var ((x, _)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Name (path) -> begin
(FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.ptsym path))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun _523054 -> (match (_523054) with
| (name, e) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (FSharp_Format.reduce1 (((FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.ptsym (path, name))))::((FSharp_Format.text "="))::(doc)::[])))
end))
in (FSharp_Format.cbrackets (FSharp_Format.combine (FSharp_Format.text "; ") (Support.List.map for1 fields))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = if (is_standard_constructor ctor) then begin
(Support.Prims.snd (Support.Option.get (as_standard_constructor ctor)))
end else begin
(Microsoft_FStar_Backends_OCaml_Syntax.ptctor ctor)
end
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = if (is_standard_constructor ctor) then begin
(Support.Prims.snd (Support.Option.get (as_standard_constructor ctor)))
end else begin
(Microsoft_FStar_Backends_OCaml_Syntax.ptctor ctor)
end
in (let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(FSharp_Format.reduce (((FSharp_Format.parens x))::((FSharp_Format.text "::"))::(xs)::[]))
end
| (_, _) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text name))::((FSharp_Format.parens (FSharp_Format.combine (FSharp_Format.text ", ") args)))::[]))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (FSharp_Format.parens (FSharp_Format.combine (FSharp_Format.text ", ") docs))
in docs))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Let ((rec_, lets, body)) -> begin
(let doc = (doc_of_lets (rec_, lets))
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (FSharp_Format.parens (FSharp_Format.combine FSharp_Format.hardline ((doc)::((FSharp_Format.reduce1 (((FSharp_Format.text "in"))::(body)::[])))::[])))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Backends_OCaml_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(let _523103 = (Support.Option.get (as_bin_op p))
in (match (_523103) with
| (_, prio, txt) -> begin
(let e1 = (doc_of_expr (prio, Left) e1)
in (let e2 = (doc_of_expr (prio, Right) e2)
in (let doc = (FSharp_Format.reduce1 ((e1)::((FSharp_Format.text txt))::(e2)::[]))
in (FSharp_Format.parens doc))))
end))
end
| (Microsoft_FStar_Backends_OCaml_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(let _523115 = (Support.Option.get (as_uni_op p))
in (match (_523115) with
| (_, txt) -> begin
(let e1 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let doc = (FSharp_Format.reduce1 (((FSharp_Format.text txt))::((FSharp_Format.parens e1))::[]))
in (FSharp_Format.parens doc)))
end))
end
| _ -> begin
(let e = (doc_of_expr (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr (e_app_prio, IRight)) args)
in (FSharp_Format.parens (FSharp_Format.reduce1 ((e)::args)))))
end)
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let doc = (FSharp_Format.reduce ((e)::((FSharp_Format.text "."))::((FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.ptsym f)))::[]))
in doc))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun _523135 -> (match (_523135) with
| (x, _) -> begin
(FSharp_Format.text x)
end)) ids)
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let doc = (FSharp_Format.reduce1 (((FSharp_Format.text "fun"))::((FSharp_Format.reduce1 ids))::((FSharp_Format.text "->"))::(body)::[]))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline (((FSharp_Format.reduce1 (((FSharp_Format.text "if"))::(cond)::((FSharp_Format.text "then"))::((FSharp_Format.text "begin"))::[])))::((doc_of_expr (min_op_prec, NonAssoc) e1))::((FSharp_Format.text "end"))::[]))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline (((FSharp_Format.reduce1 (((FSharp_Format.text "if"))::(cond)::((FSharp_Format.text "then"))::((FSharp_Format.text "begin"))::[])))::((doc_of_expr (min_op_prec, NonAssoc) e1))::((FSharp_Format.reduce1 (((FSharp_Format.text "end"))::((FSharp_Format.text "else"))::((FSharp_Format.text "begin"))::[])))::((doc_of_expr (min_op_prec, NonAssoc) e2))::((FSharp_Format.text "end"))::[]))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map doc_of_branch pats)
in (let doc = ((FSharp_Format.reduce1 (((FSharp_Format.text "match"))::((FSharp_Format.parens cond))::((FSharp_Format.text "with"))::[])))::pats
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Raise ((exn, [])) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "raise"))::((FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.ptctor exn)))::[]))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (FSharp_Format.reduce1 (((FSharp_Format.text "raise"))::((FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.ptctor exn)))::((FSharp_Format.parens (FSharp_Format.combine (FSharp_Format.text ", ") args)))::[])))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLE_Try ((e, pats)) -> begin
(FSharp_Format.combine FSharp_Format.hardline (((FSharp_Format.reduce1 (((FSharp_Format.text "try"))::((FSharp_Format.text "begin"))::[])))::((doc_of_expr (min_op_prec, NonAssoc) e))::((FSharp_Format.reduce1 (((FSharp_Format.text "end"))::((FSharp_Format.text "with"))::[])))::((FSharp_Format.combine FSharp_Format.hardline (Support.List.map doc_of_branch pats)))::[]))
end))
and doc_of_pattern = (fun pattern -> (match (pattern) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLP_Const (c) -> begin
(FSharp_Format.text (string_of_mlconstant c))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun _523188 -> (match (_523188) with
| (name, p) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.ptsym (path, name))))::((FSharp_Format.text "="))::((doc_of_pattern p))::[]))
end))
in (FSharp_Format.cbrackets (FSharp_Format.combine (FSharp_Format.text "; ") (Support.List.map for1 fields))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = if (is_standard_constructor ctor) then begin
(Support.Prims.snd (Support.Option.get (as_standard_constructor ctor)))
end else begin
(Microsoft_FStar_Backends_OCaml_Syntax.ptctor ctor)
end
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLP_CTor ((ctor, ps)) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let name = if (is_standard_constructor ctor) then begin
(Support.Prims.snd (Support.Option.get (as_standard_constructor ctor)))
end else begin
(Microsoft_FStar_Backends_OCaml_Syntax.ptctor ctor)
end
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(FSharp_Format.reduce ((x)::((FSharp_Format.text "::"))::(xs)::[]))
end
| (_, _) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text name))::((FSharp_Format.parens (FSharp_Format.combine (FSharp_Format.text ", ") ps)))::[]))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (FSharp_Format.parens (FSharp_Format.combine (FSharp_Format.text ", ") ps)))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (FSharp_Format.combine (FSharp_Format.text " | ") ps)))
end))
and doc_of_branch = (fun _523221 -> (match (_523221) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "|"))::((doc_of_pattern p))::[]))
end
| Some (c) -> begin
(let c = (doc_of_expr (min_op_prec, NonAssoc) c)
in (FSharp_Format.reduce1 (((FSharp_Format.text "|"))::((doc_of_pattern p))::((FSharp_Format.text "when"))::(c)::[])))
end)
in (FSharp_Format.combine FSharp_Format.hardline (((FSharp_Format.reduce1 ((case)::((FSharp_Format.text "->"))::((FSharp_Format.text "begin"))::[])))::((doc_of_expr (min_op_prec, NonAssoc) e))::((FSharp_Format.text "end"))::[])))
end))
and doc_of_lets = (fun _523229 -> (match (_523229) with
| (rec_, lets) -> begin
(let for1 = (fun _523234 -> (match (_523234) with
| (name, ids, e) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let ids = (Support.List.map (fun _523239 -> (match (_523239) with
| (x, _) -> begin
(FSharp_Format.text x)
end)) ids)
in (FSharp_Format.reduce1 (((FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.idsym name)))::((FSharp_Format.reduce1 ids))::((FSharp_Format.text "="))::(e)::[]))))
end))
in (let letdoc = if rec_ then begin
(FSharp_Format.reduce1 (((FSharp_Format.text "let"))::((FSharp_Format.text "rec"))::[]))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun i doc -> (FSharp_Format.reduce1 ((if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end)::(doc)::[]))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let rec doc_of_mltype = (fun outer ty -> (match (ty) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Var (x) -> begin
(FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.idsym x))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype (t_prio_tpl, Left)) tys)
in (let doc = (FSharp_Format.parens (FSharp_Format.hbox (FSharp_Format.combine (FSharp_Format.text " * ") doc)))
in doc))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Named ((args, name)) -> begin
(let args = (match (args) with
| [] -> begin
FSharp_Format.empty
end
| arg::[] -> begin
(doc_of_mltype (t_prio_name, Left) arg)
end
| _ -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (FSharp_Format.parens (FSharp_Format.hbox (FSharp_Format.combine (FSharp_Format.text ", ") args))))
end)
in (let name = if (is_standard_type name) then begin
(Support.Prims.snd (Support.Option.get (as_standard_type name)))
end else begin
(Microsoft_FStar_Backends_OCaml_Syntax.ptsym name)
end
in (FSharp_Format.hbox (FSharp_Format.reduce1 ((args)::((FSharp_Format.text name))::[])))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLTY_Fun ((t1, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (maybe_paren outer t_prio_fun (FSharp_Format.hbox (FSharp_Format.reduce1 ((d1)::((FSharp_Format.text " -> "))::(d2)::[]))))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (maybe_paren outer t_prio_fun (FSharp_Format.hbox (FSharp_Format.reduce1 ((d2)::((FSharp_Format.text " "))::(d1)::[]))))))
end))

let doc_of_mltydecl = (fun decls -> (let for1 = (fun _523283 -> (match (_523283) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.idsym x))
end
| _ -> begin
(let doc = (Support.List.map (fun x -> (FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.idsym x))) tparams)
in (FSharp_Format.parens (FSharp_Format.combine (FSharp_Format.text ", ") doc)))
end)
in (let forbody = (fun body -> (match (body) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _523301 -> (match (_523301) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (FSharp_Format.reduce1 ((name)::((FSharp_Format.text ":"))::(ty)::[]))))
end))
in (FSharp_Format.cbrackets (FSharp_Format.combine (FSharp_Format.text "; ") (Support.List.map forfield fields))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _523309 -> (match (_523309) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _ -> begin
(let tys = (Support.List.map (doc_of_mltype (t_prio_tpl, Left)) tys)
in (let tys = (FSharp_Format.combine (FSharp_Format.text " * ") tys)
in (FSharp_Format.reduce1 (((FSharp_Format.text name))::((FSharp_Format.text "of"))::(tys)::[]))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun d -> (FSharp_Format.reduce1 (((FSharp_Format.text "|"))::(d)::[]))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (FSharp_Format.reduce1 ((tparams)::((FSharp_Format.text (Microsoft_FStar_Backends_OCaml_Syntax.ptsym ([], x))))::[]))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (FSharp_Format.combine FSharp_Format.hardline (((FSharp_Format.reduce1 ((doc)::((FSharp_Format.text "="))::[])))::(body)::[])))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (FSharp_Format.reduce1 (((FSharp_Format.text "type"))::((FSharp_Format.combine (FSharp_Format.text " and ") doc))::[]))
in doc))))

let rec doc_of_sig1 = (fun s -> (match (s) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLS_Mod ((x, subsig)) -> begin
(FSharp_Format.combine FSharp_Format.hardline (((FSharp_Format.reduce1 (((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text "="))::[])))::((doc_of_sig subsig))::((FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[])))::[]))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLS_Exn ((x, [])) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::[]))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (FSharp_Format.parens (FSharp_Format.combine (FSharp_Format.text " * ") args))
in (FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::((FSharp_Format.text "of"))::(args)::[]))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLS_Val ((x, (_, ty))) -> begin
(let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (FSharp_Format.reduce1 (((FSharp_Format.text "val"))::((FSharp_Format.text x))::((FSharp_Format.text ": "))::(ty)::[])))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl decls)
end))
and doc_of_sig = (fun s -> (let docs = (Support.List.map doc_of_sig1 s)
in (let docs = (Support.List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun m -> (match (m) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLM_Exn ((x, [])) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::[]))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (FSharp_Format.parens (FSharp_Format.combine (FSharp_Format.text " * ") args))
in (FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::((FSharp_Format.text "of"))::(args)::[]))))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl decls)
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLM_Let ((rec_, lets)) -> begin
(let lets = (Support.List.map (fun _523374 -> (match (_523374) with
| (x, y, z) -> begin
((x, (- (1))), y, z)
end)) lets)
in (doc_of_lets (rec_, lets)))
end
| Microsoft_FStar_Backends_OCaml_Syntax.MLM_Top (e) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "let"))::((FSharp_Format.text "_"))::((FSharp_Format.text "="))::((doc_of_expr (min_op_prec, NonAssoc) e))::[]))
end))

let doc_of_mod = (fun m -> (let docs = (Support.List.map doc_of_mod1 m)
in (let docs = (Support.List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _523383 -> (match (_523383) with
| Microsoft_FStar_Backends_OCaml_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _523390 -> (match (_523390) with
| (x, sigmod, Microsoft_FStar_Backends_OCaml_Syntax.MLLib (sub)) -> begin
(let head = (FSharp_Format.reduce1 (((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text ":"))::((FSharp_Format.text "sig"))::[]))
in (let tail = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[]))
in (let doc = (Support.Option.map (fun _523396 -> (match (_523396) with
| (s, _) -> begin
(doc_of_sig s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (FSharp_Format.reduce (((FSharp_Format.cat head FSharp_Format.hardline))::((match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end))::((FSharp_Format.reduce sub))::((FSharp_Format.cat tail FSharp_Format.hardline))::[])))))))
end))
and for1_mod = (fun istop _523409 -> (match (_523409) with
| (x, sigmod, Microsoft_FStar_Backends_OCaml_Syntax.MLLib (sub)) -> begin
(let _523410 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (FSharp_Format.reduce1 (if (not (istop)) then begin
((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text "="))::((FSharp_Format.text "struct"))::[]
end else begin
[]
end))
in (let tail = if (not (istop)) then begin
(FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[]))
end else begin
(FSharp_Format.reduce1 [])
end
in (let doc = (Support.Option.map (fun _523417 -> (match (_523417) with
| (_, m) -> begin
(doc_of_mod m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (FSharp_Format.reduce (((FSharp_Format.cat head FSharp_Format.hardline))::((match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end))::((FSharp_Format.reduce sub))::((FSharp_Format.cat tail FSharp_Format.hardline))::[]))))))))
end))
in (let docs = (Support.List.map (fun _523428 -> (match (_523428) with
| (x, s, m) -> begin
(x, (for1_mod true (x, s, m)))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))





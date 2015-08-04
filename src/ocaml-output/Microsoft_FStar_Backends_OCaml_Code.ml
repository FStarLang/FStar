
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
| (y, _, _) -> begin
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
| (y, _) -> begin
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
| (y, _) -> begin
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
| (y, _) -> begin
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
(let _68_25811 = (let _68_25810 = (encode_char c)
in (Support.String.strcat "\'" _68_25810))
in (Support.String.strcat _68_25811 "\'"))
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
in (let doc = (let _68_25818 = (let _68_25817 = (let _68_25816 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_25816 doc))
in (FSharp_Format.hbox _68_25817))
in (FSharp_Format.parens _68_25818))
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
| _ -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let _68_25821 = (let _68_25820 = (let _68_25819 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_25819 args))
in (FSharp_Format.hbox _68_25820))
in (FSharp_Format.parens _68_25821)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _68_25823 = (let _68_25822 = (as_standard_type name)
in (Support.Option.get _68_25822))
in (Support.Prims.snd _68_25823))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptsym name)
end)
in (let _68_25827 = (let _68_25826 = (let _68_25825 = (let _68_25824 = (FSharp_Format.text name)
in (_68_25824)::[])
in (args)::_68_25825)
in (FSharp_Format.reduce1 _68_25826))
in (FSharp_Format.hbox _68_25827))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _68_25832 = (let _68_25831 = (let _68_25830 = (let _68_25829 = (let _68_25828 = (FSharp_Format.text " -> ")
in (_68_25828)::(d2)::[])
in (d1)::_68_25829)
in (FSharp_Format.reduce1 _68_25830))
in (FSharp_Format.hbox _68_25831))
in (maybe_paren outer t_prio_fun _68_25832))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _68_25837 = (let _68_25836 = (let _68_25835 = (let _68_25834 = (let _68_25833 = (FSharp_Format.text " ")
in (_68_25833)::(d1)::[])
in (d2)::_68_25834)
in (FSharp_Format.reduce1 _68_25835))
in (FSharp_Format.hbox _68_25836))
in (maybe_paren outer t_prio_fun _68_25837))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))

let rec doc_of_expr = (fun ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _68_25847 = (let _68_25846 = (let _68_25845 = (FSharp_Format.text "Obj.magic ")
in (_68_25845)::(doc)::[])
in (FSharp_Format.reduce _68_25846))
in (FSharp_Format.parens _68_25847)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _68_25851 = (let _68_25850 = (let _68_25849 = (FSharp_Format.text ";")
in (_68_25849)::(FSharp_Format.hardline)::[])
in (d)::_68_25850)
in (FSharp_Format.reduce _68_25851))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _68_25852 = (string_of_mlconstant c)
in (FSharp_Format.text _68_25852))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _68_25853 = (Microsoft_FStar_Backends_ML_Syntax.ptsym path)
in (FSharp_Format.text _68_25853))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _65_187 ) -> (match (_65_187) with
| (name, e) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _68_25860 = (let _68_25859 = (let _68_25856 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _68_25856))
in (let _68_25858 = (let _68_25857 = (FSharp_Format.text "=")
in (_68_25857)::(doc)::[])
in (_68_25859)::_68_25858))
in (FSharp_Format.reduce1 _68_25860)))
end))
in (let _68_25863 = (let _68_25862 = (FSharp_Format.text "; ")
in (let _68_25861 = (Support.List.map for1 fields)
in (FSharp_Format.combine _68_25862 _68_25861)))
in (FSharp_Format.cbrackets _68_25863)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_25865 = (let _68_25864 = (as_standard_constructor ctor)
in (Support.Option.get _68_25864))
in (Support.Prims.snd _68_25865))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_25867 = (let _68_25866 = (as_standard_constructor ctor)
in (Support.Option.get _68_25866))
in (Support.Prims.snd _68_25867))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _68_25871 = (let _68_25870 = (FSharp_Format.parens x)
in (let _68_25869 = (let _68_25868 = (FSharp_Format.text "::")
in (_68_25868)::(xs)::[])
in (_68_25870)::_68_25869))
in (FSharp_Format.reduce _68_25871))
end
| (_, _) -> begin
(let _68_25877 = (let _68_25876 = (FSharp_Format.text name)
in (let _68_25875 = (let _68_25874 = (let _68_25873 = (let _68_25872 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_25872 args))
in (FSharp_Format.parens _68_25873))
in (_68_25874)::[])
in (_68_25876)::_68_25875))
in (FSharp_Format.reduce1 _68_25877))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (let _68_25879 = (let _68_25878 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_25878 docs))
in (FSharp_Format.parens _68_25879))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets (rec_, lets))
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let _68_25885 = (let _68_25884 = (let _68_25883 = (let _68_25882 = (let _68_25881 = (let _68_25880 = (FSharp_Format.text "in")
in (_68_25880)::(body)::[])
in (FSharp_Format.reduce1 _68_25881))
in (_68_25882)::[])
in (doc)::_68_25883)
in (FSharp_Format.combine FSharp_Format.hardline _68_25884))
in (FSharp_Format.parens _68_25885))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(let _65_237 = (let _68_25886 = (as_bin_op p)
in (Support.Option.get _68_25886))
in (match (_65_237) with
| (_, prio, txt) -> begin
(let e1 = (doc_of_expr (prio, Left) e1)
in (let e2 = (doc_of_expr (prio, Right) e2)
in (let doc = (let _68_25889 = (let _68_25888 = (let _68_25887 = (FSharp_Format.text txt)
in (_68_25887)::(e2)::[])
in (e1)::_68_25888)
in (FSharp_Format.reduce1 _68_25889))
in (FSharp_Format.parens doc))))
end))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(let _65_249 = (let _68_25890 = (as_uni_op p)
in (Support.Option.get _68_25890))
in (match (_65_249) with
| (_, txt) -> begin
(let e1 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let doc = (let _68_25894 = (let _68_25893 = (FSharp_Format.text txt)
in (let _68_25892 = (let _68_25891 = (FSharp_Format.parens e1)
in (_68_25891)::[])
in (_68_25893)::_68_25892))
in (FSharp_Format.reduce1 _68_25894))
in (FSharp_Format.parens doc)))
end))
end
| _ -> begin
(let e = (doc_of_expr (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr (e_app_prio, IRight)) args)
in (let _68_25895 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _68_25895))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let doc = (let _68_25901 = (let _68_25900 = (let _68_25899 = (FSharp_Format.text ".")
in (let _68_25898 = (let _68_25897 = (let _68_25896 = (Microsoft_FStar_Backends_ML_Syntax.ptsym f)
in (FSharp_Format.text _68_25896))
in (_68_25897)::[])
in (_68_25899)::_68_25898))
in (e)::_68_25900)
in (FSharp_Format.reduce _68_25901))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _65_271 ) -> (match (_65_271) with
| ((x, _), xt) -> begin
(let _68_25914 = (let _68_25913 = (FSharp_Format.text "(")
in (let _68_25912 = (let _68_25911 = (FSharp_Format.text x)
in (let _68_25910 = (let _68_25909 = (match (xt) with
| Some (xxt) -> begin
(let _68_25906 = (let _68_25905 = (FSharp_Format.text " : ")
in (let _68_25904 = (let _68_25903 = (doc_of_mltype outer xxt)
in (_68_25903)::[])
in (_68_25905)::_68_25904))
in (FSharp_Format.reduce1 _68_25906))
end
| _ -> begin
(FSharp_Format.text "")
end)
in (let _68_25908 = (let _68_25907 = (FSharp_Format.text ")")
in (_68_25907)::[])
in (_68_25909)::_68_25908))
in (_68_25911)::_68_25910))
in (_68_25913)::_68_25912))
in (FSharp_Format.reduce1 _68_25914))
end)) ids)
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let doc = (let _68_25920 = (let _68_25919 = (FSharp_Format.text "fun")
in (let _68_25918 = (let _68_25917 = (FSharp_Format.reduce1 ids)
in (let _68_25916 = (let _68_25915 = (FSharp_Format.text "->")
in (_68_25915)::(body)::[])
in (_68_25917)::_68_25916))
in (_68_25919)::_68_25918))
in (FSharp_Format.reduce1 _68_25920))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _68_25933 = (let _68_25932 = (let _68_25927 = (let _68_25926 = (FSharp_Format.text "if")
in (let _68_25925 = (let _68_25924 = (let _68_25923 = (FSharp_Format.text "then")
in (let _68_25922 = (let _68_25921 = (FSharp_Format.text "begin")
in (_68_25921)::[])
in (_68_25923)::_68_25922))
in (cond)::_68_25924)
in (_68_25926)::_68_25925))
in (FSharp_Format.reduce1 _68_25927))
in (let _68_25931 = (let _68_25930 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _68_25929 = (let _68_25928 = (FSharp_Format.text "end")
in (_68_25928)::[])
in (_68_25930)::_68_25929))
in (_68_25932)::_68_25931))
in (FSharp_Format.combine FSharp_Format.hardline _68_25933))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _68_25956 = (let _68_25955 = (let _68_25940 = (let _68_25939 = (FSharp_Format.text "if")
in (let _68_25938 = (let _68_25937 = (let _68_25936 = (FSharp_Format.text "then")
in (let _68_25935 = (let _68_25934 = (FSharp_Format.text "begin")
in (_68_25934)::[])
in (_68_25936)::_68_25935))
in (cond)::_68_25937)
in (_68_25939)::_68_25938))
in (FSharp_Format.reduce1 _68_25940))
in (let _68_25954 = (let _68_25953 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _68_25952 = (let _68_25951 = (let _68_25946 = (let _68_25945 = (FSharp_Format.text "end")
in (let _68_25944 = (let _68_25943 = (FSharp_Format.text "else")
in (let _68_25942 = (let _68_25941 = (FSharp_Format.text "begin")
in (_68_25941)::[])
in (_68_25943)::_68_25942))
in (_68_25945)::_68_25944))
in (FSharp_Format.reduce1 _68_25946))
in (let _68_25950 = (let _68_25949 = (doc_of_expr (min_op_prec, NonAssoc) e2)
in (let _68_25948 = (let _68_25947 = (FSharp_Format.text "end")
in (_68_25947)::[])
in (_68_25949)::_68_25948))
in (_68_25951)::_68_25950))
in (_68_25953)::_68_25952))
in (_68_25955)::_68_25954))
in (FSharp_Format.combine FSharp_Format.hardline _68_25956))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map doc_of_branch pats)
in (let doc = (let _68_25963 = (let _68_25962 = (let _68_25961 = (FSharp_Format.text "match")
in (let _68_25960 = (let _68_25959 = (FSharp_Format.parens cond)
in (let _68_25958 = (let _68_25957 = (FSharp_Format.text "with")
in (_68_25957)::[])
in (_68_25959)::_68_25958))
in (_68_25961)::_68_25960))
in (FSharp_Format.reduce1 _68_25962))
in (_68_25963)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _68_25968 = (let _68_25967 = (FSharp_Format.text "raise")
in (let _68_25966 = (let _68_25965 = (let _68_25964 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _68_25964))
in (_68_25965)::[])
in (_68_25967)::_68_25966))
in (FSharp_Format.reduce1 _68_25968))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let _68_25977 = (let _68_25976 = (FSharp_Format.text "raise")
in (let _68_25975 = (let _68_25974 = (let _68_25969 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _68_25969))
in (let _68_25973 = (let _68_25972 = (let _68_25971 = (let _68_25970 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_25970 args))
in (FSharp_Format.parens _68_25971))
in (_68_25972)::[])
in (_68_25974)::_68_25973))
in (_68_25976)::_68_25975))
in (FSharp_Format.reduce1 _68_25977)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _68_25994 = (let _68_25993 = (let _68_25981 = (let _68_25980 = (FSharp_Format.text "try")
in (let _68_25979 = (let _68_25978 = (FSharp_Format.text "begin")
in (_68_25978)::[])
in (_68_25980)::_68_25979))
in (FSharp_Format.reduce1 _68_25981))
in (let _68_25992 = (let _68_25991 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _68_25990 = (let _68_25989 = (let _68_25985 = (let _68_25984 = (FSharp_Format.text "end")
in (let _68_25983 = (let _68_25982 = (FSharp_Format.text "with")
in (_68_25982)::[])
in (_68_25984)::_68_25983))
in (FSharp_Format.reduce1 _68_25985))
in (let _68_25988 = (let _68_25987 = (let _68_25986 = (Support.List.map doc_of_branch pats)
in (FSharp_Format.combine FSharp_Format.hardline _68_25986))
in (_68_25987)::[])
in (_68_25989)::_68_25988))
in (_68_25991)::_68_25990))
in (_68_25993)::_68_25992))
in (FSharp_Format.combine FSharp_Format.hardline _68_25994))
end))
and doc_of_pattern = (fun ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _68_25996 = (string_of_mlconstant c)
in (FSharp_Format.text _68_25996))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _65_328 ) -> (match (_65_328) with
| (name, p) -> begin
(let _68_26005 = (let _68_26004 = (let _68_25999 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _68_25999))
in (let _68_26003 = (let _68_26002 = (FSharp_Format.text "=")
in (let _68_26001 = (let _68_26000 = (doc_of_pattern p)
in (_68_26000)::[])
in (_68_26002)::_68_26001))
in (_68_26004)::_68_26003))
in (FSharp_Format.reduce1 _68_26005))
end))
in (let _68_26008 = (let _68_26007 = (FSharp_Format.text "; ")
in (let _68_26006 = (Support.List.map for1 fields)
in (FSharp_Format.combine _68_26007 _68_26006)))
in (FSharp_Format.cbrackets _68_26008)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_26010 = (let _68_26009 = (as_standard_constructor ctor)
in (Support.Option.get _68_26009))
in (Support.Prims.snd _68_26010))
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
(let _68_26012 = (let _68_26011 = (as_standard_constructor ctor)
in (Support.Option.get _68_26011))
in (Support.Prims.snd _68_26012))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _68_26015 = (let _68_26014 = (let _68_26013 = (FSharp_Format.text "::")
in (_68_26013)::(xs)::[])
in (x)::_68_26014)
in (FSharp_Format.reduce _68_26015))
end
| (_, _) -> begin
(let _68_26021 = (let _68_26020 = (FSharp_Format.text name)
in (let _68_26019 = (let _68_26018 = (let _68_26017 = (let _68_26016 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_26016 ps))
in (FSharp_Format.parens _68_26017))
in (_68_26018)::[])
in (_68_26020)::_68_26019))
in (FSharp_Format.reduce1 _68_26021))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let _68_26023 = (let _68_26022 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_26022 ps))
in (FSharp_Format.parens _68_26023)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _68_26024 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _68_26024 ps))))
end))
and doc_of_branch = (fun ( _65_361 ) -> (match (_65_361) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _68_26029 = (let _68_26028 = (FSharp_Format.text "|")
in (let _68_26027 = (let _68_26026 = (doc_of_pattern p)
in (_68_26026)::[])
in (_68_26028)::_68_26027))
in (FSharp_Format.reduce1 _68_26029))
end
| Some (c) -> begin
(let c = (doc_of_expr (min_op_prec, NonAssoc) c)
in (let _68_26035 = (let _68_26034 = (FSharp_Format.text "|")
in (let _68_26033 = (let _68_26032 = (doc_of_pattern p)
in (let _68_26031 = (let _68_26030 = (FSharp_Format.text "when")
in (_68_26030)::(c)::[])
in (_68_26032)::_68_26031))
in (_68_26034)::_68_26033))
in (FSharp_Format.reduce1 _68_26035)))
end)
in (let _68_26046 = (let _68_26045 = (let _68_26040 = (let _68_26039 = (let _68_26038 = (FSharp_Format.text "->")
in (let _68_26037 = (let _68_26036 = (FSharp_Format.text "begin")
in (_68_26036)::[])
in (_68_26038)::_68_26037))
in (case)::_68_26039)
in (FSharp_Format.reduce1 _68_26040))
in (let _68_26044 = (let _68_26043 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _68_26042 = (let _68_26041 = (FSharp_Format.text "end")
in (_68_26041)::[])
in (_68_26043)::_68_26042))
in (_68_26045)::_68_26044))
in (FSharp_Format.combine FSharp_Format.hardline _68_26046)))
end))
and doc_of_lets = (fun ( _65_369 ) -> (match (_65_369) with
| (rec_, lets) -> begin
(let for1 = (fun ( _65_375 ) -> (match (_65_375) with
| (name, tys, ids, e) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let ids = (Support.List.map (fun ( _65_380 ) -> (match (_65_380) with
| (x, _) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _68_26056 = (let _68_26055 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _68_26054 = (let _68_26053 = (FSharp_Format.reduce1 ids)
in (let _68_26052 = (let _68_26051 = (FSharp_Format.text "=")
in (_68_26051)::(e)::[])
in (_68_26053)::_68_26052))
in (_68_26055)::_68_26054))
in (FSharp_Format.reduce1 _68_26056))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _68_26060 = (let _68_26059 = (FSharp_Format.text "let")
in (let _68_26058 = (let _68_26057 = (FSharp_Format.text "rec")
in (_68_26057)::[])
in (_68_26059)::_68_26058))
in (FSharp_Format.reduce1 _68_26060))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _68_26064 = (let _68_26063 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_68_26063)::(doc)::[])
in (FSharp_Format.reduce1 _68_26064))) lets)
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
| _ -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))) tparams)
in (let _68_26071 = (let _68_26070 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_26070 doc))
in (FSharp_Format.parens _68_26071)))
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
in (let _68_26078 = (let _68_26077 = (let _68_26076 = (FSharp_Format.text ":")
in (_68_26076)::(ty)::[])
in (name)::_68_26077)
in (FSharp_Format.reduce1 _68_26078))))
end))
in (let _68_26081 = (let _68_26080 = (FSharp_Format.text "; ")
in (let _68_26079 = (Support.List.map forfield fields)
in (FSharp_Format.combine _68_26080 _68_26079)))
in (FSharp_Format.cbrackets _68_26081)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _65_418 ) -> (match (_65_418) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _ -> begin
(let tys = (Support.List.map (doc_of_mltype (t_prio_tpl, Left)) tys)
in (let tys = (let _68_26084 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_26084 tys))
in (let _68_26088 = (let _68_26087 = (FSharp_Format.text name)
in (let _68_26086 = (let _68_26085 = (FSharp_Format.text "of")
in (_68_26085)::(tys)::[])
in (_68_26087)::_68_26086))
in (FSharp_Format.reduce1 _68_26088))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _68_26091 = (let _68_26090 = (FSharp_Format.text "|")
in (_68_26090)::(d)::[])
in (FSharp_Format.reduce1 _68_26091))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _68_26095 = (let _68_26094 = (let _68_26093 = (let _68_26092 = (Microsoft_FStar_Backends_ML_Syntax.ptsym ([], x))
in (FSharp_Format.text _68_26092))
in (_68_26093)::[])
in (tparams)::_68_26094)
in (FSharp_Format.reduce1 _68_26095))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _68_26100 = (let _68_26099 = (let _68_26098 = (let _68_26097 = (let _68_26096 = (FSharp_Format.text "=")
in (_68_26096)::[])
in (doc)::_68_26097)
in (FSharp_Format.reduce1 _68_26098))
in (_68_26099)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _68_26100)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _68_26105 = (let _68_26104 = (FSharp_Format.text "type")
in (let _68_26103 = (let _68_26102 = (let _68_26101 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _68_26101 doc))
in (_68_26102)::[])
in (_68_26104)::_68_26103))
in (FSharp_Format.reduce1 _68_26105))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _68_26122 = (let _68_26121 = (let _68_26114 = (let _68_26113 = (FSharp_Format.text "module")
in (let _68_26112 = (let _68_26111 = (FSharp_Format.text x)
in (let _68_26110 = (let _68_26109 = (FSharp_Format.text "=")
in (_68_26109)::[])
in (_68_26111)::_68_26110))
in (_68_26113)::_68_26112))
in (FSharp_Format.reduce1 _68_26114))
in (let _68_26120 = (let _68_26119 = (doc_of_sig subsig)
in (let _68_26118 = (let _68_26117 = (let _68_26116 = (let _68_26115 = (FSharp_Format.text "end")
in (_68_26115)::[])
in (FSharp_Format.reduce1 _68_26116))
in (_68_26117)::[])
in (_68_26119)::_68_26118))
in (_68_26121)::_68_26120))
in (FSharp_Format.combine FSharp_Format.hardline _68_26122))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _68_26126 = (let _68_26125 = (FSharp_Format.text "exception")
in (let _68_26124 = (let _68_26123 = (FSharp_Format.text x)
in (_68_26123)::[])
in (_68_26125)::_68_26124))
in (FSharp_Format.reduce1 _68_26126))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _68_26128 = (let _68_26127 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_26127 args))
in (FSharp_Format.parens _68_26128))
in (let _68_26134 = (let _68_26133 = (FSharp_Format.text "exception")
in (let _68_26132 = (let _68_26131 = (FSharp_Format.text x)
in (let _68_26130 = (let _68_26129 = (FSharp_Format.text "of")
in (_68_26129)::(args)::[])
in (_68_26131)::_68_26130))
in (_68_26133)::_68_26132))
in (FSharp_Format.reduce1 _68_26134))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_, ty))) -> begin
(let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _68_26140 = (let _68_26139 = (FSharp_Format.text "val")
in (let _68_26138 = (let _68_26137 = (FSharp_Format.text x)
in (let _68_26136 = (let _68_26135 = (FSharp_Format.text ": ")
in (_68_26135)::(ty)::[])
in (_68_26137)::_68_26136))
in (_68_26139)::_68_26138))
in (FSharp_Format.reduce1 _68_26140)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl decls)
end))
and doc_of_sig = (fun ( s ) -> (let docs = (Support.List.map doc_of_sig1 s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _68_26148 = (let _68_26147 = (FSharp_Format.text "exception")
in (let _68_26146 = (let _68_26145 = (FSharp_Format.text x)
in (_68_26145)::[])
in (_68_26147)::_68_26146))
in (FSharp_Format.reduce1 _68_26148))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _68_26150 = (let _68_26149 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_26149 args))
in (FSharp_Format.parens _68_26150))
in (let _68_26156 = (let _68_26155 = (FSharp_Format.text "exception")
in (let _68_26154 = (let _68_26153 = (FSharp_Format.text x)
in (let _68_26152 = (let _68_26151 = (FSharp_Format.text "of")
in (_68_26151)::(args)::[])
in (_68_26153)::_68_26152))
in (_68_26155)::_68_26154))
in (FSharp_Format.reduce1 _68_26156))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _68_26164 = (let _68_26163 = (FSharp_Format.text "let")
in (let _68_26162 = (let _68_26161 = (FSharp_Format.text "_")
in (let _68_26160 = (let _68_26159 = (FSharp_Format.text "=")
in (let _68_26158 = (let _68_26157 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (_68_26157)::[])
in (_68_26159)::_68_26158))
in (_68_26161)::_68_26160))
in (_68_26163)::_68_26162))
in (FSharp_Format.reduce1 _68_26164))
end))

let doc_of_mod = (fun ( m ) -> (let docs = (Support.List.map doc_of_mod1 m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _65_487 ) -> (match (_65_487) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _65_494 ) -> (match (_65_494) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _68_26181 = (let _68_26180 = (FSharp_Format.text "module")
in (let _68_26179 = (let _68_26178 = (FSharp_Format.text x)
in (let _68_26177 = (let _68_26176 = (FSharp_Format.text ":")
in (let _68_26175 = (let _68_26174 = (FSharp_Format.text "sig")
in (_68_26174)::[])
in (_68_26176)::_68_26175))
in (_68_26178)::_68_26177))
in (_68_26180)::_68_26179))
in (FSharp_Format.reduce1 _68_26181))
in (let tail = (let _68_26183 = (let _68_26182 = (FSharp_Format.text "end")
in (_68_26182)::[])
in (FSharp_Format.reduce1 _68_26183))
in (let doc = (Support.Option.map (fun ( _65_500 ) -> (match (_65_500) with
| (s, _) -> begin
(doc_of_sig s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _68_26193 = (let _68_26192 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _68_26191 = (let _68_26190 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _68_26189 = (let _68_26188 = (FSharp_Format.reduce sub)
in (let _68_26187 = (let _68_26186 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_68_26186)::[])
in (_68_26188)::_68_26187))
in (_68_26190)::_68_26189))
in (_68_26192)::_68_26191))
in (FSharp_Format.reduce _68_26193)))))))
end))
and for1_mod = (fun ( istop ) ( _65_513 ) -> (match (_65_513) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _65_514 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _68_26203 = (match ((not (istop))) with
| true -> begin
(let _68_26202 = (FSharp_Format.text "module")
in (let _68_26201 = (let _68_26200 = (FSharp_Format.text x)
in (let _68_26199 = (let _68_26198 = (FSharp_Format.text "=")
in (let _68_26197 = (let _68_26196 = (FSharp_Format.text "struct")
in (_68_26196)::[])
in (_68_26198)::_68_26197))
in (_68_26200)::_68_26199))
in (_68_26202)::_68_26201))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _68_26203))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _68_26205 = (let _68_26204 = (FSharp_Format.text "end")
in (_68_26204)::[])
in (FSharp_Format.reduce1 _68_26205))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _65_521 ) -> (match (_65_521) with
| (_, m) -> begin
(doc_of_mod m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _68_26215 = (let _68_26214 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _68_26213 = (let _68_26212 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _68_26211 = (let _68_26210 = (FSharp_Format.reduce sub)
in (let _68_26209 = (let _68_26208 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_68_26208)::[])
in (_68_26210)::_68_26209))
in (_68_26212)::_68_26211))
in (_68_26214)::_68_26213))
in (FSharp_Format.reduce _68_26215))))))))
end))
in (let docs = (Support.List.map (fun ( _65_532 ) -> (match (_65_532) with
| (x, s, m) -> begin
(let _68_26217 = (for1_mod true (x, s, m))
in (x, _68_26217))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))





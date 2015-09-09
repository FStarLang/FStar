
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft -> begin
true
end
| _ -> begin
false
end))

let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight -> begin
true
end
| _ -> begin
false
end))

let is_Left = (fun _discr_ -> (match (_discr_) with
| Left -> begin
true
end
| _ -> begin
false
end))

let is_Right = (fun _discr_ -> (match (_discr_) with
| Right -> begin
true
end
| _ -> begin
false
end))

let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
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

let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix -> begin
true
end
| _ -> begin
false
end))

let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix -> begin
true
end
| _ -> begin
false
end))

let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

let ___Infix____0 = (fun projectee -> (match (projectee) with
| Infix (_60_3) -> begin
_60_3
end))

type opprec =
(Prims.int * fixity)

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

let max_op_prec = (FStar_Util.max_int, Infix (NonAssoc))

let rec in_ns = (fun x -> (match (x) with
| ([], _60_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_60_18, _60_20) -> begin
false
end))

let path_of_ns = (fun currentModule ns -> (let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
| true -> begin
[]
end
| false -> begin
(let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
in (let ns_len = (FStar_List.length ns)
in (let found = (FStar_Util.find_map cg_libs (fun cg_path -> (let cg_len = (FStar_List.length cg_path)
in (match (((FStar_List.length cg_path) < ns_len)) with
| true -> begin
(let _60_31 = (FStar_Util.first_N cg_len ns)
in (match (_60_31) with
| (pfx, sfx) -> begin
(match ((pfx = cg_path)) with
| true -> begin
(let _126_31 = (let _126_30 = (let _126_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_126_29)::[])
in (FStar_List.append pfx _126_30))
in Some (_126_31))
end
| false -> begin
None
end)
end))
end
| false -> begin
None
end))))
in (match (found) with
| None -> begin
(ns')::[]
end
| Some (x) -> begin
x
end))))
end)))

let mlpath_of_mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _60_41 -> begin
(let _60_44 = x
in (match (_60_44) with
| (ns, x) -> begin
(let _126_36 = (path_of_ns currentModule ns)
in (_126_36, x))
end))
end))

let ptsym_of_symbol = (fun s -> (match (((let _126_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _126_39)) <> (FStar_String.get s 0))) with
| true -> begin
(Prims.strcat "l__" s)
end
| false -> begin
s
end))

let ptsym = (fun currentModule mlp -> (match ((FStar_List.isEmpty (Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Prims.snd mlp))
end
| false -> begin
(let _60_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_50) with
| (p, s) -> begin
(let _126_46 = (let _126_45 = (let _126_44 = (ptsym_of_symbol s)
in (_126_44)::[])
in (FStar_List.append p _126_45))
in (FStar_String.concat "." _126_46))
end))
end))

let ptctor = (fun currentModule mlp -> (let _60_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_55) with
| (p, s) -> begin
(let s = (match (((let _126_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _126_51)) <> (FStar_String.get s 0))) with
| true -> begin
(Prims.strcat "U__" s)
end
| false -> begin
s
end)
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

let prim_types = []

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ns -> (ns = ("Prims")::[]))

let as_bin_op = (fun _60_60 -> (match (_60_60) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun _60_66 -> (match (_60_66) with
| (y, _60_63, _60_65) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun p -> ((as_bin_op p) <> None))

let as_uni_op = (fun _60_70 -> (match (_60_70) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun _60_74 -> (match (_60_74) with
| (y, _60_73) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun p -> ((as_uni_op p) <> None))

let as_standard_type = (fun _60_78 -> (match (_60_78) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun _60_82 -> (match (_60_82) with
| (y, _60_81) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun _60_86 -> (match (_60_86) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun _60_90 -> (match (_60_90) with
| (y, _60_89) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun p -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun _60_94 inner doc -> (match (_60_94) with
| (outer, side) -> begin
(let noparens = (fun _inner _outer side -> (let _60_103 = _inner
in (match (_60_103) with
| (pi, fi) -> begin
(let _60_106 = _outer
in (match (_60_106) with
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
| (_60_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_60_134, _60_136) -> begin
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

let ocaml_u8_codepoint = (fun i -> (match (((FStar_Util.int_of_byte i) = 0)) with
| true -> begin
"\\x00"
end
| false -> begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end))

let encode_char = (fun c -> (match (((FStar_Util.int_of_char c) > 127)) with
| true -> begin
(let bytes = (FStar_Util.string_of_char c)
in (let bytes = (FStar_Util.unicode_of_string bytes)
in (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)))
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
| c when (FStar_Util.is_letter_or_digit c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_punctuation c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_symbol c) -> begin
(FStar_Util.string_of_char c)
end
| _60_154 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end))

let string_of_mlconstant = (fun sctt -> (match (sctt) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"()"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (true) -> begin
"true"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (false) -> begin
"false"
end
| FStar_Extraction_ML_Syntax.MLC_Char (c) -> begin
(let _126_92 = (let _126_91 = (encode_char c)
in (Prims.strcat "\'" _126_91))
in (Prims.strcat _126_92 "\'"))
end
| FStar_Extraction_ML_Syntax.MLC_Byte (c) -> begin
(Prims.strcat (Prims.strcat "\'" (ocaml_u8_codepoint c)) "\'")
end
| FStar_Extraction_ML_Syntax.MLC_Int32 (i) -> begin
(FStar_Util.string_of_int32 i)
end
| FStar_Extraction_ML_Syntax.MLC_Int64 (i) -> begin
(Prims.strcat (FStar_Util.string_of_int64 i) "L")
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(let bytes = (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)
in (Prims.strcat (Prims.strcat "\"" bytes) "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let chars = (FStar_String.collect encode_char chars)
in (Prims.strcat (Prims.strcat "\"" chars) "\""))
end))

let rec doc_of_mltype' = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s '_' 'u')
end
| false -> begin
s
end))
in (let _126_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _126_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _126_107 = (let _126_106 = (let _126_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _126_105 doc))
in (FSharp_Format.hbox _126_106))
in (FSharp_Format.parens _126_107))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(let args = (match (args) with
| [] -> begin
FSharp_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _60_196 -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _126_110 = (let _126_109 = (let _126_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_108 args))
in (FSharp_Format.hbox _126_109))
in (FSharp_Format.parens _126_110)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _126_112 = (let _126_111 = (as_standard_type name)
in (FStar_Option.get _126_111))
in (Prims.snd _126_112))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _126_116 = (let _126_115 = (let _126_114 = (let _126_113 = (FSharp_Format.text name)
in (_126_113)::[])
in (args)::_126_114)
in (FSharp_Format.reduce1 _126_115))
in (FSharp_Format.hbox _126_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _60_202, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _126_121 = (let _126_120 = (let _126_119 = (let _126_118 = (let _126_117 = (FSharp_Format.text " -> ")
in (_126_117)::(d2)::[])
in (d1)::_126_118)
in (FSharp_Format.reduce1 _126_119))
in (FSharp_Format.hbox _126_120))
in (maybe_paren outer t_prio_fun _126_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_App (t1, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _126_126 = (let _126_125 = (let _126_124 = (let _126_123 = (let _126_122 = (FSharp_Format.text " ")
in (_126_122)::(d1)::[])
in (d2)::_126_123)
in (FSharp_Format.reduce1 _126_124))
in (FSharp_Format.hbox _126_125))
in (maybe_paren outer t_prio_fun _126_126))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(FSharp_Format.text "obj")
end
| false -> begin
(FSharp_Format.text "Obj.t")
end)
end))
and doc_of_mltype = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun currentModule outer e -> (match (e) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _126_151 = (let _126_150 = (let _126_149 = (FSharp_Format.text "Prims.checked_cast")
in (_126_149)::(doc)::[])
in (FSharp_Format.reduce _126_150))
in (FSharp_Format.parens _126_151))
end
| false -> begin
(let _126_154 = (let _126_153 = (let _126_152 = (FSharp_Format.text "Obj.magic ")
in (_126_152)::(doc)::[])
in (FSharp_Format.reduce _126_153))
in (FSharp_Format.parens _126_154))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _126_158 = (let _126_157 = (let _126_156 = (FSharp_Format.text ";")
in (_126_156)::(FSharp_Format.hardline)::[])
in (d)::_126_157)
in (FSharp_Format.reduce _126_158))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _126_159 = (string_of_mlconstant c)
in (FSharp_Format.text _126_159))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _60_236) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _126_160 = (ptsym currentModule path)
in (FSharp_Format.text _126_160))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _60_248 -> (match (_60_248) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _126_167 = (let _126_166 = (let _126_163 = (ptsym currentModule (path, name))
in (FSharp_Format.text _126_163))
in (let _126_165 = (let _126_164 = (FSharp_Format.text "=")
in (_126_164)::(doc)::[])
in (_126_166)::_126_165))
in (FSharp_Format.reduce1 _126_167)))
end))
in (let _126_170 = (let _126_169 = (FSharp_Format.text "; ")
in (let _126_168 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _126_169 _126_168)))
in (FSharp_Format.cbrackets _126_170)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _126_172 = (let _126_171 = (as_standard_constructor ctor)
in (FStar_Option.get _126_171))
in (Prims.snd _126_172))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _126_174 = (let _126_173 = (as_standard_constructor ctor)
in (FStar_Option.get _126_173))
in (Prims.snd _126_174))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _126_178 = (let _126_177 = (FSharp_Format.parens x)
in (let _126_176 = (let _126_175 = (FSharp_Format.text "::")
in (_126_175)::(xs)::[])
in (_126_177)::_126_176))
in (FSharp_Format.reduce _126_178))
end
| (_60_267, _60_269) -> begin
(let _126_184 = (let _126_183 = (FSharp_Format.text name)
in (let _126_182 = (let _126_181 = (let _126_180 = (let _126_179 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_179 args))
in (FSharp_Format.parens _126_180))
in (_126_181)::[])
in (_126_183)::_126_182))
in (FSharp_Format.reduce1 _126_184))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _126_186 = (let _126_185 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_185 docs))
in (FSharp_Format.parens _126_186))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _126_192 = (let _126_191 = (let _126_190 = (let _126_189 = (let _126_188 = (let _126_187 = (FSharp_Format.text "in")
in (_126_187)::(body)::[])
in (FSharp_Format.reduce1 _126_188))
in (_126_189)::[])
in (doc)::_126_190)
in (FSharp_Format.combine FSharp_Format.hardline _126_191))
in (FSharp_Format.parens _126_192))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (p), unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (p), unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _60_319 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _126_193 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _126_193))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _126_198 = (let _126_197 = (let _126_196 = (FSharp_Format.text ".")
in (let _126_195 = (let _126_194 = (FSharp_Format.text (Prims.snd f))
in (_126_194)::[])
in (_126_196)::_126_195))
in (e)::_126_197)
in (FSharp_Format.reduce _126_198))
end
| false -> begin
(let _126_204 = (let _126_203 = (let _126_202 = (FSharp_Format.text ".")
in (let _126_201 = (let _126_200 = (let _126_199 = (ptsym currentModule f)
in (FSharp_Format.text _126_199))
in (_126_200)::[])
in (_126_202)::_126_201))
in (e)::_126_203)
in (FSharp_Format.reduce _126_204))
end)
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _126_220 = (let _126_219 = (FSharp_Format.text "(")
in (let _126_218 = (let _126_217 = (FSharp_Format.text x)
in (let _126_216 = (let _126_215 = (match (xt) with
| Some (xxt) -> begin
(let _126_212 = (let _126_211 = (FSharp_Format.text " : ")
in (let _126_210 = (let _126_209 = (doc_of_mltype currentModule outer xxt)
in (_126_209)::[])
in (_126_211)::_126_210))
in (FSharp_Format.reduce1 _126_212))
end
| _60_338 -> begin
(FSharp_Format.text "")
end)
in (let _126_214 = (let _126_213 = (FSharp_Format.text ")")
in (_126_213)::[])
in (_126_215)::_126_214))
in (_126_217)::_126_216))
in (_126_219)::_126_218))
in (FSharp_Format.reduce1 _126_220))
end
| false -> begin
(FSharp_Format.text x)
end))
in (let ids = (FStar_List.map (fun _60_344 -> (match (_60_344) with
| ((x, _60_341), xt) -> begin
(bvar_annot x xt)
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _126_227 = (let _126_226 = (FSharp_Format.text "fun")
in (let _126_225 = (let _126_224 = (FSharp_Format.reduce1 ids)
in (let _126_223 = (let _126_222 = (FSharp_Format.text "->")
in (_126_222)::(body)::[])
in (_126_224)::_126_223))
in (_126_226)::_126_225))
in (FSharp_Format.reduce1 _126_227))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _126_240 = (let _126_239 = (let _126_234 = (let _126_233 = (FSharp_Format.text "if")
in (let _126_232 = (let _126_231 = (let _126_230 = (FSharp_Format.text "then")
in (let _126_229 = (let _126_228 = (FSharp_Format.text "begin")
in (_126_228)::[])
in (_126_230)::_126_229))
in (cond)::_126_231)
in (_126_233)::_126_232))
in (FSharp_Format.reduce1 _126_234))
in (let _126_238 = (let _126_237 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _126_236 = (let _126_235 = (FSharp_Format.text "end")
in (_126_235)::[])
in (_126_237)::_126_236))
in (_126_239)::_126_238))
in (FSharp_Format.combine FSharp_Format.hardline _126_240))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _126_263 = (let _126_262 = (let _126_247 = (let _126_246 = (FSharp_Format.text "if")
in (let _126_245 = (let _126_244 = (let _126_243 = (FSharp_Format.text "then")
in (let _126_242 = (let _126_241 = (FSharp_Format.text "begin")
in (_126_241)::[])
in (_126_243)::_126_242))
in (cond)::_126_244)
in (_126_246)::_126_245))
in (FSharp_Format.reduce1 _126_247))
in (let _126_261 = (let _126_260 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _126_259 = (let _126_258 = (let _126_253 = (let _126_252 = (FSharp_Format.text "end")
in (let _126_251 = (let _126_250 = (FSharp_Format.text "else")
in (let _126_249 = (let _126_248 = (FSharp_Format.text "begin")
in (_126_248)::[])
in (_126_250)::_126_249))
in (_126_252)::_126_251))
in (FSharp_Format.reduce1 _126_253))
in (let _126_257 = (let _126_256 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _126_255 = (let _126_254 = (FSharp_Format.text "end")
in (_126_254)::[])
in (_126_256)::_126_255))
in (_126_258)::_126_257))
in (_126_260)::_126_259))
in (_126_262)::_126_261))
in (FSharp_Format.combine FSharp_Format.hardline _126_263))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _126_270 = (let _126_269 = (let _126_268 = (FSharp_Format.text "match")
in (let _126_267 = (let _126_266 = (FSharp_Format.parens cond)
in (let _126_265 = (let _126_264 = (FSharp_Format.text "with")
in (_126_264)::[])
in (_126_266)::_126_265))
in (_126_268)::_126_267))
in (FSharp_Format.reduce1 _126_269))
in (_126_270)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _126_275 = (let _126_274 = (FSharp_Format.text "raise")
in (let _126_273 = (let _126_272 = (let _126_271 = (ptctor currentModule exn)
in (FSharp_Format.text _126_271))
in (_126_272)::[])
in (_126_274)::_126_273))
in (FSharp_Format.reduce1 _126_275))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _126_284 = (let _126_283 = (FSharp_Format.text "raise")
in (let _126_282 = (let _126_281 = (let _126_276 = (ptctor currentModule exn)
in (FSharp_Format.text _126_276))
in (let _126_280 = (let _126_279 = (let _126_278 = (let _126_277 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_277 args))
in (FSharp_Format.parens _126_278))
in (_126_279)::[])
in (_126_281)::_126_280))
in (_126_283)::_126_282))
in (FSharp_Format.reduce1 _126_284)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _126_301 = (let _126_300 = (let _126_288 = (let _126_287 = (FSharp_Format.text "try")
in (let _126_286 = (let _126_285 = (FSharp_Format.text "begin")
in (_126_285)::[])
in (_126_287)::_126_286))
in (FSharp_Format.reduce1 _126_288))
in (let _126_299 = (let _126_298 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _126_297 = (let _126_296 = (let _126_292 = (let _126_291 = (FSharp_Format.text "end")
in (let _126_290 = (let _126_289 = (FSharp_Format.text "with")
in (_126_289)::[])
in (_126_291)::_126_290))
in (FSharp_Format.reduce1 _126_292))
in (let _126_295 = (let _126_294 = (let _126_293 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _126_293))
in (_126_294)::[])
in (_126_296)::_126_295))
in (_126_298)::_126_297))
in (_126_300)::_126_299))
in (FSharp_Format.combine FSharp_Format.hardline _126_301))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _60_392 = (let _126_306 = (as_bin_op p)
in (FStar_Option.get _126_306))
in (match (_60_392) with
| (_60_389, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _126_309 = (let _126_308 = (let _126_307 = (FSharp_Format.text txt)
in (_126_307)::(e2)::[])
in (e1)::_126_308)
in (FSharp_Format.reduce1 _126_309))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _60_402 = (let _126_313 = (as_uni_op p)
in (FStar_Option.get _126_313))
in (match (_60_402) with
| (_60_400, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _126_317 = (let _126_316 = (FSharp_Format.text txt)
in (let _126_315 = (let _126_314 = (FSharp_Format.parens e1)
in (_126_314)::[])
in (_126_316)::_126_315))
in (FSharp_Format.reduce1 _126_317))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _126_320 = (string_of_mlconstant c)
in (FSharp_Format.text _126_320))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _60_419 -> (match (_60_419) with
| (name, p) -> begin
(let _126_329 = (let _126_328 = (let _126_323 = (ptsym currentModule (path, name))
in (FSharp_Format.text _126_323))
in (let _126_327 = (let _126_326 = (FSharp_Format.text "=")
in (let _126_325 = (let _126_324 = (doc_of_pattern currentModule p)
in (_126_324)::[])
in (_126_326)::_126_325))
in (_126_328)::_126_327))
in (FSharp_Format.reduce1 _126_329))
end))
in (let _126_332 = (let _126_331 = (FSharp_Format.text "; ")
in (let _126_330 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _126_331 _126_330)))
in (FSharp_Format.cbrackets _126_332)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _126_334 = (let _126_333 = (as_standard_constructor ctor)
in (FStar_Option.get _126_333))
in (Prims.snd _126_334))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _126_336 = (let _126_335 = (as_standard_constructor ctor)
in (FStar_Option.get _126_335))
in (Prims.snd _126_336))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _126_342 = (let _126_341 = (doc_of_pattern currentModule x)
in (let _126_340 = (let _126_339 = (FSharp_Format.text "::")
in (let _126_338 = (let _126_337 = (doc_of_pattern currentModule xs)
in (_126_337)::[])
in (_126_339)::_126_338))
in (_126_341)::_126_340))
in (FSharp_Format.reduce _126_342))
end
| (_60_436, FStar_Extraction_ML_Syntax.MLP_Tuple (_60_438)::[]) -> begin
(let _126_347 = (let _126_346 = (FSharp_Format.text name)
in (let _126_345 = (let _126_344 = (let _126_343 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _126_343))
in (_126_344)::[])
in (_126_346)::_126_345))
in (FSharp_Format.reduce1 _126_347))
end
| _60_443 -> begin
(let _126_354 = (let _126_353 = (FSharp_Format.text name)
in (let _126_352 = (let _126_351 = (let _126_350 = (let _126_349 = (FSharp_Format.text ", ")
in (let _126_348 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _126_349 _126_348)))
in (FSharp_Format.parens _126_350))
in (_126_351)::[])
in (_126_353)::_126_352))
in (FSharp_Format.reduce1 _126_354))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _126_356 = (let _126_355 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_355 ps))
in (FSharp_Format.parens _126_356)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _126_357 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _126_357 ps))))
end))
and doc_of_branch = (fun currentModule _60_456 -> (match (_60_456) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _126_363 = (let _126_362 = (FSharp_Format.text "|")
in (let _126_361 = (let _126_360 = (doc_of_pattern currentModule p)
in (_126_360)::[])
in (_126_362)::_126_361))
in (FSharp_Format.reduce1 _126_363))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _126_369 = (let _126_368 = (FSharp_Format.text "|")
in (let _126_367 = (let _126_366 = (doc_of_pattern currentModule p)
in (let _126_365 = (let _126_364 = (FSharp_Format.text "when")
in (_126_364)::(c)::[])
in (_126_366)::_126_365))
in (_126_368)::_126_367))
in (FSharp_Format.reduce1 _126_369)))
end)
in (let _126_380 = (let _126_379 = (let _126_374 = (let _126_373 = (let _126_372 = (FSharp_Format.text "->")
in (let _126_371 = (let _126_370 = (FSharp_Format.text "begin")
in (_126_370)::[])
in (_126_372)::_126_371))
in (case)::_126_373)
in (FSharp_Format.reduce1 _126_374))
in (let _126_378 = (let _126_377 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _126_376 = (let _126_375 = (FSharp_Format.text "end")
in (_126_375)::[])
in (_126_377)::_126_376))
in (_126_379)::_126_378))
in (FSharp_Format.combine FSharp_Format.hardline _126_380)))
end))
and doc_of_lets = (fun currentModule _60_466 -> (match (_60_466) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun _60_473 -> (match (_60_473) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _60_470; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (FStar_List.map (fun _60_479 -> (match (_60_479) with
| (x, _60_478) -> begin
(FSharp_Format.text x)
end)) ids)
in (let ty_annot = (match (((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level))) with
| true -> begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FSharp_Format.text "")
end
| Some ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _126_387 = (let _126_386 = (FSharp_Format.text ":")
in (_126_386)::(ty)::[])
in (FSharp_Format.reduce1 _126_387)))
end)
end
| false -> begin
(FSharp_Format.text "")
end)
in (let _126_394 = (let _126_393 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _126_392 = (let _126_391 = (FSharp_Format.reduce1 ids)
in (let _126_390 = (let _126_389 = (let _126_388 = (FSharp_Format.text "=")
in (_126_388)::(e)::[])
in (ty_annot)::_126_389)
in (_126_391)::_126_390))
in (_126_393)::_126_392))
in (FSharp_Format.reduce1 _126_394))))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _126_398 = (let _126_397 = (FSharp_Format.text "let")
in (let _126_396 = (let _126_395 = (FSharp_Format.text "rec")
in (_126_395)::[])
in (_126_397)::_126_396))
in (FSharp_Format.reduce1 _126_398))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _126_402 = (let _126_401 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_126_401)::(doc)::[])
in (FSharp_Format.reduce1 _126_402))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun currentModule decls -> (let for1 = (fun _60_508 -> (match (_60_508) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _60_513 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _126_411 = (let _126_410 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_410 doc))
in (FSharp_Format.parens _126_411)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _60_526 -> (match (_60_526) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _126_418 = (let _126_417 = (let _126_416 = (FSharp_Format.text ":")
in (_126_416)::(ty)::[])
in (name)::_126_417)
in (FSharp_Format.reduce1 _126_418))))
end))
in (let _126_421 = (let _126_420 = (FSharp_Format.text "; ")
in (let _126_419 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _126_420 _126_419)))
in (FSharp_Format.cbrackets _126_421)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _60_534 -> (match (_60_534) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _60_537 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _126_424 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _126_424 tys))
in (let _126_428 = (let _126_427 = (FSharp_Format.text name)
in (let _126_426 = (let _126_425 = (FSharp_Format.text "of")
in (_126_425)::(tys)::[])
in (_126_427)::_126_426))
in (FSharp_Format.reduce1 _126_428))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _126_431 = (let _126_430 = (FSharp_Format.text "|")
in (_126_430)::(d)::[])
in (FSharp_Format.reduce1 _126_431))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _126_435 = (let _126_434 = (let _126_433 = (let _126_432 = (ptsym currentModule ([], x))
in (FSharp_Format.text _126_432))
in (_126_433)::[])
in (tparams)::_126_434)
in (FSharp_Format.reduce1 _126_435))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _126_440 = (let _126_439 = (let _126_438 = (let _126_437 = (let _126_436 = (FSharp_Format.text "=")
in (_126_436)::[])
in (doc)::_126_437)
in (FSharp_Format.reduce1 _126_438))
in (_126_439)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _126_440)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = (match (((FStar_List.length doc) > 0)) with
| true -> begin
(let _126_445 = (let _126_444 = (FSharp_Format.text "type")
in (let _126_443 = (let _126_442 = (let _126_441 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _126_441 doc))
in (_126_442)::[])
in (_126_444)::_126_443))
in (FSharp_Format.reduce1 _126_445))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _126_465 = (let _126_464 = (let _126_457 = (let _126_456 = (FSharp_Format.text "module")
in (let _126_455 = (let _126_454 = (FSharp_Format.text x)
in (let _126_453 = (let _126_452 = (FSharp_Format.text "=")
in (_126_452)::[])
in (_126_454)::_126_453))
in (_126_456)::_126_455))
in (FSharp_Format.reduce1 _126_457))
in (let _126_463 = (let _126_462 = (doc_of_sig currentModule subsig)
in (let _126_461 = (let _126_460 = (let _126_459 = (let _126_458 = (FSharp_Format.text "end")
in (_126_458)::[])
in (FSharp_Format.reduce1 _126_459))
in (_126_460)::[])
in (_126_462)::_126_461))
in (_126_464)::_126_463))
in (FSharp_Format.combine FSharp_Format.hardline _126_465))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _126_469 = (let _126_468 = (FSharp_Format.text "exception")
in (let _126_467 = (let _126_466 = (FSharp_Format.text x)
in (_126_466)::[])
in (_126_468)::_126_467))
in (FSharp_Format.reduce1 _126_469))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _126_471 = (let _126_470 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _126_470 args))
in (FSharp_Format.parens _126_471))
in (let _126_477 = (let _126_476 = (FSharp_Format.text "exception")
in (let _126_475 = (let _126_474 = (FSharp_Format.text x)
in (let _126_473 = (let _126_472 = (FSharp_Format.text "of")
in (_126_472)::(args)::[])
in (_126_474)::_126_473))
in (_126_476)::_126_475))
in (FSharp_Format.reduce1 _126_477))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_60_568, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _126_483 = (let _126_482 = (FSharp_Format.text "val")
in (let _126_481 = (let _126_480 = (FSharp_Format.text x)
in (let _126_479 = (let _126_478 = (FSharp_Format.text ": ")
in (_126_478)::(ty)::[])
in (_126_480)::_126_479))
in (_126_482)::_126_481))
in (FSharp_Format.reduce1 _126_483)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _126_494 = (let _126_493 = (FSharp_Format.text "exception")
in (let _126_492 = (let _126_491 = (FSharp_Format.text x)
in (_126_491)::[])
in (_126_493)::_126_492))
in (FSharp_Format.reduce1 _126_494))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _126_496 = (let _126_495 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _126_495 args))
in (FSharp_Format.parens _126_496))
in (let _126_502 = (let _126_501 = (FSharp_Format.text "exception")
in (let _126_500 = (let _126_499 = (FSharp_Format.text x)
in (let _126_498 = (let _126_497 = (FSharp_Format.text "of")
in (_126_497)::(args)::[])
in (_126_499)::_126_498))
in (_126_501)::_126_500))
in (FSharp_Format.reduce1 _126_502))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _126_510 = (let _126_509 = (FSharp_Format.text "let")
in (let _126_508 = (let _126_507 = (FSharp_Format.text "_")
in (let _126_506 = (let _126_505 = (FSharp_Format.text "=")
in (let _126_504 = (let _126_503 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_126_503)::[])
in (_126_505)::_126_504))
in (_126_507)::_126_506))
in (_126_509)::_126_508))
in (FSharp_Format.reduce1 _126_510))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _60_607 -> (match (_60_607) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _60_614 -> (match (_60_614) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _126_529 = (let _126_528 = (FSharp_Format.text "module")
in (let _126_527 = (let _126_526 = (FSharp_Format.text x)
in (let _126_525 = (let _126_524 = (FSharp_Format.text ":")
in (let _126_523 = (let _126_522 = (FSharp_Format.text "sig")
in (_126_522)::[])
in (_126_524)::_126_523))
in (_126_526)::_126_525))
in (_126_528)::_126_527))
in (FSharp_Format.reduce1 _126_529))
in (let tail = (let _126_531 = (let _126_530 = (FSharp_Format.text "end")
in (_126_530)::[])
in (FSharp_Format.reduce1 _126_531))
in (let doc = (FStar_Option.map (fun _60_620 -> (match (_60_620) with
| (s, _60_619) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _126_541 = (let _126_540 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _126_539 = (let _126_538 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _126_537 = (let _126_536 = (FSharp_Format.reduce sub)
in (let _126_535 = (let _126_534 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_126_534)::[])
in (_126_536)::_126_535))
in (_126_538)::_126_537))
in (_126_540)::_126_539))
in (FSharp_Format.reduce _126_541)))))))
end))
and for1_mod = (fun istop _60_633 -> (match (_60_633) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _126_554 = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _126_546 = (FSharp_Format.text "module")
in (let _126_545 = (let _126_544 = (FSharp_Format.text x)
in (_126_544)::[])
in (_126_546)::_126_545))
end
| false -> begin
(match ((not (istop))) with
| true -> begin
(let _126_553 = (FSharp_Format.text "module")
in (let _126_552 = (let _126_551 = (FSharp_Format.text x)
in (let _126_550 = (let _126_549 = (FSharp_Format.text "=")
in (let _126_548 = (let _126_547 = (FSharp_Format.text "struct")
in (_126_547)::[])
in (_126_549)::_126_548))
in (_126_551)::_126_550))
in (_126_553)::_126_552))
end
| false -> begin
[]
end)
end)
in (FSharp_Format.reduce1 _126_554))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _126_556 = (let _126_555 = (FSharp_Format.text "end")
in (_126_555)::[])
in (FSharp_Format.reduce1 _126_556))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (FStar_Option.map (fun _60_639 -> (match (_60_639) with
| (_60_637, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _126_560 = (let _126_559 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _126_559 FSharp_Format.hardline))
in (_126_560)::[])
end
| false -> begin
[]
end)
in (let _126_569 = (let _126_568 = (let _126_567 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _126_566 = (let _126_565 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _126_564 = (let _126_563 = (FSharp_Format.reduce sub)
in (let _126_562 = (let _126_561 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_126_561)::[])
in (_126_563)::_126_562))
in (_126_565)::_126_564))
in (_126_567)::_126_566))
in (FStar_List.append prefix _126_568))
in (FStar_All.pipe_left FSharp_Format.reduce _126_569))))))))
end))
in (let docs = (FStar_List.map (fun _60_651 -> (match (_60_651) with
| (x, s, m) -> begin
(let _126_571 = (for1_mod true (x, s, m))
in (x, _126_571))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _126_578 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _126_578 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _126_583 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _126_583 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





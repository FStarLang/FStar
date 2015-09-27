
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
(let _129_31 = (let _129_30 = (let _129_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_129_29)::[])
in (FStar_List.append pfx _129_30))
in Some (_129_31))
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
(let _129_36 = (path_of_ns currentModule ns)
in (_129_36, x))
end))
end))

let ptsym_of_symbol = (fun s -> (match (((let _129_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _129_39)) <> (FStar_String.get s 0))) with
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
(let _129_46 = (let _129_45 = (let _129_44 = (ptsym_of_symbol s)
in (_129_44)::[])
in (FStar_List.append p _129_45))
in (FStar_String.concat "." _129_46))
end))
end))

let ptctor = (fun currentModule mlp -> (let _60_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_55) with
| (p, s) -> begin
(let s = (match (((let _129_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _129_51)) <> (FStar_String.get s 0))) with
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
(let _129_92 = (let _129_91 = (encode_char c)
in (Prims.strcat "\'" _129_91))
in (Prims.strcat _129_92 "\'"))
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
in (let _129_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _129_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _129_107 = (let _129_106 = (let _129_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _129_105 doc))
in (FSharp_Format.hbox _129_106))
in (FSharp_Format.parens _129_107))
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
in (let _129_110 = (let _129_109 = (let _129_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _129_108 args))
in (FSharp_Format.hbox _129_109))
in (FSharp_Format.parens _129_110)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _129_112 = (let _129_111 = (as_standard_type name)
in (FStar_Option.get _129_111))
in (Prims.snd _129_112))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _129_116 = (let _129_115 = (let _129_114 = (let _129_113 = (FSharp_Format.text name)
in (_129_113)::[])
in (args)::_129_114)
in (FSharp_Format.reduce1 _129_115))
in (FSharp_Format.hbox _129_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _60_202, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _129_121 = (let _129_120 = (let _129_119 = (let _129_118 = (let _129_117 = (FSharp_Format.text " -> ")
in (_129_117)::(d2)::[])
in (d1)::_129_118)
in (FSharp_Format.reduce1 _129_119))
in (FSharp_Format.hbox _129_120))
in (maybe_paren outer t_prio_fun _129_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_App (t1, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _129_126 = (let _129_125 = (let _129_124 = (let _129_123 = (let _129_122 = (FSharp_Format.text " ")
in (_129_122)::(d1)::[])
in (d2)::_129_123)
in (FSharp_Format.reduce1 _129_124))
in (FSharp_Format.hbox _129_125))
in (maybe_paren outer t_prio_fun _129_126))))
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
(let _129_151 = (let _129_150 = (let _129_149 = (FSharp_Format.text "Prims.checked_cast")
in (_129_149)::(doc)::[])
in (FSharp_Format.reduce _129_150))
in (FSharp_Format.parens _129_151))
end
| false -> begin
(let _129_154 = (let _129_153 = (let _129_152 = (FSharp_Format.text "Obj.magic ")
in (_129_152)::(doc)::[])
in (FSharp_Format.reduce _129_153))
in (FSharp_Format.parens _129_154))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _129_158 = (let _129_157 = (let _129_156 = (FSharp_Format.text ";")
in (_129_156)::(FSharp_Format.hardline)::[])
in (d)::_129_157)
in (FSharp_Format.reduce _129_158))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _129_159 = (string_of_mlconstant c)
in (FSharp_Format.text _129_159))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _60_236) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _129_160 = (ptsym currentModule path)
in (FSharp_Format.text _129_160))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _60_248 -> (match (_60_248) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _129_167 = (let _129_166 = (let _129_163 = (ptsym currentModule (path, name))
in (FSharp_Format.text _129_163))
in (let _129_165 = (let _129_164 = (FSharp_Format.text "=")
in (_129_164)::(doc)::[])
in (_129_166)::_129_165))
in (FSharp_Format.reduce1 _129_167)))
end))
in (let _129_170 = (let _129_169 = (FSharp_Format.text "; ")
in (let _129_168 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _129_169 _129_168)))
in (FSharp_Format.cbrackets _129_170)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _129_172 = (let _129_171 = (as_standard_constructor ctor)
in (FStar_Option.get _129_171))
in (Prims.snd _129_172))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _129_174 = (let _129_173 = (as_standard_constructor ctor)
in (FStar_Option.get _129_173))
in (Prims.snd _129_174))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _129_178 = (let _129_177 = (FSharp_Format.parens x)
in (let _129_176 = (let _129_175 = (FSharp_Format.text "::")
in (_129_175)::(xs)::[])
in (_129_177)::_129_176))
in (FSharp_Format.reduce _129_178))
end
| (_60_267, _60_269) -> begin
(let _129_184 = (let _129_183 = (FSharp_Format.text name)
in (let _129_182 = (let _129_181 = (let _129_180 = (let _129_179 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _129_179 args))
in (FSharp_Format.parens _129_180))
in (_129_181)::[])
in (_129_183)::_129_182))
in (FSharp_Format.reduce1 _129_184))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _129_186 = (let _129_185 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _129_185 docs))
in (FSharp_Format.parens _129_186))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _129_192 = (let _129_191 = (let _129_190 = (let _129_189 = (let _129_188 = (let _129_187 = (FSharp_Format.text "in")
in (_129_187)::(body)::[])
in (FSharp_Format.reduce1 _129_188))
in (_129_189)::[])
in (doc)::_129_190)
in (FSharp_Format.combine FSharp_Format.hardline _129_191))
in (FSharp_Format.parens _129_192))))
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
in (let _129_193 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _129_193))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _129_198 = (let _129_197 = (let _129_196 = (FSharp_Format.text ".")
in (let _129_195 = (let _129_194 = (FSharp_Format.text (Prims.snd f))
in (_129_194)::[])
in (_129_196)::_129_195))
in (e)::_129_197)
in (FSharp_Format.reduce _129_198))
end
| false -> begin
(let _129_204 = (let _129_203 = (let _129_202 = (FSharp_Format.text ".")
in (let _129_201 = (let _129_200 = (let _129_199 = (ptsym currentModule f)
in (FSharp_Format.text _129_199))
in (_129_200)::[])
in (_129_202)::_129_201))
in (e)::_129_203)
in (FSharp_Format.reduce _129_204))
end)
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _129_220 = (let _129_219 = (FSharp_Format.text "(")
in (let _129_218 = (let _129_217 = (FSharp_Format.text x)
in (let _129_216 = (let _129_215 = (match (xt) with
| Some (xxt) -> begin
(let _129_212 = (let _129_211 = (FSharp_Format.text " : ")
in (let _129_210 = (let _129_209 = (doc_of_mltype currentModule outer xxt)
in (_129_209)::[])
in (_129_211)::_129_210))
in (FSharp_Format.reduce1 _129_212))
end
| _60_338 -> begin
(FSharp_Format.text "")
end)
in (let _129_214 = (let _129_213 = (FSharp_Format.text ")")
in (_129_213)::[])
in (_129_215)::_129_214))
in (_129_217)::_129_216))
in (_129_219)::_129_218))
in (FSharp_Format.reduce1 _129_220))
end
| false -> begin
(FSharp_Format.text x)
end))
in (let ids = (FStar_List.map (fun _60_344 -> (match (_60_344) with
| ((x, _60_341), xt) -> begin
(bvar_annot x xt)
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _129_227 = (let _129_226 = (FSharp_Format.text "fun")
in (let _129_225 = (let _129_224 = (FSharp_Format.reduce1 ids)
in (let _129_223 = (let _129_222 = (FSharp_Format.text "->")
in (_129_222)::(body)::[])
in (_129_224)::_129_223))
in (_129_226)::_129_225))
in (FSharp_Format.reduce1 _129_227))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _129_240 = (let _129_239 = (let _129_234 = (let _129_233 = (FSharp_Format.text "if")
in (let _129_232 = (let _129_231 = (let _129_230 = (FSharp_Format.text "then")
in (let _129_229 = (let _129_228 = (FSharp_Format.text "begin")
in (_129_228)::[])
in (_129_230)::_129_229))
in (cond)::_129_231)
in (_129_233)::_129_232))
in (FSharp_Format.reduce1 _129_234))
in (let _129_238 = (let _129_237 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _129_236 = (let _129_235 = (FSharp_Format.text "end")
in (_129_235)::[])
in (_129_237)::_129_236))
in (_129_239)::_129_238))
in (FSharp_Format.combine FSharp_Format.hardline _129_240))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _129_263 = (let _129_262 = (let _129_247 = (let _129_246 = (FSharp_Format.text "if")
in (let _129_245 = (let _129_244 = (let _129_243 = (FSharp_Format.text "then")
in (let _129_242 = (let _129_241 = (FSharp_Format.text "begin")
in (_129_241)::[])
in (_129_243)::_129_242))
in (cond)::_129_244)
in (_129_246)::_129_245))
in (FSharp_Format.reduce1 _129_247))
in (let _129_261 = (let _129_260 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _129_259 = (let _129_258 = (let _129_253 = (let _129_252 = (FSharp_Format.text "end")
in (let _129_251 = (let _129_250 = (FSharp_Format.text "else")
in (let _129_249 = (let _129_248 = (FSharp_Format.text "begin")
in (_129_248)::[])
in (_129_250)::_129_249))
in (_129_252)::_129_251))
in (FSharp_Format.reduce1 _129_253))
in (let _129_257 = (let _129_256 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _129_255 = (let _129_254 = (FSharp_Format.text "end")
in (_129_254)::[])
in (_129_256)::_129_255))
in (_129_258)::_129_257))
in (_129_260)::_129_259))
in (_129_262)::_129_261))
in (FSharp_Format.combine FSharp_Format.hardline _129_263))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _129_270 = (let _129_269 = (let _129_268 = (FSharp_Format.text "match")
in (let _129_267 = (let _129_266 = (FSharp_Format.parens cond)
in (let _129_265 = (let _129_264 = (FSharp_Format.text "with")
in (_129_264)::[])
in (_129_266)::_129_265))
in (_129_268)::_129_267))
in (FSharp_Format.reduce1 _129_269))
in (_129_270)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _129_275 = (let _129_274 = (FSharp_Format.text "raise")
in (let _129_273 = (let _129_272 = (let _129_271 = (ptctor currentModule exn)
in (FSharp_Format.text _129_271))
in (_129_272)::[])
in (_129_274)::_129_273))
in (FSharp_Format.reduce1 _129_275))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _129_284 = (let _129_283 = (FSharp_Format.text "raise")
in (let _129_282 = (let _129_281 = (let _129_276 = (ptctor currentModule exn)
in (FSharp_Format.text _129_276))
in (let _129_280 = (let _129_279 = (let _129_278 = (let _129_277 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _129_277 args))
in (FSharp_Format.parens _129_278))
in (_129_279)::[])
in (_129_281)::_129_280))
in (_129_283)::_129_282))
in (FSharp_Format.reduce1 _129_284)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _129_301 = (let _129_300 = (let _129_288 = (let _129_287 = (FSharp_Format.text "try")
in (let _129_286 = (let _129_285 = (FSharp_Format.text "begin")
in (_129_285)::[])
in (_129_287)::_129_286))
in (FSharp_Format.reduce1 _129_288))
in (let _129_299 = (let _129_298 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _129_297 = (let _129_296 = (let _129_292 = (let _129_291 = (FSharp_Format.text "end")
in (let _129_290 = (let _129_289 = (FSharp_Format.text "with")
in (_129_289)::[])
in (_129_291)::_129_290))
in (FSharp_Format.reduce1 _129_292))
in (let _129_295 = (let _129_294 = (let _129_293 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _129_293))
in (_129_294)::[])
in (_129_296)::_129_295))
in (_129_298)::_129_297))
in (_129_300)::_129_299))
in (FSharp_Format.combine FSharp_Format.hardline _129_301))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _60_392 = (let _129_306 = (as_bin_op p)
in (FStar_Option.get _129_306))
in (match (_60_392) with
| (_60_389, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _129_309 = (let _129_308 = (let _129_307 = (FSharp_Format.text txt)
in (_129_307)::(e2)::[])
in (e1)::_129_308)
in (FSharp_Format.reduce1 _129_309))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _60_402 = (let _129_313 = (as_uni_op p)
in (FStar_Option.get _129_313))
in (match (_60_402) with
| (_60_400, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _129_317 = (let _129_316 = (FSharp_Format.text txt)
in (let _129_315 = (let _129_314 = (FSharp_Format.parens e1)
in (_129_314)::[])
in (_129_316)::_129_315))
in (FSharp_Format.reduce1 _129_317))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _129_320 = (string_of_mlconstant c)
in (FSharp_Format.text _129_320))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _60_419 -> (match (_60_419) with
| (name, p) -> begin
(let _129_329 = (let _129_328 = (let _129_323 = (ptsym currentModule (path, name))
in (FSharp_Format.text _129_323))
in (let _129_327 = (let _129_326 = (FSharp_Format.text "=")
in (let _129_325 = (let _129_324 = (doc_of_pattern currentModule p)
in (_129_324)::[])
in (_129_326)::_129_325))
in (_129_328)::_129_327))
in (FSharp_Format.reduce1 _129_329))
end))
in (let _129_332 = (let _129_331 = (FSharp_Format.text "; ")
in (let _129_330 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _129_331 _129_330)))
in (FSharp_Format.cbrackets _129_332)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _129_334 = (let _129_333 = (as_standard_constructor ctor)
in (FStar_Option.get _129_333))
in (Prims.snd _129_334))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _129_336 = (let _129_335 = (as_standard_constructor ctor)
in (FStar_Option.get _129_335))
in (Prims.snd _129_336))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _129_342 = (let _129_341 = (doc_of_pattern currentModule x)
in (let _129_340 = (let _129_339 = (FSharp_Format.text "::")
in (let _129_338 = (let _129_337 = (doc_of_pattern currentModule xs)
in (_129_337)::[])
in (_129_339)::_129_338))
in (_129_341)::_129_340))
in (FSharp_Format.reduce _129_342))
end
| (_60_436, FStar_Extraction_ML_Syntax.MLP_Tuple (_60_438)::[]) -> begin
(let _129_347 = (let _129_346 = (FSharp_Format.text name)
in (let _129_345 = (let _129_344 = (let _129_343 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _129_343))
in (_129_344)::[])
in (_129_346)::_129_345))
in (FSharp_Format.reduce1 _129_347))
end
| _60_443 -> begin
(let _129_354 = (let _129_353 = (FSharp_Format.text name)
in (let _129_352 = (let _129_351 = (let _129_350 = (let _129_349 = (FSharp_Format.text ", ")
in (let _129_348 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _129_349 _129_348)))
in (FSharp_Format.parens _129_350))
in (_129_351)::[])
in (_129_353)::_129_352))
in (FSharp_Format.reduce1 _129_354))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _129_356 = (let _129_355 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _129_355 ps))
in (FSharp_Format.parens _129_356)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _129_357 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _129_357 ps))))
end))
and doc_of_branch = (fun currentModule _60_456 -> (match (_60_456) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _129_363 = (let _129_362 = (FSharp_Format.text "|")
in (let _129_361 = (let _129_360 = (doc_of_pattern currentModule p)
in (_129_360)::[])
in (_129_362)::_129_361))
in (FSharp_Format.reduce1 _129_363))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _129_369 = (let _129_368 = (FSharp_Format.text "|")
in (let _129_367 = (let _129_366 = (doc_of_pattern currentModule p)
in (let _129_365 = (let _129_364 = (FSharp_Format.text "when")
in (_129_364)::(c)::[])
in (_129_366)::_129_365))
in (_129_368)::_129_367))
in (FSharp_Format.reduce1 _129_369)))
end)
in (let _129_380 = (let _129_379 = (let _129_374 = (let _129_373 = (let _129_372 = (FSharp_Format.text "->")
in (let _129_371 = (let _129_370 = (FSharp_Format.text "begin")
in (_129_370)::[])
in (_129_372)::_129_371))
in (case)::_129_373)
in (FSharp_Format.reduce1 _129_374))
in (let _129_378 = (let _129_377 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _129_376 = (let _129_375 = (FSharp_Format.text "end")
in (_129_375)::[])
in (_129_377)::_129_376))
in (_129_379)::_129_378))
in (FSharp_Format.combine FSharp_Format.hardline _129_380)))
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
in (let _129_387 = (let _129_386 = (FSharp_Format.text ":")
in (_129_386)::(ty)::[])
in (FSharp_Format.reduce1 _129_387)))
end)
end
| false -> begin
(FSharp_Format.text "")
end)
in (let _129_394 = (let _129_393 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _129_392 = (let _129_391 = (FSharp_Format.reduce1 ids)
in (let _129_390 = (let _129_389 = (let _129_388 = (FSharp_Format.text "=")
in (_129_388)::(e)::[])
in (ty_annot)::_129_389)
in (_129_391)::_129_390))
in (_129_393)::_129_392))
in (FSharp_Format.reduce1 _129_394))))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _129_398 = (let _129_397 = (FSharp_Format.text "let")
in (let _129_396 = (let _129_395 = (FSharp_Format.text "rec")
in (_129_395)::[])
in (_129_397)::_129_396))
in (FSharp_Format.reduce1 _129_398))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _129_402 = (let _129_401 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_129_401)::(doc)::[])
in (FSharp_Format.reduce1 _129_402))) lets)
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
in (let _129_411 = (let _129_410 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _129_410 doc))
in (FSharp_Format.parens _129_411)))
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
in (let _129_418 = (let _129_417 = (let _129_416 = (FSharp_Format.text ":")
in (_129_416)::(ty)::[])
in (name)::_129_417)
in (FSharp_Format.reduce1 _129_418))))
end))
in (let _129_421 = (let _129_420 = (FSharp_Format.text "; ")
in (let _129_419 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _129_420 _129_419)))
in (FSharp_Format.cbrackets _129_421)))
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
in (let tys = (let _129_424 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _129_424 tys))
in (let _129_428 = (let _129_427 = (FSharp_Format.text name)
in (let _129_426 = (let _129_425 = (FSharp_Format.text "of")
in (_129_425)::(tys)::[])
in (_129_427)::_129_426))
in (FSharp_Format.reduce1 _129_428))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _129_431 = (let _129_430 = (FSharp_Format.text "|")
in (_129_430)::(d)::[])
in (FSharp_Format.reduce1 _129_431))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _129_435 = (let _129_434 = (let _129_433 = (let _129_432 = (ptsym currentModule ([], x))
in (FSharp_Format.text _129_432))
in (_129_433)::[])
in (tparams)::_129_434)
in (FSharp_Format.reduce1 _129_435))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _129_440 = (let _129_439 = (let _129_438 = (let _129_437 = (let _129_436 = (FSharp_Format.text "=")
in (_129_436)::[])
in (doc)::_129_437)
in (FSharp_Format.reduce1 _129_438))
in (_129_439)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _129_440)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = (match (((FStar_List.length doc) > 0)) with
| true -> begin
(let _129_445 = (let _129_444 = (FSharp_Format.text "type")
in (let _129_443 = (let _129_442 = (let _129_441 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _129_441 doc))
in (_129_442)::[])
in (_129_444)::_129_443))
in (FSharp_Format.reduce1 _129_445))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _129_465 = (let _129_464 = (let _129_457 = (let _129_456 = (FSharp_Format.text "module")
in (let _129_455 = (let _129_454 = (FSharp_Format.text x)
in (let _129_453 = (let _129_452 = (FSharp_Format.text "=")
in (_129_452)::[])
in (_129_454)::_129_453))
in (_129_456)::_129_455))
in (FSharp_Format.reduce1 _129_457))
in (let _129_463 = (let _129_462 = (doc_of_sig currentModule subsig)
in (let _129_461 = (let _129_460 = (let _129_459 = (let _129_458 = (FSharp_Format.text "end")
in (_129_458)::[])
in (FSharp_Format.reduce1 _129_459))
in (_129_460)::[])
in (_129_462)::_129_461))
in (_129_464)::_129_463))
in (FSharp_Format.combine FSharp_Format.hardline _129_465))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _129_469 = (let _129_468 = (FSharp_Format.text "exception")
in (let _129_467 = (let _129_466 = (FSharp_Format.text x)
in (_129_466)::[])
in (_129_468)::_129_467))
in (FSharp_Format.reduce1 _129_469))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _129_471 = (let _129_470 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _129_470 args))
in (FSharp_Format.parens _129_471))
in (let _129_477 = (let _129_476 = (FSharp_Format.text "exception")
in (let _129_475 = (let _129_474 = (FSharp_Format.text x)
in (let _129_473 = (let _129_472 = (FSharp_Format.text "of")
in (_129_472)::(args)::[])
in (_129_474)::_129_473))
in (_129_476)::_129_475))
in (FSharp_Format.reduce1 _129_477))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_60_568, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _129_483 = (let _129_482 = (FSharp_Format.text "val")
in (let _129_481 = (let _129_480 = (FSharp_Format.text x)
in (let _129_479 = (let _129_478 = (FSharp_Format.text ": ")
in (_129_478)::(ty)::[])
in (_129_480)::_129_479))
in (_129_482)::_129_481))
in (FSharp_Format.reduce1 _129_483)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _129_494 = (let _129_493 = (FSharp_Format.text "exception")
in (let _129_492 = (let _129_491 = (FSharp_Format.text x)
in (_129_491)::[])
in (_129_493)::_129_492))
in (FSharp_Format.reduce1 _129_494))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _129_496 = (let _129_495 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _129_495 args))
in (FSharp_Format.parens _129_496))
in (let _129_502 = (let _129_501 = (FSharp_Format.text "exception")
in (let _129_500 = (let _129_499 = (FSharp_Format.text x)
in (let _129_498 = (let _129_497 = (FSharp_Format.text "of")
in (_129_497)::(args)::[])
in (_129_499)::_129_498))
in (_129_501)::_129_500))
in (FSharp_Format.reduce1 _129_502))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _129_510 = (let _129_509 = (FSharp_Format.text "let")
in (let _129_508 = (let _129_507 = (FSharp_Format.text "_")
in (let _129_506 = (let _129_505 = (FSharp_Format.text "=")
in (let _129_504 = (let _129_503 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_129_503)::[])
in (_129_505)::_129_504))
in (_129_507)::_129_506))
in (_129_509)::_129_508))
in (FSharp_Format.reduce1 _129_510))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _60_607 -> (match (_60_607) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _60_614 -> (match (_60_614) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _129_529 = (let _129_528 = (FSharp_Format.text "module")
in (let _129_527 = (let _129_526 = (FSharp_Format.text x)
in (let _129_525 = (let _129_524 = (FSharp_Format.text ":")
in (let _129_523 = (let _129_522 = (FSharp_Format.text "sig")
in (_129_522)::[])
in (_129_524)::_129_523))
in (_129_526)::_129_525))
in (_129_528)::_129_527))
in (FSharp_Format.reduce1 _129_529))
in (let tail = (let _129_531 = (let _129_530 = (FSharp_Format.text "end")
in (_129_530)::[])
in (FSharp_Format.reduce1 _129_531))
in (let doc = (FStar_Option.map (fun _60_620 -> (match (_60_620) with
| (s, _60_619) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _129_541 = (let _129_540 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _129_539 = (let _129_538 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _129_537 = (let _129_536 = (FSharp_Format.reduce sub)
in (let _129_535 = (let _129_534 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_129_534)::[])
in (_129_536)::_129_535))
in (_129_538)::_129_537))
in (_129_540)::_129_539))
in (FSharp_Format.reduce _129_541)))))))
end))
and for1_mod = (fun istop _60_633 -> (match (_60_633) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _129_554 = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _129_546 = (FSharp_Format.text "module")
in (let _129_545 = (let _129_544 = (FSharp_Format.text x)
in (_129_544)::[])
in (_129_546)::_129_545))
end
| false -> begin
(match ((not (istop))) with
| true -> begin
(let _129_553 = (FSharp_Format.text "module")
in (let _129_552 = (let _129_551 = (FSharp_Format.text x)
in (let _129_550 = (let _129_549 = (FSharp_Format.text "=")
in (let _129_548 = (let _129_547 = (FSharp_Format.text "struct")
in (_129_547)::[])
in (_129_549)::_129_548))
in (_129_551)::_129_550))
in (_129_553)::_129_552))
end
| false -> begin
[]
end)
end)
in (FSharp_Format.reduce1 _129_554))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _129_556 = (let _129_555 = (FSharp_Format.text "end")
in (_129_555)::[])
in (FSharp_Format.reduce1 _129_556))
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
(let _129_560 = (let _129_559 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _129_559 FSharp_Format.hardline))
in (_129_560)::[])
end
| false -> begin
[]
end)
in (let _129_569 = (let _129_568 = (let _129_567 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _129_566 = (let _129_565 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _129_564 = (let _129_563 = (FSharp_Format.reduce sub)
in (let _129_562 = (let _129_561 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_129_561)::[])
in (_129_563)::_129_562))
in (_129_565)::_129_564))
in (_129_567)::_129_566))
in (FStar_List.append prefix _129_568))
in (FStar_All.pipe_left FSharp_Format.reduce _129_569))))))))
end))
in (let docs = (FStar_List.map (fun _60_651 -> (match (_60_651) with
| (x, s, m) -> begin
(let _129_571 = (for1_mod true (x, s, m))
in (x, _129_571))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _129_578 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _129_578 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _129_583 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _129_583 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))






open Prims
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
(let _125_31 = (let _125_30 = (let _125_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_125_29)::[])
in (FStar_List.append pfx _125_30))
in Some (_125_31))
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
(let _125_36 = (path_of_ns currentModule ns)
in (_125_36, x))
end))
end))

let ptsym_of_symbol = (fun s -> (match (((let _125_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _125_39)) <> (FStar_String.get s 0))) with
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
(let _125_46 = (let _125_45 = (let _125_44 = (ptsym_of_symbol s)
in (_125_44)::[])
in (FStar_List.append p _125_45))
in (FStar_String.concat "." _125_46))
end))
end))

let ptctor = (fun currentModule mlp -> (let _60_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_55) with
| (p, s) -> begin
(let s = (match (((let _125_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _125_51)) <> (FStar_String.get s 0))) with
| true -> begin
(Prims.strcat "U__" s)
end
| false -> begin
s
end)
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

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
(let _125_92 = (let _125_91 = (encode_char c)
in (Prims.strcat "\'" _125_91))
in (Prims.strcat _125_92 "\'"))
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
| FStar_Extraction_ML_Syntax.MLC_Int (s) -> begin
(match ((FStar_ST.read FStar_Options.use_native_int)) with
| true -> begin
s
end
| false -> begin
(Prims.strcat (Prims.strcat "(Prims.parse_int \"" s) "\")")
end)
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
in (let _125_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _125_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _125_107 = (let _125_106 = (let _125_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_105 doc))
in (FSharp_Format.hbox _125_106))
in (FSharp_Format.parens _125_107))
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
| _60_198 -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _125_110 = (let _125_109 = (let _125_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_108 args))
in (FSharp_Format.hbox _125_109))
in (FSharp_Format.parens _125_110)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _125_112 = (let _125_111 = (as_standard_type name)
in (FStar_Option.get _125_111))
in (Prims.snd _125_112))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _125_116 = (let _125_115 = (let _125_114 = (let _125_113 = (FSharp_Format.text name)
in (_125_113)::[])
in (args)::_125_114)
in (FSharp_Format.reduce1 _125_115))
in (FSharp_Format.hbox _125_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _60_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _125_121 = (let _125_120 = (let _125_119 = (let _125_118 = (let _125_117 = (FSharp_Format.text " -> ")
in (_125_117)::(d2)::[])
in (d1)::_125_118)
in (FSharp_Format.reduce1 _125_119))
in (FSharp_Format.hbox _125_120))
in (maybe_paren outer t_prio_fun _125_121))))
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
(let _125_146 = (let _125_145 = (let _125_144 = (FSharp_Format.text "Prims.checked_cast")
in (_125_144)::(doc)::[])
in (FSharp_Format.reduce _125_145))
in (FSharp_Format.parens _125_146))
end
| false -> begin
(let _125_149 = (let _125_148 = (let _125_147 = (FSharp_Format.text "Obj.magic ")
in (_125_147)::(doc)::[])
in (FSharp_Format.reduce _125_148))
in (FSharp_Format.parens _125_149))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _125_153 = (let _125_152 = (let _125_151 = (FSharp_Format.text ";")
in (_125_151)::(FSharp_Format.hardline)::[])
in (d)::_125_152)
in (FSharp_Format.reduce _125_153))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _125_154 = (string_of_mlconstant c)
in (FSharp_Format.text _125_154))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _60_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _125_155 = (ptsym currentModule path)
in (FSharp_Format.text _125_155))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _60_244 -> (match (_60_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_162 = (let _125_161 = (let _125_158 = (ptsym currentModule (path, name))
in (FSharp_Format.text _125_158))
in (let _125_160 = (let _125_159 = (FSharp_Format.text "=")
in (_125_159)::(doc)::[])
in (_125_161)::_125_160))
in (FSharp_Format.reduce1 _125_162)))
end))
in (let _125_165 = (let _125_164 = (FSharp_Format.text "; ")
in (let _125_163 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _125_164 _125_163)))
in (FSharp_Format.cbrackets _125_165)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_167 = (let _125_166 = (as_standard_constructor ctor)
in (FStar_Option.get _125_166))
in (Prims.snd _125_167))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_169 = (let _125_168 = (as_standard_constructor ctor)
in (FStar_Option.get _125_168))
in (Prims.snd _125_169))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _125_173 = (let _125_172 = (FSharp_Format.parens x)
in (let _125_171 = (let _125_170 = (FSharp_Format.text "::")
in (_125_170)::(xs)::[])
in (_125_172)::_125_171))
in (FSharp_Format.reduce _125_173))
end
| (_60_263, _60_265) -> begin
(let _125_179 = (let _125_178 = (FSharp_Format.text name)
in (let _125_177 = (let _125_176 = (let _125_175 = (let _125_174 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_174 args))
in (FSharp_Format.parens _125_175))
in (_125_176)::[])
in (_125_178)::_125_177))
in (FSharp_Format.reduce1 _125_179))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _125_181 = (let _125_180 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_180 docs))
in (FSharp_Format.parens _125_181))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _125_187 = (let _125_186 = (let _125_185 = (let _125_184 = (let _125_183 = (let _125_182 = (FSharp_Format.text "in")
in (_125_182)::(body)::[])
in (FSharp_Format.reduce1 _125_183))
in (_125_184)::[])
in (doc)::_125_185)
in (FSharp_Format.combine FSharp_Format.hardline _125_186))
in (FSharp_Format.parens _125_187))))
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
| _60_315 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _125_188 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _125_188))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_193 = (let _125_192 = (let _125_191 = (FSharp_Format.text ".")
in (let _125_190 = (let _125_189 = (FSharp_Format.text (Prims.snd f))
in (_125_189)::[])
in (_125_191)::_125_190))
in (e)::_125_192)
in (FSharp_Format.reduce _125_193))
end
| false -> begin
(let _125_199 = (let _125_198 = (let _125_197 = (FSharp_Format.text ".")
in (let _125_196 = (let _125_195 = (let _125_194 = (ptsym currentModule f)
in (FSharp_Format.text _125_194))
in (_125_195)::[])
in (_125_197)::_125_196))
in (e)::_125_198)
in (FSharp_Format.reduce _125_199))
end)
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_215 = (let _125_214 = (FSharp_Format.text "(")
in (let _125_213 = (let _125_212 = (FSharp_Format.text x)
in (let _125_211 = (let _125_210 = (match (xt) with
| Some (xxt) -> begin
(let _125_207 = (let _125_206 = (FSharp_Format.text " : ")
in (let _125_205 = (let _125_204 = (doc_of_mltype currentModule outer xxt)
in (_125_204)::[])
in (_125_206)::_125_205))
in (FSharp_Format.reduce1 _125_207))
end
| _60_334 -> begin
(FSharp_Format.text "")
end)
in (let _125_209 = (let _125_208 = (FSharp_Format.text ")")
in (_125_208)::[])
in (_125_210)::_125_209))
in (_125_212)::_125_211))
in (_125_214)::_125_213))
in (FSharp_Format.reduce1 _125_215))
end
| false -> begin
(FSharp_Format.text x)
end))
in (let ids = (FStar_List.map (fun _60_340 -> (match (_60_340) with
| ((x, _60_337), xt) -> begin
(bvar_annot x xt)
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _125_222 = (let _125_221 = (FSharp_Format.text "fun")
in (let _125_220 = (let _125_219 = (FSharp_Format.reduce1 ids)
in (let _125_218 = (let _125_217 = (FSharp_Format.text "->")
in (_125_217)::(body)::[])
in (_125_219)::_125_218))
in (_125_221)::_125_220))
in (FSharp_Format.reduce1 _125_222))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _125_235 = (let _125_234 = (let _125_229 = (let _125_228 = (FSharp_Format.text "if")
in (let _125_227 = (let _125_226 = (let _125_225 = (FSharp_Format.text "then")
in (let _125_224 = (let _125_223 = (FSharp_Format.text "begin")
in (_125_223)::[])
in (_125_225)::_125_224))
in (cond)::_125_226)
in (_125_228)::_125_227))
in (FSharp_Format.reduce1 _125_229))
in (let _125_233 = (let _125_232 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _125_231 = (let _125_230 = (FSharp_Format.text "end")
in (_125_230)::[])
in (_125_232)::_125_231))
in (_125_234)::_125_233))
in (FSharp_Format.combine FSharp_Format.hardline _125_235))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _125_258 = (let _125_257 = (let _125_242 = (let _125_241 = (FSharp_Format.text "if")
in (let _125_240 = (let _125_239 = (let _125_238 = (FSharp_Format.text "then")
in (let _125_237 = (let _125_236 = (FSharp_Format.text "begin")
in (_125_236)::[])
in (_125_238)::_125_237))
in (cond)::_125_239)
in (_125_241)::_125_240))
in (FSharp_Format.reduce1 _125_242))
in (let _125_256 = (let _125_255 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _125_254 = (let _125_253 = (let _125_248 = (let _125_247 = (FSharp_Format.text "end")
in (let _125_246 = (let _125_245 = (FSharp_Format.text "else")
in (let _125_244 = (let _125_243 = (FSharp_Format.text "begin")
in (_125_243)::[])
in (_125_245)::_125_244))
in (_125_247)::_125_246))
in (FSharp_Format.reduce1 _125_248))
in (let _125_252 = (let _125_251 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _125_250 = (let _125_249 = (FSharp_Format.text "end")
in (_125_249)::[])
in (_125_251)::_125_250))
in (_125_253)::_125_252))
in (_125_255)::_125_254))
in (_125_257)::_125_256))
in (FSharp_Format.combine FSharp_Format.hardline _125_258))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _125_265 = (let _125_264 = (let _125_263 = (FSharp_Format.text "match")
in (let _125_262 = (let _125_261 = (FSharp_Format.parens cond)
in (let _125_260 = (let _125_259 = (FSharp_Format.text "with")
in (_125_259)::[])
in (_125_261)::_125_260))
in (_125_263)::_125_262))
in (FSharp_Format.reduce1 _125_264))
in (_125_265)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _125_270 = (let _125_269 = (FSharp_Format.text "raise")
in (let _125_268 = (let _125_267 = (let _125_266 = (ptctor currentModule exn)
in (FSharp_Format.text _125_266))
in (_125_267)::[])
in (_125_269)::_125_268))
in (FSharp_Format.reduce1 _125_270))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _125_279 = (let _125_278 = (FSharp_Format.text "raise")
in (let _125_277 = (let _125_276 = (let _125_271 = (ptctor currentModule exn)
in (FSharp_Format.text _125_271))
in (let _125_275 = (let _125_274 = (let _125_273 = (let _125_272 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_272 args))
in (FSharp_Format.parens _125_273))
in (_125_274)::[])
in (_125_276)::_125_275))
in (_125_278)::_125_277))
in (FSharp_Format.reduce1 _125_279)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _125_296 = (let _125_295 = (let _125_283 = (let _125_282 = (FSharp_Format.text "try")
in (let _125_281 = (let _125_280 = (FSharp_Format.text "begin")
in (_125_280)::[])
in (_125_282)::_125_281))
in (FSharp_Format.reduce1 _125_283))
in (let _125_294 = (let _125_293 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_292 = (let _125_291 = (let _125_287 = (let _125_286 = (FSharp_Format.text "end")
in (let _125_285 = (let _125_284 = (FSharp_Format.text "with")
in (_125_284)::[])
in (_125_286)::_125_285))
in (FSharp_Format.reduce1 _125_287))
in (let _125_290 = (let _125_289 = (let _125_288 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _125_288))
in (_125_289)::[])
in (_125_291)::_125_290))
in (_125_293)::_125_292))
in (_125_295)::_125_294))
in (FSharp_Format.combine FSharp_Format.hardline _125_296))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _60_388 = (let _125_301 = (as_bin_op p)
in (FStar_Option.get _125_301))
in (match (_60_388) with
| (_60_385, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _125_304 = (let _125_303 = (let _125_302 = (FSharp_Format.text txt)
in (_125_302)::(e2)::[])
in (e1)::_125_303)
in (FSharp_Format.reduce1 _125_304))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _60_398 = (let _125_308 = (as_uni_op p)
in (FStar_Option.get _125_308))
in (match (_60_398) with
| (_60_396, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _125_312 = (let _125_311 = (FSharp_Format.text txt)
in (let _125_310 = (let _125_309 = (FSharp_Format.parens e1)
in (_125_309)::[])
in (_125_311)::_125_310))
in (FSharp_Format.reduce1 _125_312))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _125_315 = (string_of_mlconstant c)
in (FSharp_Format.text _125_315))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _60_415 -> (match (_60_415) with
| (name, p) -> begin
(let _125_324 = (let _125_323 = (let _125_318 = (ptsym currentModule (path, name))
in (FSharp_Format.text _125_318))
in (let _125_322 = (let _125_321 = (FSharp_Format.text "=")
in (let _125_320 = (let _125_319 = (doc_of_pattern currentModule p)
in (_125_319)::[])
in (_125_321)::_125_320))
in (_125_323)::_125_322))
in (FSharp_Format.reduce1 _125_324))
end))
in (let _125_327 = (let _125_326 = (FSharp_Format.text "; ")
in (let _125_325 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _125_326 _125_325)))
in (FSharp_Format.cbrackets _125_327)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_329 = (let _125_328 = (as_standard_constructor ctor)
in (FStar_Option.get _125_328))
in (Prims.snd _125_329))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_331 = (let _125_330 = (as_standard_constructor ctor)
in (FStar_Option.get _125_330))
in (Prims.snd _125_331))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _125_337 = (let _125_336 = (doc_of_pattern currentModule x)
in (let _125_335 = (let _125_334 = (FSharp_Format.text "::")
in (let _125_333 = (let _125_332 = (doc_of_pattern currentModule xs)
in (_125_332)::[])
in (_125_334)::_125_333))
in (_125_336)::_125_335))
in (FSharp_Format.reduce _125_337))
end
| (_60_432, FStar_Extraction_ML_Syntax.MLP_Tuple (_60_434)::[]) -> begin
(let _125_342 = (let _125_341 = (FSharp_Format.text name)
in (let _125_340 = (let _125_339 = (let _125_338 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _125_338))
in (_125_339)::[])
in (_125_341)::_125_340))
in (FSharp_Format.reduce1 _125_342))
end
| _60_439 -> begin
(let _125_349 = (let _125_348 = (FSharp_Format.text name)
in (let _125_347 = (let _125_346 = (let _125_345 = (let _125_344 = (FSharp_Format.text ", ")
in (let _125_343 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _125_344 _125_343)))
in (FSharp_Format.parens _125_345))
in (_125_346)::[])
in (_125_348)::_125_347))
in (FSharp_Format.reduce1 _125_349))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _125_351 = (let _125_350 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_350 ps))
in (FSharp_Format.parens _125_351)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _125_352 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _125_352 ps))))
end))
and doc_of_branch = (fun currentModule _60_452 -> (match (_60_452) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _125_358 = (let _125_357 = (FSharp_Format.text "|")
in (let _125_356 = (let _125_355 = (doc_of_pattern currentModule p)
in (_125_355)::[])
in (_125_357)::_125_356))
in (FSharp_Format.reduce1 _125_358))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _125_364 = (let _125_363 = (FSharp_Format.text "|")
in (let _125_362 = (let _125_361 = (doc_of_pattern currentModule p)
in (let _125_360 = (let _125_359 = (FSharp_Format.text "when")
in (_125_359)::(c)::[])
in (_125_361)::_125_360))
in (_125_363)::_125_362))
in (FSharp_Format.reduce1 _125_364)))
end)
in (let _125_375 = (let _125_374 = (let _125_369 = (let _125_368 = (let _125_367 = (FSharp_Format.text "->")
in (let _125_366 = (let _125_365 = (FSharp_Format.text "begin")
in (_125_365)::[])
in (_125_367)::_125_366))
in (case)::_125_368)
in (FSharp_Format.reduce1 _125_369))
in (let _125_373 = (let _125_372 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_371 = (let _125_370 = (FSharp_Format.text "end")
in (_125_370)::[])
in (_125_372)::_125_371))
in (_125_374)::_125_373))
in (FSharp_Format.combine FSharp_Format.hardline _125_375)))
end))
and doc_of_lets = (fun currentModule _60_462 -> (match (_60_462) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun _60_469 -> (match (_60_469) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _60_466; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (FStar_List.map (fun _60_475 -> (match (_60_475) with
| (x, _60_474) -> begin
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
in (let _125_382 = (let _125_381 = (FSharp_Format.text ":")
in (_125_381)::(ty)::[])
in (FSharp_Format.reduce1 _125_382)))
end)
end
| false -> begin
(FSharp_Format.text "")
end)
in (let _125_389 = (let _125_388 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _125_387 = (let _125_386 = (FSharp_Format.reduce1 ids)
in (let _125_385 = (let _125_384 = (let _125_383 = (FSharp_Format.text "=")
in (_125_383)::(e)::[])
in (ty_annot)::_125_384)
in (_125_386)::_125_385))
in (_125_388)::_125_387))
in (FSharp_Format.reduce1 _125_389))))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _125_393 = (let _125_392 = (FSharp_Format.text "let")
in (let _125_391 = (let _125_390 = (FSharp_Format.text "rec")
in (_125_390)::[])
in (_125_392)::_125_391))
in (FSharp_Format.reduce1 _125_393))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _125_397 = (let _125_396 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_125_396)::(doc)::[])
in (FSharp_Format.reduce1 _125_397))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun currentModule decls -> (let for1 = (fun _60_504 -> (match (_60_504) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _60_509 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _125_406 = (let _125_405 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_405 doc))
in (FSharp_Format.parens _125_406)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _60_522 -> (match (_60_522) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_413 = (let _125_412 = (let _125_411 = (FSharp_Format.text ":")
in (_125_411)::(ty)::[])
in (name)::_125_412)
in (FSharp_Format.reduce1 _125_413))))
end))
in (let _125_416 = (let _125_415 = (FSharp_Format.text "; ")
in (let _125_414 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _125_415 _125_414)))
in (FSharp_Format.cbrackets _125_416)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _60_530 -> (match (_60_530) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _60_533 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _125_419 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_419 tys))
in (let _125_423 = (let _125_422 = (FSharp_Format.text name)
in (let _125_421 = (let _125_420 = (FSharp_Format.text "of")
in (_125_420)::(tys)::[])
in (_125_422)::_125_421))
in (FSharp_Format.reduce1 _125_423))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _125_426 = (let _125_425 = (FSharp_Format.text "|")
in (_125_425)::(d)::[])
in (FSharp_Format.reduce1 _125_426))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _125_430 = (let _125_429 = (let _125_428 = (let _125_427 = (ptsym currentModule ([], x))
in (FSharp_Format.text _125_427))
in (_125_428)::[])
in (tparams)::_125_429)
in (FSharp_Format.reduce1 _125_430))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _125_435 = (let _125_434 = (let _125_433 = (let _125_432 = (let _125_431 = (FSharp_Format.text "=")
in (_125_431)::[])
in (doc)::_125_432)
in (FSharp_Format.reduce1 _125_433))
in (_125_434)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _125_435)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = (match (((FStar_List.length doc) > 0)) with
| true -> begin
(let _125_440 = (let _125_439 = (FSharp_Format.text "type")
in (let _125_438 = (let _125_437 = (let _125_436 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _125_436 doc))
in (_125_437)::[])
in (_125_439)::_125_438))
in (FSharp_Format.reduce1 _125_440))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _125_460 = (let _125_459 = (let _125_452 = (let _125_451 = (FSharp_Format.text "module")
in (let _125_450 = (let _125_449 = (FSharp_Format.text x)
in (let _125_448 = (let _125_447 = (FSharp_Format.text "=")
in (_125_447)::[])
in (_125_449)::_125_448))
in (_125_451)::_125_450))
in (FSharp_Format.reduce1 _125_452))
in (let _125_458 = (let _125_457 = (doc_of_sig currentModule subsig)
in (let _125_456 = (let _125_455 = (let _125_454 = (let _125_453 = (FSharp_Format.text "end")
in (_125_453)::[])
in (FSharp_Format.reduce1 _125_454))
in (_125_455)::[])
in (_125_457)::_125_456))
in (_125_459)::_125_458))
in (FSharp_Format.combine FSharp_Format.hardline _125_460))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _125_464 = (let _125_463 = (FSharp_Format.text "exception")
in (let _125_462 = (let _125_461 = (FSharp_Format.text x)
in (_125_461)::[])
in (_125_463)::_125_462))
in (FSharp_Format.reduce1 _125_464))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _125_466 = (let _125_465 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_465 args))
in (FSharp_Format.parens _125_466))
in (let _125_472 = (let _125_471 = (FSharp_Format.text "exception")
in (let _125_470 = (let _125_469 = (FSharp_Format.text x)
in (let _125_468 = (let _125_467 = (FSharp_Format.text "of")
in (_125_467)::(args)::[])
in (_125_469)::_125_468))
in (_125_471)::_125_470))
in (FSharp_Format.reduce1 _125_472))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_60_564, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_478 = (let _125_477 = (FSharp_Format.text "val")
in (let _125_476 = (let _125_475 = (FSharp_Format.text x)
in (let _125_474 = (let _125_473 = (FSharp_Format.text ": ")
in (_125_473)::(ty)::[])
in (_125_475)::_125_474))
in (_125_477)::_125_476))
in (FSharp_Format.reduce1 _125_478)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _125_489 = (let _125_488 = (FSharp_Format.text "exception")
in (let _125_487 = (let _125_486 = (FSharp_Format.text x)
in (_125_486)::[])
in (_125_488)::_125_487))
in (FSharp_Format.reduce1 _125_489))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _125_491 = (let _125_490 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_490 args))
in (FSharp_Format.parens _125_491))
in (let _125_497 = (let _125_496 = (FSharp_Format.text "exception")
in (let _125_495 = (let _125_494 = (FSharp_Format.text x)
in (let _125_493 = (let _125_492 = (FSharp_Format.text "of")
in (_125_492)::(args)::[])
in (_125_494)::_125_493))
in (_125_496)::_125_495))
in (FSharp_Format.reduce1 _125_497))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _125_505 = (let _125_504 = (FSharp_Format.text "let")
in (let _125_503 = (let _125_502 = (FSharp_Format.text "_")
in (let _125_501 = (let _125_500 = (FSharp_Format.text "=")
in (let _125_499 = (let _125_498 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_125_498)::[])
in (_125_500)::_125_499))
in (_125_502)::_125_501))
in (_125_504)::_125_503))
in (FSharp_Format.reduce1 _125_505))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _60_603 -> (match (_60_603) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _60_610 -> (match (_60_610) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _125_524 = (let _125_523 = (FSharp_Format.text "module")
in (let _125_522 = (let _125_521 = (FSharp_Format.text x)
in (let _125_520 = (let _125_519 = (FSharp_Format.text ":")
in (let _125_518 = (let _125_517 = (FSharp_Format.text "sig")
in (_125_517)::[])
in (_125_519)::_125_518))
in (_125_521)::_125_520))
in (_125_523)::_125_522))
in (FSharp_Format.reduce1 _125_524))
in (let tail = (let _125_526 = (let _125_525 = (FSharp_Format.text "end")
in (_125_525)::[])
in (FSharp_Format.reduce1 _125_526))
in (let doc = (FStar_Option.map (fun _60_616 -> (match (_60_616) with
| (s, _60_615) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _125_536 = (let _125_535 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _125_534 = (let _125_533 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _125_532 = (let _125_531 = (FSharp_Format.reduce sub)
in (let _125_530 = (let _125_529 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_125_529)::[])
in (_125_531)::_125_530))
in (_125_533)::_125_532))
in (_125_535)::_125_534))
in (FSharp_Format.reduce _125_536)))))))
end))
and for1_mod = (fun istop _60_629 -> (match (_60_629) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _125_549 = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_541 = (FSharp_Format.text "module")
in (let _125_540 = (let _125_539 = (FSharp_Format.text x)
in (_125_539)::[])
in (_125_541)::_125_540))
end
| false -> begin
(match ((not (istop))) with
| true -> begin
(let _125_548 = (FSharp_Format.text "module")
in (let _125_547 = (let _125_546 = (FSharp_Format.text x)
in (let _125_545 = (let _125_544 = (FSharp_Format.text "=")
in (let _125_543 = (let _125_542 = (FSharp_Format.text "struct")
in (_125_542)::[])
in (_125_544)::_125_543))
in (_125_546)::_125_545))
in (_125_548)::_125_547))
end
| false -> begin
[]
end)
end)
in (FSharp_Format.reduce1 _125_549))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _125_551 = (let _125_550 = (FSharp_Format.text "end")
in (_125_550)::[])
in (FSharp_Format.reduce1 _125_551))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (FStar_Option.map (fun _60_635 -> (match (_60_635) with
| (_60_633, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_555 = (let _125_554 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _125_554 FSharp_Format.hardline))
in (_125_555)::[])
end
| false -> begin
[]
end)
in (let _125_567 = (let _125_566 = (let _125_565 = (let _125_564 = (let _125_563 = (FSharp_Format.text "open Prims")
in (let _125_562 = (let _125_561 = (let _125_560 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _125_559 = (let _125_558 = (FSharp_Format.reduce sub)
in (let _125_557 = (let _125_556 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_125_556)::[])
in (_125_558)::_125_557))
in (_125_560)::_125_559))
in (FSharp_Format.hardline)::_125_561)
in (_125_563)::_125_562))
in (FSharp_Format.hardline)::_125_564)
in (head)::_125_565)
in (FStar_List.append prefix _125_566))
in (FStar_All.pipe_left FSharp_Format.reduce _125_567))))))))
end))
in (let docs = (FStar_List.map (fun _60_647 -> (match (_60_647) with
| (x, s, m) -> begin
(let _125_569 = (for1_mod true (x, s, m))
in (x, _125_569))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _125_576 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _125_576 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _125_581 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _125_581 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

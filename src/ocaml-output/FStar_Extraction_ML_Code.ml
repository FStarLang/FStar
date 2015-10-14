
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
| FStar_Extraction_ML_Syntax.MLTY_App (t1, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _125_126 = (let _125_125 = (let _125_124 = (let _125_123 = (let _125_122 = (FSharp_Format.text " ")
in (_125_122)::(d1)::[])
in (d2)::_125_123)
in (FSharp_Format.reduce1 _125_124))
in (FSharp_Format.hbox _125_125))
in (maybe_paren outer t_prio_fun _125_126))))
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
(let _125_151 = (let _125_150 = (let _125_149 = (FSharp_Format.text "Prims.checked_cast")
in (_125_149)::(doc)::[])
in (FSharp_Format.reduce _125_150))
in (FSharp_Format.parens _125_151))
end
| false -> begin
(let _125_154 = (let _125_153 = (let _125_152 = (FSharp_Format.text "Obj.magic ")
in (_125_152)::(doc)::[])
in (FSharp_Format.reduce _125_153))
in (FSharp_Format.parens _125_154))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _125_158 = (let _125_157 = (let _125_156 = (FSharp_Format.text ";")
in (_125_156)::(FSharp_Format.hardline)::[])
in (d)::_125_157)
in (FSharp_Format.reduce _125_158))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _125_159 = (string_of_mlconstant c)
in (FSharp_Format.text _125_159))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _60_238) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _125_160 = (ptsym currentModule path)
in (FSharp_Format.text _125_160))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _60_250 -> (match (_60_250) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_167 = (let _125_166 = (let _125_163 = (ptsym currentModule (path, name))
in (FSharp_Format.text _125_163))
in (let _125_165 = (let _125_164 = (FSharp_Format.text "=")
in (_125_164)::(doc)::[])
in (_125_166)::_125_165))
in (FSharp_Format.reduce1 _125_167)))
end))
in (let _125_170 = (let _125_169 = (FSharp_Format.text "; ")
in (let _125_168 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _125_169 _125_168)))
in (FSharp_Format.cbrackets _125_170)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_172 = (let _125_171 = (as_standard_constructor ctor)
in (FStar_Option.get _125_171))
in (Prims.snd _125_172))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_174 = (let _125_173 = (as_standard_constructor ctor)
in (FStar_Option.get _125_173))
in (Prims.snd _125_174))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _125_178 = (let _125_177 = (FSharp_Format.parens x)
in (let _125_176 = (let _125_175 = (FSharp_Format.text "::")
in (_125_175)::(xs)::[])
in (_125_177)::_125_176))
in (FSharp_Format.reduce _125_178))
end
| (_60_269, _60_271) -> begin
(let _125_184 = (let _125_183 = (FSharp_Format.text name)
in (let _125_182 = (let _125_181 = (let _125_180 = (let _125_179 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_179 args))
in (FSharp_Format.parens _125_180))
in (_125_181)::[])
in (_125_183)::_125_182))
in (FSharp_Format.reduce1 _125_184))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _125_186 = (let _125_185 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_185 docs))
in (FSharp_Format.parens _125_186))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _125_192 = (let _125_191 = (let _125_190 = (let _125_189 = (let _125_188 = (let _125_187 = (FSharp_Format.text "in")
in (_125_187)::(body)::[])
in (FSharp_Format.reduce1 _125_188))
in (_125_189)::[])
in (doc)::_125_190)
in (FSharp_Format.combine FSharp_Format.hardline _125_191))
in (FSharp_Format.parens _125_192))))
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
| _60_321 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _125_193 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _125_193))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_198 = (let _125_197 = (let _125_196 = (FSharp_Format.text ".")
in (let _125_195 = (let _125_194 = (FSharp_Format.text (Prims.snd f))
in (_125_194)::[])
in (_125_196)::_125_195))
in (e)::_125_197)
in (FSharp_Format.reduce _125_198))
end
| false -> begin
(let _125_204 = (let _125_203 = (let _125_202 = (FSharp_Format.text ".")
in (let _125_201 = (let _125_200 = (let _125_199 = (ptsym currentModule f)
in (FSharp_Format.text _125_199))
in (_125_200)::[])
in (_125_202)::_125_201))
in (e)::_125_203)
in (FSharp_Format.reduce _125_204))
end)
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_220 = (let _125_219 = (FSharp_Format.text "(")
in (let _125_218 = (let _125_217 = (FSharp_Format.text x)
in (let _125_216 = (let _125_215 = (match (xt) with
| Some (xxt) -> begin
(let _125_212 = (let _125_211 = (FSharp_Format.text " : ")
in (let _125_210 = (let _125_209 = (doc_of_mltype currentModule outer xxt)
in (_125_209)::[])
in (_125_211)::_125_210))
in (FSharp_Format.reduce1 _125_212))
end
| _60_340 -> begin
(FSharp_Format.text "")
end)
in (let _125_214 = (let _125_213 = (FSharp_Format.text ")")
in (_125_213)::[])
in (_125_215)::_125_214))
in (_125_217)::_125_216))
in (_125_219)::_125_218))
in (FSharp_Format.reduce1 _125_220))
end
| false -> begin
(FSharp_Format.text x)
end))
in (let ids = (FStar_List.map (fun _60_346 -> (match (_60_346) with
| ((x, _60_343), xt) -> begin
(bvar_annot x xt)
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _125_227 = (let _125_226 = (FSharp_Format.text "fun")
in (let _125_225 = (let _125_224 = (FSharp_Format.reduce1 ids)
in (let _125_223 = (let _125_222 = (FSharp_Format.text "->")
in (_125_222)::(body)::[])
in (_125_224)::_125_223))
in (_125_226)::_125_225))
in (FSharp_Format.reduce1 _125_227))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _125_240 = (let _125_239 = (let _125_234 = (let _125_233 = (FSharp_Format.text "if")
in (let _125_232 = (let _125_231 = (let _125_230 = (FSharp_Format.text "then")
in (let _125_229 = (let _125_228 = (FSharp_Format.text "begin")
in (_125_228)::[])
in (_125_230)::_125_229))
in (cond)::_125_231)
in (_125_233)::_125_232))
in (FSharp_Format.reduce1 _125_234))
in (let _125_238 = (let _125_237 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _125_236 = (let _125_235 = (FSharp_Format.text "end")
in (_125_235)::[])
in (_125_237)::_125_236))
in (_125_239)::_125_238))
in (FSharp_Format.combine FSharp_Format.hardline _125_240))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _125_263 = (let _125_262 = (let _125_247 = (let _125_246 = (FSharp_Format.text "if")
in (let _125_245 = (let _125_244 = (let _125_243 = (FSharp_Format.text "then")
in (let _125_242 = (let _125_241 = (FSharp_Format.text "begin")
in (_125_241)::[])
in (_125_243)::_125_242))
in (cond)::_125_244)
in (_125_246)::_125_245))
in (FSharp_Format.reduce1 _125_247))
in (let _125_261 = (let _125_260 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _125_259 = (let _125_258 = (let _125_253 = (let _125_252 = (FSharp_Format.text "end")
in (let _125_251 = (let _125_250 = (FSharp_Format.text "else")
in (let _125_249 = (let _125_248 = (FSharp_Format.text "begin")
in (_125_248)::[])
in (_125_250)::_125_249))
in (_125_252)::_125_251))
in (FSharp_Format.reduce1 _125_253))
in (let _125_257 = (let _125_256 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _125_255 = (let _125_254 = (FSharp_Format.text "end")
in (_125_254)::[])
in (_125_256)::_125_255))
in (_125_258)::_125_257))
in (_125_260)::_125_259))
in (_125_262)::_125_261))
in (FSharp_Format.combine FSharp_Format.hardline _125_263))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _125_270 = (let _125_269 = (let _125_268 = (FSharp_Format.text "match")
in (let _125_267 = (let _125_266 = (FSharp_Format.parens cond)
in (let _125_265 = (let _125_264 = (FSharp_Format.text "with")
in (_125_264)::[])
in (_125_266)::_125_265))
in (_125_268)::_125_267))
in (FSharp_Format.reduce1 _125_269))
in (_125_270)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _125_275 = (let _125_274 = (FSharp_Format.text "raise")
in (let _125_273 = (let _125_272 = (let _125_271 = (ptctor currentModule exn)
in (FSharp_Format.text _125_271))
in (_125_272)::[])
in (_125_274)::_125_273))
in (FSharp_Format.reduce1 _125_275))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _125_284 = (let _125_283 = (FSharp_Format.text "raise")
in (let _125_282 = (let _125_281 = (let _125_276 = (ptctor currentModule exn)
in (FSharp_Format.text _125_276))
in (let _125_280 = (let _125_279 = (let _125_278 = (let _125_277 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_277 args))
in (FSharp_Format.parens _125_278))
in (_125_279)::[])
in (_125_281)::_125_280))
in (_125_283)::_125_282))
in (FSharp_Format.reduce1 _125_284)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _125_301 = (let _125_300 = (let _125_288 = (let _125_287 = (FSharp_Format.text "try")
in (let _125_286 = (let _125_285 = (FSharp_Format.text "begin")
in (_125_285)::[])
in (_125_287)::_125_286))
in (FSharp_Format.reduce1 _125_288))
in (let _125_299 = (let _125_298 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_297 = (let _125_296 = (let _125_292 = (let _125_291 = (FSharp_Format.text "end")
in (let _125_290 = (let _125_289 = (FSharp_Format.text "with")
in (_125_289)::[])
in (_125_291)::_125_290))
in (FSharp_Format.reduce1 _125_292))
in (let _125_295 = (let _125_294 = (let _125_293 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _125_293))
in (_125_294)::[])
in (_125_296)::_125_295))
in (_125_298)::_125_297))
in (_125_300)::_125_299))
in (FSharp_Format.combine FSharp_Format.hardline _125_301))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _60_394 = (let _125_306 = (as_bin_op p)
in (FStar_Option.get _125_306))
in (match (_60_394) with
| (_60_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _125_309 = (let _125_308 = (let _125_307 = (FSharp_Format.text txt)
in (_125_307)::(e2)::[])
in (e1)::_125_308)
in (FSharp_Format.reduce1 _125_309))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _60_404 = (let _125_313 = (as_uni_op p)
in (FStar_Option.get _125_313))
in (match (_60_404) with
| (_60_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _125_317 = (let _125_316 = (FSharp_Format.text txt)
in (let _125_315 = (let _125_314 = (FSharp_Format.parens e1)
in (_125_314)::[])
in (_125_316)::_125_315))
in (FSharp_Format.reduce1 _125_317))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _125_320 = (string_of_mlconstant c)
in (FSharp_Format.text _125_320))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _60_421 -> (match (_60_421) with
| (name, p) -> begin
(let _125_329 = (let _125_328 = (let _125_323 = (ptsym currentModule (path, name))
in (FSharp_Format.text _125_323))
in (let _125_327 = (let _125_326 = (FSharp_Format.text "=")
in (let _125_325 = (let _125_324 = (doc_of_pattern currentModule p)
in (_125_324)::[])
in (_125_326)::_125_325))
in (_125_328)::_125_327))
in (FSharp_Format.reduce1 _125_329))
end))
in (let _125_332 = (let _125_331 = (FSharp_Format.text "; ")
in (let _125_330 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _125_331 _125_330)))
in (FSharp_Format.cbrackets _125_332)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_334 = (let _125_333 = (as_standard_constructor ctor)
in (FStar_Option.get _125_333))
in (Prims.snd _125_334))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_336 = (let _125_335 = (as_standard_constructor ctor)
in (FStar_Option.get _125_335))
in (Prims.snd _125_336))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _125_342 = (let _125_341 = (doc_of_pattern currentModule x)
in (let _125_340 = (let _125_339 = (FSharp_Format.text "::")
in (let _125_338 = (let _125_337 = (doc_of_pattern currentModule xs)
in (_125_337)::[])
in (_125_339)::_125_338))
in (_125_341)::_125_340))
in (FSharp_Format.reduce _125_342))
end
| (_60_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_60_440)::[]) -> begin
(let _125_347 = (let _125_346 = (FSharp_Format.text name)
in (let _125_345 = (let _125_344 = (let _125_343 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _125_343))
in (_125_344)::[])
in (_125_346)::_125_345))
in (FSharp_Format.reduce1 _125_347))
end
| _60_445 -> begin
(let _125_354 = (let _125_353 = (FSharp_Format.text name)
in (let _125_352 = (let _125_351 = (let _125_350 = (let _125_349 = (FSharp_Format.text ", ")
in (let _125_348 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _125_349 _125_348)))
in (FSharp_Format.parens _125_350))
in (_125_351)::[])
in (_125_353)::_125_352))
in (FSharp_Format.reduce1 _125_354))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _125_356 = (let _125_355 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_355 ps))
in (FSharp_Format.parens _125_356)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _125_357 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _125_357 ps))))
end))
and doc_of_branch = (fun currentModule _60_458 -> (match (_60_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _125_363 = (let _125_362 = (FSharp_Format.text "|")
in (let _125_361 = (let _125_360 = (doc_of_pattern currentModule p)
in (_125_360)::[])
in (_125_362)::_125_361))
in (FSharp_Format.reduce1 _125_363))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _125_369 = (let _125_368 = (FSharp_Format.text "|")
in (let _125_367 = (let _125_366 = (doc_of_pattern currentModule p)
in (let _125_365 = (let _125_364 = (FSharp_Format.text "when")
in (_125_364)::(c)::[])
in (_125_366)::_125_365))
in (_125_368)::_125_367))
in (FSharp_Format.reduce1 _125_369)))
end)
in (let _125_380 = (let _125_379 = (let _125_374 = (let _125_373 = (let _125_372 = (FSharp_Format.text "->")
in (let _125_371 = (let _125_370 = (FSharp_Format.text "begin")
in (_125_370)::[])
in (_125_372)::_125_371))
in (case)::_125_373)
in (FSharp_Format.reduce1 _125_374))
in (let _125_378 = (let _125_377 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_376 = (let _125_375 = (FSharp_Format.text "end")
in (_125_375)::[])
in (_125_377)::_125_376))
in (_125_379)::_125_378))
in (FSharp_Format.combine FSharp_Format.hardline _125_380)))
end))
and doc_of_lets = (fun currentModule _60_468 -> (match (_60_468) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun _60_475 -> (match (_60_475) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _60_472; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (FStar_List.map (fun _60_481 -> (match (_60_481) with
| (x, _60_480) -> begin
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
in (let _125_387 = (let _125_386 = (FSharp_Format.text ":")
in (_125_386)::(ty)::[])
in (FSharp_Format.reduce1 _125_387)))
end)
end
| false -> begin
(FSharp_Format.text "")
end)
in (let _125_394 = (let _125_393 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _125_392 = (let _125_391 = (FSharp_Format.reduce1 ids)
in (let _125_390 = (let _125_389 = (let _125_388 = (FSharp_Format.text "=")
in (_125_388)::(e)::[])
in (ty_annot)::_125_389)
in (_125_391)::_125_390))
in (_125_393)::_125_392))
in (FSharp_Format.reduce1 _125_394))))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _125_398 = (let _125_397 = (FSharp_Format.text "let")
in (let _125_396 = (let _125_395 = (FSharp_Format.text "rec")
in (_125_395)::[])
in (_125_397)::_125_396))
in (FSharp_Format.reduce1 _125_398))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _125_402 = (let _125_401 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_125_401)::(doc)::[])
in (FSharp_Format.reduce1 _125_402))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun currentModule decls -> (let for1 = (fun _60_510 -> (match (_60_510) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _60_515 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _125_411 = (let _125_410 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_410 doc))
in (FSharp_Format.parens _125_411)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _60_528 -> (match (_60_528) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_418 = (let _125_417 = (let _125_416 = (FSharp_Format.text ":")
in (_125_416)::(ty)::[])
in (name)::_125_417)
in (FSharp_Format.reduce1 _125_418))))
end))
in (let _125_421 = (let _125_420 = (FSharp_Format.text "; ")
in (let _125_419 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _125_420 _125_419)))
in (FSharp_Format.cbrackets _125_421)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _60_536 -> (match (_60_536) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _60_539 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _125_424 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_424 tys))
in (let _125_428 = (let _125_427 = (FSharp_Format.text name)
in (let _125_426 = (let _125_425 = (FSharp_Format.text "of")
in (_125_425)::(tys)::[])
in (_125_427)::_125_426))
in (FSharp_Format.reduce1 _125_428))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _125_431 = (let _125_430 = (FSharp_Format.text "|")
in (_125_430)::(d)::[])
in (FSharp_Format.reduce1 _125_431))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _125_435 = (let _125_434 = (let _125_433 = (let _125_432 = (ptsym currentModule ([], x))
in (FSharp_Format.text _125_432))
in (_125_433)::[])
in (tparams)::_125_434)
in (FSharp_Format.reduce1 _125_435))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _125_440 = (let _125_439 = (let _125_438 = (let _125_437 = (let _125_436 = (FSharp_Format.text "=")
in (_125_436)::[])
in (doc)::_125_437)
in (FSharp_Format.reduce1 _125_438))
in (_125_439)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _125_440)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = (match (((FStar_List.length doc) > 0)) with
| true -> begin
(let _125_445 = (let _125_444 = (FSharp_Format.text "type")
in (let _125_443 = (let _125_442 = (let _125_441 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _125_441 doc))
in (_125_442)::[])
in (_125_444)::_125_443))
in (FSharp_Format.reduce1 _125_445))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _125_465 = (let _125_464 = (let _125_457 = (let _125_456 = (FSharp_Format.text "module")
in (let _125_455 = (let _125_454 = (FSharp_Format.text x)
in (let _125_453 = (let _125_452 = (FSharp_Format.text "=")
in (_125_452)::[])
in (_125_454)::_125_453))
in (_125_456)::_125_455))
in (FSharp_Format.reduce1 _125_457))
in (let _125_463 = (let _125_462 = (doc_of_sig currentModule subsig)
in (let _125_461 = (let _125_460 = (let _125_459 = (let _125_458 = (FSharp_Format.text "end")
in (_125_458)::[])
in (FSharp_Format.reduce1 _125_459))
in (_125_460)::[])
in (_125_462)::_125_461))
in (_125_464)::_125_463))
in (FSharp_Format.combine FSharp_Format.hardline _125_465))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _125_469 = (let _125_468 = (FSharp_Format.text "exception")
in (let _125_467 = (let _125_466 = (FSharp_Format.text x)
in (_125_466)::[])
in (_125_468)::_125_467))
in (FSharp_Format.reduce1 _125_469))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _125_471 = (let _125_470 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_470 args))
in (FSharp_Format.parens _125_471))
in (let _125_477 = (let _125_476 = (FSharp_Format.text "exception")
in (let _125_475 = (let _125_474 = (FSharp_Format.text x)
in (let _125_473 = (let _125_472 = (FSharp_Format.text "of")
in (_125_472)::(args)::[])
in (_125_474)::_125_473))
in (_125_476)::_125_475))
in (FSharp_Format.reduce1 _125_477))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_60_570, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_483 = (let _125_482 = (FSharp_Format.text "val")
in (let _125_481 = (let _125_480 = (FSharp_Format.text x)
in (let _125_479 = (let _125_478 = (FSharp_Format.text ": ")
in (_125_478)::(ty)::[])
in (_125_480)::_125_479))
in (_125_482)::_125_481))
in (FSharp_Format.reduce1 _125_483)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _125_494 = (let _125_493 = (FSharp_Format.text "exception")
in (let _125_492 = (let _125_491 = (FSharp_Format.text x)
in (_125_491)::[])
in (_125_493)::_125_492))
in (FSharp_Format.reduce1 _125_494))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _125_496 = (let _125_495 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_495 args))
in (FSharp_Format.parens _125_496))
in (let _125_502 = (let _125_501 = (FSharp_Format.text "exception")
in (let _125_500 = (let _125_499 = (FSharp_Format.text x)
in (let _125_498 = (let _125_497 = (FSharp_Format.text "of")
in (_125_497)::(args)::[])
in (_125_499)::_125_498))
in (_125_501)::_125_500))
in (FSharp_Format.reduce1 _125_502))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _125_510 = (let _125_509 = (FSharp_Format.text "let")
in (let _125_508 = (let _125_507 = (FSharp_Format.text "_")
in (let _125_506 = (let _125_505 = (FSharp_Format.text "=")
in (let _125_504 = (let _125_503 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_125_503)::[])
in (_125_505)::_125_504))
in (_125_507)::_125_506))
in (_125_509)::_125_508))
in (FSharp_Format.reduce1 _125_510))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _60_609 -> (match (_60_609) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _60_616 -> (match (_60_616) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _125_529 = (let _125_528 = (FSharp_Format.text "module")
in (let _125_527 = (let _125_526 = (FSharp_Format.text x)
in (let _125_525 = (let _125_524 = (FSharp_Format.text ":")
in (let _125_523 = (let _125_522 = (FSharp_Format.text "sig")
in (_125_522)::[])
in (_125_524)::_125_523))
in (_125_526)::_125_525))
in (_125_528)::_125_527))
in (FSharp_Format.reduce1 _125_529))
in (let tail = (let _125_531 = (let _125_530 = (FSharp_Format.text "end")
in (_125_530)::[])
in (FSharp_Format.reduce1 _125_531))
in (let doc = (FStar_Option.map (fun _60_622 -> (match (_60_622) with
| (s, _60_621) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _125_541 = (let _125_540 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _125_539 = (let _125_538 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _125_537 = (let _125_536 = (FSharp_Format.reduce sub)
in (let _125_535 = (let _125_534 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_125_534)::[])
in (_125_536)::_125_535))
in (_125_538)::_125_537))
in (_125_540)::_125_539))
in (FSharp_Format.reduce _125_541)))))))
end))
and for1_mod = (fun istop _60_635 -> (match (_60_635) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _125_554 = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_546 = (FSharp_Format.text "module")
in (let _125_545 = (let _125_544 = (FSharp_Format.text x)
in (_125_544)::[])
in (_125_546)::_125_545))
end
| false -> begin
(match ((not (istop))) with
| true -> begin
(let _125_553 = (FSharp_Format.text "module")
in (let _125_552 = (let _125_551 = (FSharp_Format.text x)
in (let _125_550 = (let _125_549 = (FSharp_Format.text "=")
in (let _125_548 = (let _125_547 = (FSharp_Format.text "struct")
in (_125_547)::[])
in (_125_549)::_125_548))
in (_125_551)::_125_550))
in (_125_553)::_125_552))
end
| false -> begin
[]
end)
end)
in (FSharp_Format.reduce1 _125_554))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _125_556 = (let _125_555 = (FSharp_Format.text "end")
in (_125_555)::[])
in (FSharp_Format.reduce1 _125_556))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (FStar_Option.map (fun _60_641 -> (match (_60_641) with
| (_60_639, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_560 = (let _125_559 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _125_559 FSharp_Format.hardline))
in (_125_560)::[])
end
| false -> begin
[]
end)
in (let _125_572 = (let _125_571 = (let _125_570 = (let _125_569 = (let _125_568 = (FSharp_Format.text "open Prims")
in (let _125_567 = (let _125_566 = (let _125_565 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _125_564 = (let _125_563 = (FSharp_Format.reduce sub)
in (let _125_562 = (let _125_561 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_125_561)::[])
in (_125_563)::_125_562))
in (_125_565)::_125_564))
in (FSharp_Format.hardline)::_125_566)
in (_125_568)::_125_567))
in (FSharp_Format.hardline)::_125_569)
in (head)::_125_570)
in (FStar_List.append prefix _125_571))
in (FStar_All.pipe_left FSharp_Format.reduce _125_572))))))))
end))
in (let docs = (FStar_List.map (fun _60_653 -> (match (_60_653) with
| (x, s, m) -> begin
(let _125_574 = (for1_mod true (x, s, m))
in (x, _125_574))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _125_581 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _125_581 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _125_586 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _125_586 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))






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
in if (ns' = currentModule) then begin
[]
end else begin
(let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
in (let ns_len = (FStar_List.length ns)
in (let found = (FStar_Util.find_map cg_libs (fun cg_path -> (let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(let _60_31 = (FStar_Util.first_N cg_len ns)
in (match (_60_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _126_31 = (let _126_30 = (let _126_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_126_29)::[])
in (FStar_List.append pfx _126_30))
in Some (_126_31))
end else begin
None
end
end))
end else begin
None
end)))
in (match (found) with
| None -> begin
(ns')::[]
end
| Some (x) -> begin
x
end))))
end))

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

let ptsym_of_symbol = (fun s -> if ((let _126_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _126_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

let ptsym = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(let _60_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_50) with
| (p, s) -> begin
(let _126_46 = (let _126_45 = (let _126_44 = (ptsym_of_symbol s)
in (_126_44)::[])
in (FStar_List.append p _126_45))
in (FStar_String.concat "." _126_46))
end))
end)

let ptctor = (fun currentModule mlp -> (let _60_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_55) with
| (p, s) -> begin
(let s = if ((let _126_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _126_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

let prim_types = []

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ns -> (ns = ("Prims")::[]))

let as_bin_op = (fun _60_60 -> (match (_60_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _60_66 -> (match (_60_66) with
| (y, _60_63, _60_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

let is_bin_op = (fun p -> ((as_bin_op p) <> None))

let as_uni_op = (fun _60_70 -> (match (_60_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _60_74 -> (match (_60_74) with
| (y, _60_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

let is_uni_op = (fun p -> ((as_uni_op p) <> None))

let as_standard_type = (fun _60_78 -> (match (_60_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _60_82 -> (match (_60_82) with
| (y, _60_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

let is_standard_type = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun _60_86 -> (match (_60_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _60_90 -> (match (_60_90) with
| (y, _60_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
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
in if (noparens inner outer side) then begin
doc
end else begin
(FSharp_Format.parens doc)
end)
end))

let ocaml_u8_codepoint = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

let encode_char = (fun c -> if ((FStar_Util.int_of_char c) > 127) then begin
(let bytes = (FStar_Util.string_of_char c)
in (let bytes = (FStar_Util.unicode_of_string bytes)
in (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)))
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
end)

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
| FStar_Extraction_ML_Syntax.MLC_Int (s) -> begin
if (FStar_ST.read FStar_Options.use_native_int) then begin
s
end else begin
(Prims.strcat (Prims.strcat "(Prims.parse_int \"" s) "\")")
end
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
(let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
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
| _60_198 -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _126_110 = (let _126_109 = (let _126_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_108 args))
in (FSharp_Format.hbox _126_109))
in (FSharp_Format.parens _126_110)))
end)
in (let name = if (is_standard_type name) then begin
(let _126_112 = (let _126_111 = (as_standard_type name)
in (FStar_Option.get _126_111))
in (Prims.snd _126_112))
end else begin
(ptsym currentModule name)
end
in (let _126_116 = (let _126_115 = (let _126_114 = (let _126_113 = (FSharp_Format.text name)
in (_126_113)::[])
in (args)::_126_114)
in (FSharp_Format.reduce1 _126_115))
in (FSharp_Format.hbox _126_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _60_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _126_121 = (let _126_120 = (let _126_119 = (let _126_118 = (let _126_117 = (FSharp_Format.text " -> ")
in (_126_117)::(d2)::[])
in (d1)::_126_118)
in (FSharp_Format.reduce1 _126_119))
in (FSharp_Format.hbox _126_120))
in (maybe_paren outer t_prio_fun _126_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FSharp_Format.text "obj")
end else begin
(FSharp_Format.text "Obj.t")
end
end))
and doc_of_mltype = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _126_146 = (let _126_145 = (let _126_144 = (FSharp_Format.text "Prims.checked_cast")
in (_126_144)::(doc)::[])
in (FSharp_Format.reduce _126_145))
in (FSharp_Format.parens _126_146))
end else begin
(let _126_149 = (let _126_148 = (let _126_147 = (FSharp_Format.text "Obj.magic ")
in (_126_147)::(doc)::[])
in (FSharp_Format.reduce _126_148))
in (FSharp_Format.parens _126_149))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _126_153 = (let _126_152 = (let _126_151 = (FSharp_Format.text ";")
in (_126_151)::(FSharp_Format.hardline)::[])
in (d)::_126_152)
in (FSharp_Format.reduce _126_153))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _126_154 = (string_of_mlconstant c)
in (FSharp_Format.text _126_154))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _60_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _126_155 = (ptsym currentModule path)
in (FSharp_Format.text _126_155))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _60_244 -> (match (_60_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _126_162 = (let _126_161 = (let _126_158 = (ptsym currentModule (path, name))
in (FSharp_Format.text _126_158))
in (let _126_160 = (let _126_159 = (FSharp_Format.text "=")
in (_126_159)::(doc)::[])
in (_126_161)::_126_160))
in (FSharp_Format.reduce1 _126_162)))
end))
in (let _126_165 = (let _126_164 = (FSharp_Format.text "; ")
in (let _126_163 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _126_164 _126_163)))
in (FSharp_Format.cbrackets _126_165)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _126_167 = (let _126_166 = (as_standard_constructor ctor)
in (FStar_Option.get _126_166))
in (Prims.snd _126_167))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _126_169 = (let _126_168 = (as_standard_constructor ctor)
in (FStar_Option.get _126_168))
in (Prims.snd _126_169))
end else begin
(ptctor currentModule ctor)
end
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _126_173 = (let _126_172 = (FSharp_Format.parens x)
in (let _126_171 = (let _126_170 = (FSharp_Format.text "::")
in (_126_170)::(xs)::[])
in (_126_172)::_126_171))
in (FSharp_Format.reduce _126_173))
end
| (_60_263, _60_265) -> begin
(let _126_179 = (let _126_178 = (FSharp_Format.text name)
in (let _126_177 = (let _126_176 = (let _126_175 = (let _126_174 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_174 args))
in (FSharp_Format.parens _126_175))
in (_126_176)::[])
in (_126_178)::_126_177))
in (FSharp_Format.reduce1 _126_179))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _126_181 = (let _126_180 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_180 docs))
in (FSharp_Format.parens _126_181))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _126_187 = (let _126_186 = (let _126_185 = (let _126_184 = (let _126_183 = (let _126_182 = (FSharp_Format.text "in")
in (_126_182)::(body)::[])
in (FSharp_Format.reduce1 _126_183))
in (_126_184)::[])
in (doc)::_126_185)
in (FSharp_Format.combine FSharp_Format.hardline _126_186))
in (FSharp_Format.parens _126_187))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _60_291}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _60_309}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _60_321 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _126_188 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _126_188))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _126_193 = (let _126_192 = (let _126_191 = (FSharp_Format.text ".")
in (let _126_190 = (let _126_189 = (FSharp_Format.text (Prims.snd f))
in (_126_189)::[])
in (_126_191)::_126_190))
in (e)::_126_192)
in (FSharp_Format.reduce _126_193))
end else begin
(let _126_199 = (let _126_198 = (let _126_197 = (FSharp_Format.text ".")
in (let _126_196 = (let _126_195 = (let _126_194 = (ptsym currentModule f)
in (FSharp_Format.text _126_194))
in (_126_195)::[])
in (_126_197)::_126_196))
in (e)::_126_198)
in (FSharp_Format.reduce _126_199))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _126_215 = (let _126_214 = (FSharp_Format.text "(")
in (let _126_213 = (let _126_212 = (FSharp_Format.text x)
in (let _126_211 = (let _126_210 = (match (xt) with
| Some (xxt) -> begin
(let _126_207 = (let _126_206 = (FSharp_Format.text " : ")
in (let _126_205 = (let _126_204 = (doc_of_mltype currentModule outer xxt)
in (_126_204)::[])
in (_126_206)::_126_205))
in (FSharp_Format.reduce1 _126_207))
end
| _60_340 -> begin
(FSharp_Format.text "")
end)
in (let _126_209 = (let _126_208 = (FSharp_Format.text ")")
in (_126_208)::[])
in (_126_210)::_126_209))
in (_126_212)::_126_211))
in (_126_214)::_126_213))
in (FSharp_Format.reduce1 _126_215))
end else begin
(FSharp_Format.text x)
end)
in (let ids = (FStar_List.map (fun _60_346 -> (match (_60_346) with
| ((x, _60_343), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _126_222 = (let _126_221 = (FSharp_Format.text "fun")
in (let _126_220 = (let _126_219 = (FSharp_Format.reduce1 ids)
in (let _126_218 = (let _126_217 = (FSharp_Format.text "->")
in (_126_217)::(body)::[])
in (_126_219)::_126_218))
in (_126_221)::_126_220))
in (FSharp_Format.reduce1 _126_222))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _126_235 = (let _126_234 = (let _126_229 = (let _126_228 = (FSharp_Format.text "if")
in (let _126_227 = (let _126_226 = (let _126_225 = (FSharp_Format.text "then")
in (let _126_224 = (let _126_223 = (FSharp_Format.text "begin")
in (_126_223)::[])
in (_126_225)::_126_224))
in (cond)::_126_226)
in (_126_228)::_126_227))
in (FSharp_Format.reduce1 _126_229))
in (let _126_233 = (let _126_232 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _126_231 = (let _126_230 = (FSharp_Format.text "end")
in (_126_230)::[])
in (_126_232)::_126_231))
in (_126_234)::_126_233))
in (FSharp_Format.combine FSharp_Format.hardline _126_235))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _126_258 = (let _126_257 = (let _126_242 = (let _126_241 = (FSharp_Format.text "if")
in (let _126_240 = (let _126_239 = (let _126_238 = (FSharp_Format.text "then")
in (let _126_237 = (let _126_236 = (FSharp_Format.text "begin")
in (_126_236)::[])
in (_126_238)::_126_237))
in (cond)::_126_239)
in (_126_241)::_126_240))
in (FSharp_Format.reduce1 _126_242))
in (let _126_256 = (let _126_255 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _126_254 = (let _126_253 = (let _126_248 = (let _126_247 = (FSharp_Format.text "end")
in (let _126_246 = (let _126_245 = (FSharp_Format.text "else")
in (let _126_244 = (let _126_243 = (FSharp_Format.text "begin")
in (_126_243)::[])
in (_126_245)::_126_244))
in (_126_247)::_126_246))
in (FSharp_Format.reduce1 _126_248))
in (let _126_252 = (let _126_251 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _126_250 = (let _126_249 = (FSharp_Format.text "end")
in (_126_249)::[])
in (_126_251)::_126_250))
in (_126_253)::_126_252))
in (_126_255)::_126_254))
in (_126_257)::_126_256))
in (FSharp_Format.combine FSharp_Format.hardline _126_258))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _126_265 = (let _126_264 = (let _126_263 = (FSharp_Format.text "match")
in (let _126_262 = (let _126_261 = (FSharp_Format.parens cond)
in (let _126_260 = (let _126_259 = (FSharp_Format.text "with")
in (_126_259)::[])
in (_126_261)::_126_260))
in (_126_263)::_126_262))
in (FSharp_Format.reduce1 _126_264))
in (_126_265)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _126_270 = (let _126_269 = (FSharp_Format.text "raise")
in (let _126_268 = (let _126_267 = (let _126_266 = (ptctor currentModule exn)
in (FSharp_Format.text _126_266))
in (_126_267)::[])
in (_126_269)::_126_268))
in (FSharp_Format.reduce1 _126_270))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _126_279 = (let _126_278 = (FSharp_Format.text "raise")
in (let _126_277 = (let _126_276 = (let _126_271 = (ptctor currentModule exn)
in (FSharp_Format.text _126_271))
in (let _126_275 = (let _126_274 = (let _126_273 = (let _126_272 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_272 args))
in (FSharp_Format.parens _126_273))
in (_126_274)::[])
in (_126_276)::_126_275))
in (_126_278)::_126_277))
in (FSharp_Format.reduce1 _126_279)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _126_296 = (let _126_295 = (let _126_283 = (let _126_282 = (FSharp_Format.text "try")
in (let _126_281 = (let _126_280 = (FSharp_Format.text "begin")
in (_126_280)::[])
in (_126_282)::_126_281))
in (FSharp_Format.reduce1 _126_283))
in (let _126_294 = (let _126_293 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _126_292 = (let _126_291 = (let _126_287 = (let _126_286 = (FSharp_Format.text "end")
in (let _126_285 = (let _126_284 = (FSharp_Format.text "with")
in (_126_284)::[])
in (_126_286)::_126_285))
in (FSharp_Format.reduce1 _126_287))
in (let _126_290 = (let _126_289 = (let _126_288 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _126_288))
in (_126_289)::[])
in (_126_291)::_126_290))
in (_126_293)::_126_292))
in (_126_295)::_126_294))
in (FSharp_Format.combine FSharp_Format.hardline _126_296))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _60_394 = (let _126_301 = (as_bin_op p)
in (FStar_Option.get _126_301))
in (match (_60_394) with
| (_60_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _126_304 = (let _126_303 = (let _126_302 = (FSharp_Format.text txt)
in (_126_302)::(e2)::[])
in (e1)::_126_303)
in (FSharp_Format.reduce1 _126_304))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _60_404 = (let _126_308 = (as_uni_op p)
in (FStar_Option.get _126_308))
in (match (_60_404) with
| (_60_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _126_312 = (let _126_311 = (FSharp_Format.text txt)
in (let _126_310 = (let _126_309 = (FSharp_Format.parens e1)
in (_126_309)::[])
in (_126_311)::_126_310))
in (FSharp_Format.reduce1 _126_312))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _126_315 = (string_of_mlconstant c)
in (FSharp_Format.text _126_315))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _60_421 -> (match (_60_421) with
| (name, p) -> begin
(let _126_324 = (let _126_323 = (let _126_318 = (ptsym currentModule (path, name))
in (FSharp_Format.text _126_318))
in (let _126_322 = (let _126_321 = (FSharp_Format.text "=")
in (let _126_320 = (let _126_319 = (doc_of_pattern currentModule p)
in (_126_319)::[])
in (_126_321)::_126_320))
in (_126_323)::_126_322))
in (FSharp_Format.reduce1 _126_324))
end))
in (let _126_327 = (let _126_326 = (FSharp_Format.text "; ")
in (let _126_325 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _126_326 _126_325)))
in (FSharp_Format.cbrackets _126_327)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _126_329 = (let _126_328 = (as_standard_constructor ctor)
in (FStar_Option.get _126_328))
in (Prims.snd _126_329))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _126_331 = (let _126_330 = (as_standard_constructor ctor)
in (FStar_Option.get _126_330))
in (Prims.snd _126_331))
end else begin
(ptctor currentModule ctor)
end
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _126_337 = (let _126_336 = (doc_of_pattern currentModule x)
in (let _126_335 = (let _126_334 = (FSharp_Format.text "::")
in (let _126_333 = (let _126_332 = (doc_of_pattern currentModule xs)
in (_126_332)::[])
in (_126_334)::_126_333))
in (_126_336)::_126_335))
in (FSharp_Format.reduce _126_337))
end
| (_60_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_60_440)::[]) -> begin
(let _126_342 = (let _126_341 = (FSharp_Format.text name)
in (let _126_340 = (let _126_339 = (let _126_338 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _126_338))
in (_126_339)::[])
in (_126_341)::_126_340))
in (FSharp_Format.reduce1 _126_342))
end
| _60_445 -> begin
(let _126_349 = (let _126_348 = (FSharp_Format.text name)
in (let _126_347 = (let _126_346 = (let _126_345 = (let _126_344 = (FSharp_Format.text ", ")
in (let _126_343 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _126_344 _126_343)))
in (FSharp_Format.parens _126_345))
in (_126_346)::[])
in (_126_348)::_126_347))
in (FSharp_Format.reduce1 _126_349))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _126_351 = (let _126_350 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_350 ps))
in (FSharp_Format.parens _126_351)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _126_352 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _126_352 ps))))
end))
and doc_of_branch = (fun currentModule _60_458 -> (match (_60_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _126_358 = (let _126_357 = (FSharp_Format.text "|")
in (let _126_356 = (let _126_355 = (doc_of_pattern currentModule p)
in (_126_355)::[])
in (_126_357)::_126_356))
in (FSharp_Format.reduce1 _126_358))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _126_364 = (let _126_363 = (FSharp_Format.text "|")
in (let _126_362 = (let _126_361 = (doc_of_pattern currentModule p)
in (let _126_360 = (let _126_359 = (FSharp_Format.text "when")
in (_126_359)::(c)::[])
in (_126_361)::_126_360))
in (_126_363)::_126_362))
in (FSharp_Format.reduce1 _126_364)))
end)
in (let _126_375 = (let _126_374 = (let _126_369 = (let _126_368 = (let _126_367 = (FSharp_Format.text "->")
in (let _126_366 = (let _126_365 = (FSharp_Format.text "begin")
in (_126_365)::[])
in (_126_367)::_126_366))
in (case)::_126_368)
in (FSharp_Format.reduce1 _126_369))
in (let _126_373 = (let _126_372 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _126_371 = (let _126_370 = (FSharp_Format.text "end")
in (_126_370)::[])
in (_126_372)::_126_371))
in (_126_374)::_126_373))
in (FSharp_Format.combine FSharp_Format.hardline _126_375)))
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
in (let ty_annot = if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (_60_486::_60_484, _60_489) -> begin
(FSharp_Format.text "")
end
| ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _126_382 = (let _126_381 = (FSharp_Format.text ":")
in (_126_381)::(ty)::[])
in (FSharp_Format.reduce1 _126_382)))
end)
end else begin
(FSharp_Format.text "")
end
in (let _126_389 = (let _126_388 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _126_387 = (let _126_386 = (FSharp_Format.reduce1 ids)
in (let _126_385 = (let _126_384 = (let _126_383 = (FSharp_Format.text "=")
in (_126_383)::(e)::[])
in (ty_annot)::_126_384)
in (_126_386)::_126_385))
in (_126_388)::_126_387))
in (FSharp_Format.reduce1 _126_389))))))
end))
in (let letdoc = if rec_ then begin
(let _126_393 = (let _126_392 = (FSharp_Format.text "let")
in (let _126_391 = (let _126_390 = (FSharp_Format.text "rec")
in (_126_390)::[])
in (_126_392)::_126_391))
in (FSharp_Format.reduce1 _126_393))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _126_397 = (let _126_396 = if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end
in (_126_396)::(doc)::[])
in (FSharp_Format.reduce1 _126_397))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun currentModule decls -> (let for1 = (fun _60_507 -> (match (_60_507) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _60_512 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _126_406 = (let _126_405 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _126_405 doc))
in (FSharp_Format.parens _126_406)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _60_525 -> (match (_60_525) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _126_413 = (let _126_412 = (let _126_411 = (FSharp_Format.text ":")
in (_126_411)::(ty)::[])
in (name)::_126_412)
in (FSharp_Format.reduce1 _126_413))))
end))
in (let _126_416 = (let _126_415 = (FSharp_Format.text "; ")
in (let _126_414 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _126_415 _126_414)))
in (FSharp_Format.cbrackets _126_416)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _60_533 -> (match (_60_533) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _60_536 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _126_419 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _126_419 tys))
in (let _126_423 = (let _126_422 = (FSharp_Format.text name)
in (let _126_421 = (let _126_420 = (FSharp_Format.text "of")
in (_126_420)::(tys)::[])
in (_126_422)::_126_421))
in (FSharp_Format.reduce1 _126_423))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _126_426 = (let _126_425 = (FSharp_Format.text "|")
in (_126_425)::(d)::[])
in (FSharp_Format.reduce1 _126_426))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _126_430 = (let _126_429 = (let _126_428 = (let _126_427 = (ptsym currentModule ([], x))
in (FSharp_Format.text _126_427))
in (_126_428)::[])
in (tparams)::_126_429)
in (FSharp_Format.reduce1 _126_430))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _126_435 = (let _126_434 = (let _126_433 = (let _126_432 = (let _126_431 = (FSharp_Format.text "=")
in (_126_431)::[])
in (doc)::_126_432)
in (FSharp_Format.reduce1 _126_433))
in (_126_434)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _126_435)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = if ((FStar_List.length doc) > 0) then begin
(let _126_440 = (let _126_439 = (FSharp_Format.text "type")
in (let _126_438 = (let _126_437 = (let _126_436 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _126_436 doc))
in (_126_437)::[])
in (_126_439)::_126_438))
in (FSharp_Format.reduce1 _126_440))
end else begin
(FSharp_Format.text "")
end
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _126_460 = (let _126_459 = (let _126_452 = (let _126_451 = (FSharp_Format.text "module")
in (let _126_450 = (let _126_449 = (FSharp_Format.text x)
in (let _126_448 = (let _126_447 = (FSharp_Format.text "=")
in (_126_447)::[])
in (_126_449)::_126_448))
in (_126_451)::_126_450))
in (FSharp_Format.reduce1 _126_452))
in (let _126_458 = (let _126_457 = (doc_of_sig currentModule subsig)
in (let _126_456 = (let _126_455 = (let _126_454 = (let _126_453 = (FSharp_Format.text "end")
in (_126_453)::[])
in (FSharp_Format.reduce1 _126_454))
in (_126_455)::[])
in (_126_457)::_126_456))
in (_126_459)::_126_458))
in (FSharp_Format.combine FSharp_Format.hardline _126_460))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _126_464 = (let _126_463 = (FSharp_Format.text "exception")
in (let _126_462 = (let _126_461 = (FSharp_Format.text x)
in (_126_461)::[])
in (_126_463)::_126_462))
in (FSharp_Format.reduce1 _126_464))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _126_466 = (let _126_465 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _126_465 args))
in (FSharp_Format.parens _126_466))
in (let _126_472 = (let _126_471 = (FSharp_Format.text "exception")
in (let _126_470 = (let _126_469 = (FSharp_Format.text x)
in (let _126_468 = (let _126_467 = (FSharp_Format.text "of")
in (_126_467)::(args)::[])
in (_126_469)::_126_468))
in (_126_471)::_126_470))
in (FSharp_Format.reduce1 _126_472))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_60_567, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _126_478 = (let _126_477 = (FSharp_Format.text "val")
in (let _126_476 = (let _126_475 = (FSharp_Format.text x)
in (let _126_474 = (let _126_473 = (FSharp_Format.text ": ")
in (_126_473)::(ty)::[])
in (_126_475)::_126_474))
in (_126_477)::_126_476))
in (FSharp_Format.reduce1 _126_478)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _126_489 = (let _126_488 = (FSharp_Format.text "exception")
in (let _126_487 = (let _126_486 = (FSharp_Format.text x)
in (_126_486)::[])
in (_126_488)::_126_487))
in (FSharp_Format.reduce1 _126_489))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _126_491 = (let _126_490 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _126_490 args))
in (FSharp_Format.parens _126_491))
in (let _126_497 = (let _126_496 = (FSharp_Format.text "exception")
in (let _126_495 = (let _126_494 = (FSharp_Format.text x)
in (let _126_493 = (let _126_492 = (FSharp_Format.text "of")
in (_126_492)::(args)::[])
in (_126_494)::_126_493))
in (_126_496)::_126_495))
in (FSharp_Format.reduce1 _126_497))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _126_505 = (let _126_504 = (FSharp_Format.text "let")
in (let _126_503 = (let _126_502 = (FSharp_Format.text "_")
in (let _126_501 = (let _126_500 = (FSharp_Format.text "=")
in (let _126_499 = (let _126_498 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_126_498)::[])
in (_126_500)::_126_499))
in (_126_502)::_126_501))
in (_126_504)::_126_503))
in (FSharp_Format.reduce1 _126_505))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _60_606 -> (match (_60_606) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _60_613 -> (match (_60_613) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _126_524 = (let _126_523 = (FSharp_Format.text "module")
in (let _126_522 = (let _126_521 = (FSharp_Format.text x)
in (let _126_520 = (let _126_519 = (FSharp_Format.text ":")
in (let _126_518 = (let _126_517 = (FSharp_Format.text "sig")
in (_126_517)::[])
in (_126_519)::_126_518))
in (_126_521)::_126_520))
in (_126_523)::_126_522))
in (FSharp_Format.reduce1 _126_524))
in (let tail = (let _126_526 = (let _126_525 = (FSharp_Format.text "end")
in (_126_525)::[])
in (FSharp_Format.reduce1 _126_526))
in (let doc = (FStar_Option.map (fun _60_619 -> (match (_60_619) with
| (s, _60_618) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _126_536 = (let _126_535 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _126_534 = (let _126_533 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _126_532 = (let _126_531 = (FSharp_Format.reduce sub)
in (let _126_530 = (let _126_529 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_126_529)::[])
in (_126_531)::_126_530))
in (_126_533)::_126_532))
in (_126_535)::_126_534))
in (FSharp_Format.reduce _126_536)))))))
end))
and for1_mod = (fun istop _60_632 -> (match (_60_632) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _126_549 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _126_541 = (FSharp_Format.text "module")
in (let _126_540 = (let _126_539 = (FSharp_Format.text x)
in (_126_539)::[])
in (_126_541)::_126_540))
end else begin
if (not (istop)) then begin
(let _126_548 = (FSharp_Format.text "module")
in (let _126_547 = (let _126_546 = (FSharp_Format.text x)
in (let _126_545 = (let _126_544 = (FSharp_Format.text "=")
in (let _126_543 = (let _126_542 = (FSharp_Format.text "struct")
in (_126_542)::[])
in (_126_544)::_126_543))
in (_126_546)::_126_545))
in (_126_548)::_126_547))
end else begin
[]
end
end
in (FSharp_Format.reduce1 _126_549))
in (let tail = if (not (istop)) then begin
(let _126_551 = (let _126_550 = (FSharp_Format.text "end")
in (_126_550)::[])
in (FSharp_Format.reduce1 _126_551))
end else begin
(FSharp_Format.reduce1 [])
end
in (let doc = (FStar_Option.map (fun _60_638 -> (match (_60_638) with
| (_60_636, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _126_555 = (let _126_554 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _126_554 FSharp_Format.hardline))
in (_126_555)::[])
end else begin
[]
end
in (let _126_567 = (let _126_566 = (let _126_565 = (let _126_564 = (let _126_563 = (FSharp_Format.text "open Prims")
in (let _126_562 = (let _126_561 = (let _126_560 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _126_559 = (let _126_558 = (FSharp_Format.reduce sub)
in (let _126_557 = (let _126_556 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_126_556)::[])
in (_126_558)::_126_557))
in (_126_560)::_126_559))
in (FSharp_Format.hardline)::_126_561)
in (_126_563)::_126_562))
in (FSharp_Format.hardline)::_126_564)
in (head)::_126_565)
in (FStar_List.append prefix _126_566))
in (FStar_All.pipe_left FSharp_Format.reduce _126_567))))))))
end))
in (let docs = (FStar_List.map (fun _60_650 -> (match (_60_650) with
| (x, s, m) -> begin
(let _126_569 = (for1_mod true (x, s, m))
in (x, _126_569))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _126_576 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _126_576 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _126_581 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _126_581 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





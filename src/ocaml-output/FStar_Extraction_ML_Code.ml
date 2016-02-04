
open Prims
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

let is_ILeft : assoc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| ILeft -> begin
true
end
| _ -> begin
false
end))

let is_IRight : assoc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| IRight -> begin
true
end
| _ -> begin
false
end))

let is_Left : assoc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Left -> begin
true
end
| _ -> begin
false
end))

let is_Right : assoc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Right -> begin
true
end
| _ -> begin
false
end))

let is_NonAssoc : assoc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_Prefix : fixity  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Prefix -> begin
true
end
| _ -> begin
false
end))

let is_Postfix : fixity  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Postfix -> begin
true
end
| _ -> begin
false
end))

let is_Infix : fixity  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

let ___Infix____0 : fixity  ->  assoc = (fun projectee -> (match (projectee) with
| Infix (_78_3) -> begin
_78_3
end))

type opprec =
(Prims.int * fixity)

type level =
(opprec * assoc)

let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

let t_prio_name : (Prims.int * fixity) = (30, Postfix)

let e_bin_prio_lambda : (Prims.int * fixity) = (5, Prefix)

let e_bin_prio_if : (Prims.int * fixity) = (15, Prefix)

let e_bin_prio_letin : (Prims.int * fixity) = (19, Prefix)

let e_bin_prio_or : (Prims.int * fixity) = (20, Infix (Left))

let e_bin_prio_and : (Prims.int * fixity) = (25, Infix (Left))

let e_bin_prio_eq : (Prims.int * fixity) = (27, Infix (NonAssoc))

let e_bin_prio_order : (Prims.int * fixity) = (29, Infix (NonAssoc))

let e_bin_prio_op1 : (Prims.int * fixity) = (30, Infix (Left))

let e_bin_prio_op2 : (Prims.int * fixity) = (40, Infix (Left))

let e_bin_prio_op3 : (Prims.int * fixity) = (50, Infix (Left))

let e_bin_prio_op4 : (Prims.int * fixity) = (60, Infix (Left))

let e_bin_prio_comb : (Prims.int * fixity) = (70, Infix (Left))

let e_bin_prio_seq : (Prims.int * fixity) = (100, Infix (Left))

let e_app_prio : (Prims.int * fixity) = (10000, Infix (Left))

let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

let rec in_ns = (fun x -> (match (x) with
| ([], _78_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_78_18, _78_20) -> begin
false
end))

let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
in (let ns_len = (FStar_List.length ns)
in (let found = (FStar_Util.find_map cg_libs (fun cg_path -> (let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(let _78_31 = (FStar_Util.first_N cg_len ns)
in (match (_78_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _181_31 = (let _181_30 = (let _181_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_181_29)::[])
in (FStar_List.append pfx _181_30))
in Some (_181_31))
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

let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _78_41 -> begin
(let _78_44 = x
in (match (_78_44) with
| (ns, x) -> begin
(let _181_36 = (path_of_ns currentModule ns)
in (_181_36, x))
end))
end))

let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _181_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _181_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(let _78_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_78_50) with
| (p, s) -> begin
(let _181_46 = (let _181_45 = (let _181_44 = (ptsym_of_symbol s)
in (_181_44)::[])
in (FStar_List.append p _181_45))
in (FStar_String.concat "." _181_46))
end))
end)

let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (let _78_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_78_55) with
| (p, s) -> begin
(let s = if ((let _181_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _181_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

let prim_types = []

let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _78_60 -> (match (_78_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _78_66 -> (match (_78_66) with
| (y, _78_63, _78_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _78_70 -> (match (_78_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _78_74 -> (match (_78_74) with
| (y, _78_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

let as_standard_type = (fun _78_78 -> (match (_78_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _78_82 -> (match (_78_82) with
| (y, _78_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _78_86 -> (match (_78_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _78_90 -> (match (_78_90) with
| (y, _78_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FSharp_Format.doc  ->  FSharp_Format.doc = (fun _78_94 inner doc -> (match (_78_94) with
| (outer, side) -> begin
(let noparens = (fun _inner _outer side -> (let _78_103 = _inner
in (match (_78_103) with
| (pi, fi) -> begin
(let _78_106 = _outer
in (match (_78_106) with
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
| (_78_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_78_134, _78_136) -> begin
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

let ocaml_u8_codepoint : Prims.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

let encode_char : Prims.char  ->  Prims.string = (fun c -> if ((FStar_Util.int_of_char c) > 127) then begin
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
| _78_154 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end)

let string_of_mlconstant : FStar_Extraction_ML_Syntax.mlconstant  ->  Prims.string = (fun sctt -> (match (sctt) with
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
(let _181_92 = (let _181_91 = (encode_char c)
in (Prims.strcat "\'" _181_91))
in (Prims.strcat _181_92 "\'"))
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

let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FSharp_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _181_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _181_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _181_107 = (let _181_106 = (let _181_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _181_105 doc))
in (FSharp_Format.hbox _181_106))
in (FSharp_Format.parens _181_107))
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
| _78_198 -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _181_110 = (let _181_109 = (let _181_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _181_108 args))
in (FSharp_Format.hbox _181_109))
in (FSharp_Format.parens _181_110)))
end)
in (let name = if (is_standard_type name) then begin
(let _181_112 = (let _181_111 = (as_standard_type name)
in (FStar_Option.get _181_111))
in (Prims.snd _181_112))
end else begin
(ptsym currentModule name)
end
in (let _181_116 = (let _181_115 = (let _181_114 = (let _181_113 = (FSharp_Format.text name)
in (_181_113)::[])
in (args)::_181_114)
in (FSharp_Format.reduce1 _181_115))
in (FSharp_Format.hbox _181_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _78_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _181_121 = (let _181_120 = (let _181_119 = (let _181_118 = (let _181_117 = (FSharp_Format.text " -> ")
in (_181_117)::(d2)::[])
in (d1)::_181_118)
in (FSharp_Format.reduce1 _181_119))
in (FSharp_Format.hbox _181_120))
in (maybe_paren outer t_prio_fun _181_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FSharp_Format.text "obj")
end else begin
(FSharp_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FSharp_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _181_146 = (let _181_145 = (let _181_144 = (FSharp_Format.text "Prims.checked_cast")
in (_181_144)::(doc)::[])
in (FSharp_Format.reduce _181_145))
in (FSharp_Format.parens _181_146))
end else begin
(let _181_151 = (let _181_150 = (let _181_149 = (FSharp_Format.text "Obj.magic ")
in (let _181_148 = (let _181_147 = (FSharp_Format.parens doc)
in (_181_147)::[])
in (_181_149)::_181_148))
in (FSharp_Format.reduce _181_150))
in (FSharp_Format.parens _181_151))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _181_155 = (let _181_154 = (let _181_153 = (FSharp_Format.text ";")
in (_181_153)::(FSharp_Format.hardline)::[])
in (d)::_181_154)
in (FSharp_Format.reduce _181_155))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _181_156 = (string_of_mlconstant c)
in (FSharp_Format.text _181_156))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _78_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _181_157 = (ptsym currentModule path)
in (FSharp_Format.text _181_157))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _78_244 -> (match (_78_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _181_164 = (let _181_163 = (let _181_160 = (ptsym currentModule (path, name))
in (FSharp_Format.text _181_160))
in (let _181_162 = (let _181_161 = (FSharp_Format.text "=")
in (_181_161)::(doc)::[])
in (_181_163)::_181_162))
in (FSharp_Format.reduce1 _181_164)))
end))
in (let _181_167 = (let _181_166 = (FSharp_Format.text "; ")
in (let _181_165 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _181_166 _181_165)))
in (FSharp_Format.cbrackets _181_167)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _181_169 = (let _181_168 = (as_standard_constructor ctor)
in (FStar_Option.get _181_168))
in (Prims.snd _181_169))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _181_171 = (let _181_170 = (as_standard_constructor ctor)
in (FStar_Option.get _181_170))
in (Prims.snd _181_171))
end else begin
(ptctor currentModule ctor)
end
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _181_175 = (let _181_174 = (FSharp_Format.parens x)
in (let _181_173 = (let _181_172 = (FSharp_Format.text "::")
in (_181_172)::(xs)::[])
in (_181_174)::_181_173))
in (FSharp_Format.reduce _181_175))
end
| (_78_263, _78_265) -> begin
(let _181_181 = (let _181_180 = (FSharp_Format.text name)
in (let _181_179 = (let _181_178 = (let _181_177 = (let _181_176 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _181_176 args))
in (FSharp_Format.parens _181_177))
in (_181_178)::[])
in (_181_180)::_181_179))
in (FSharp_Format.reduce1 _181_181))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _181_183 = (let _181_182 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _181_182 docs))
in (FSharp_Format.parens _181_183))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _181_189 = (let _181_188 = (let _181_187 = (let _181_186 = (let _181_185 = (let _181_184 = (FSharp_Format.text "in")
in (_181_184)::(body)::[])
in (FSharp_Format.reduce1 _181_185))
in (_181_186)::[])
in (doc)::_181_187)
in (FSharp_Format.combine FSharp_Format.hardline _181_188))
in (FSharp_Format.parens _181_189))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _78_291}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _78_309}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _78_321 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _181_190 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _181_190))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _181_195 = (let _181_194 = (let _181_193 = (FSharp_Format.text ".")
in (let _181_192 = (let _181_191 = (FSharp_Format.text (Prims.snd f))
in (_181_191)::[])
in (_181_193)::_181_192))
in (e)::_181_194)
in (FSharp_Format.reduce _181_195))
end else begin
(let _181_201 = (let _181_200 = (let _181_199 = (FSharp_Format.text ".")
in (let _181_198 = (let _181_197 = (let _181_196 = (ptsym currentModule f)
in (FSharp_Format.text _181_196))
in (_181_197)::[])
in (_181_199)::_181_198))
in (e)::_181_200)
in (FSharp_Format.reduce _181_201))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _181_217 = (let _181_216 = (FSharp_Format.text "(")
in (let _181_215 = (let _181_214 = (FSharp_Format.text x)
in (let _181_213 = (let _181_212 = (match (xt) with
| Some (xxt) -> begin
(let _181_209 = (let _181_208 = (FSharp_Format.text " : ")
in (let _181_207 = (let _181_206 = (doc_of_mltype currentModule outer xxt)
in (_181_206)::[])
in (_181_208)::_181_207))
in (FSharp_Format.reduce1 _181_209))
end
| _78_340 -> begin
(FSharp_Format.text "")
end)
in (let _181_211 = (let _181_210 = (FSharp_Format.text ")")
in (_181_210)::[])
in (_181_212)::_181_211))
in (_181_214)::_181_213))
in (_181_216)::_181_215))
in (FSharp_Format.reduce1 _181_217))
end else begin
(FSharp_Format.text x)
end)
in (let ids = (FStar_List.map (fun _78_346 -> (match (_78_346) with
| ((x, _78_343), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _181_224 = (let _181_223 = (FSharp_Format.text "fun")
in (let _181_222 = (let _181_221 = (FSharp_Format.reduce1 ids)
in (let _181_220 = (let _181_219 = (FSharp_Format.text "->")
in (_181_219)::(body)::[])
in (_181_221)::_181_220))
in (_181_223)::_181_222))
in (FSharp_Format.reduce1 _181_224))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _181_237 = (let _181_236 = (let _181_231 = (let _181_230 = (FSharp_Format.text "if")
in (let _181_229 = (let _181_228 = (let _181_227 = (FSharp_Format.text "then")
in (let _181_226 = (let _181_225 = (FSharp_Format.text "begin")
in (_181_225)::[])
in (_181_227)::_181_226))
in (cond)::_181_228)
in (_181_230)::_181_229))
in (FSharp_Format.reduce1 _181_231))
in (let _181_235 = (let _181_234 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _181_233 = (let _181_232 = (FSharp_Format.text "end")
in (_181_232)::[])
in (_181_234)::_181_233))
in (_181_236)::_181_235))
in (FSharp_Format.combine FSharp_Format.hardline _181_237))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _181_260 = (let _181_259 = (let _181_244 = (let _181_243 = (FSharp_Format.text "if")
in (let _181_242 = (let _181_241 = (let _181_240 = (FSharp_Format.text "then")
in (let _181_239 = (let _181_238 = (FSharp_Format.text "begin")
in (_181_238)::[])
in (_181_240)::_181_239))
in (cond)::_181_241)
in (_181_243)::_181_242))
in (FSharp_Format.reduce1 _181_244))
in (let _181_258 = (let _181_257 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _181_256 = (let _181_255 = (let _181_250 = (let _181_249 = (FSharp_Format.text "end")
in (let _181_248 = (let _181_247 = (FSharp_Format.text "else")
in (let _181_246 = (let _181_245 = (FSharp_Format.text "begin")
in (_181_245)::[])
in (_181_247)::_181_246))
in (_181_249)::_181_248))
in (FSharp_Format.reduce1 _181_250))
in (let _181_254 = (let _181_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _181_252 = (let _181_251 = (FSharp_Format.text "end")
in (_181_251)::[])
in (_181_253)::_181_252))
in (_181_255)::_181_254))
in (_181_257)::_181_256))
in (_181_259)::_181_258))
in (FSharp_Format.combine FSharp_Format.hardline _181_260))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _181_267 = (let _181_266 = (let _181_265 = (FSharp_Format.text "match")
in (let _181_264 = (let _181_263 = (FSharp_Format.parens cond)
in (let _181_262 = (let _181_261 = (FSharp_Format.text "with")
in (_181_261)::[])
in (_181_263)::_181_262))
in (_181_265)::_181_264))
in (FSharp_Format.reduce1 _181_266))
in (_181_267)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _181_272 = (let _181_271 = (FSharp_Format.text "raise")
in (let _181_270 = (let _181_269 = (let _181_268 = (ptctor currentModule exn)
in (FSharp_Format.text _181_268))
in (_181_269)::[])
in (_181_271)::_181_270))
in (FSharp_Format.reduce1 _181_272))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _181_281 = (let _181_280 = (FSharp_Format.text "raise")
in (let _181_279 = (let _181_278 = (let _181_273 = (ptctor currentModule exn)
in (FSharp_Format.text _181_273))
in (let _181_277 = (let _181_276 = (let _181_275 = (let _181_274 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _181_274 args))
in (FSharp_Format.parens _181_275))
in (_181_276)::[])
in (_181_278)::_181_277))
in (_181_280)::_181_279))
in (FSharp_Format.reduce1 _181_281)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _181_298 = (let _181_297 = (let _181_285 = (let _181_284 = (FSharp_Format.text "try")
in (let _181_283 = (let _181_282 = (FSharp_Format.text "begin")
in (_181_282)::[])
in (_181_284)::_181_283))
in (FSharp_Format.reduce1 _181_285))
in (let _181_296 = (let _181_295 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _181_294 = (let _181_293 = (let _181_289 = (let _181_288 = (FSharp_Format.text "end")
in (let _181_287 = (let _181_286 = (FSharp_Format.text "with")
in (_181_286)::[])
in (_181_288)::_181_287))
in (FSharp_Format.reduce1 _181_289))
in (let _181_292 = (let _181_291 = (let _181_290 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _181_290))
in (_181_291)::[])
in (_181_293)::_181_292))
in (_181_295)::_181_294))
in (_181_297)::_181_296))
in (FSharp_Format.combine FSharp_Format.hardline _181_298))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule p e1 e2 -> (let _78_394 = (let _181_303 = (as_bin_op p)
in (FStar_Option.get _181_303))
in (match (_78_394) with
| (_78_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _181_306 = (let _181_305 = (let _181_304 = (FSharp_Format.text txt)
in (_181_304)::(e2)::[])
in (e1)::_181_305)
in (FSharp_Format.reduce1 _181_306))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule p e1 -> (let _78_404 = (let _181_310 = (as_uni_op p)
in (FStar_Option.get _181_310))
in (match (_78_404) with
| (_78_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _181_314 = (let _181_313 = (FSharp_Format.text txt)
in (let _181_312 = (let _181_311 = (FSharp_Format.parens e1)
in (_181_311)::[])
in (_181_313)::_181_312))
in (FSharp_Format.reduce1 _181_314))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FSharp_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _181_317 = (string_of_mlconstant c)
in (FSharp_Format.text _181_317))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _78_421 -> (match (_78_421) with
| (name, p) -> begin
(let _181_326 = (let _181_325 = (let _181_320 = (ptsym currentModule (path, name))
in (FSharp_Format.text _181_320))
in (let _181_324 = (let _181_323 = (FSharp_Format.text "=")
in (let _181_322 = (let _181_321 = (doc_of_pattern currentModule p)
in (_181_321)::[])
in (_181_323)::_181_322))
in (_181_325)::_181_324))
in (FSharp_Format.reduce1 _181_326))
end))
in (let _181_329 = (let _181_328 = (FSharp_Format.text "; ")
in (let _181_327 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _181_328 _181_327)))
in (FSharp_Format.cbrackets _181_329)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _181_331 = (let _181_330 = (as_standard_constructor ctor)
in (FStar_Option.get _181_330))
in (Prims.snd _181_331))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _181_333 = (let _181_332 = (as_standard_constructor ctor)
in (FStar_Option.get _181_332))
in (Prims.snd _181_333))
end else begin
(ptctor currentModule ctor)
end
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _181_339 = (let _181_338 = (doc_of_pattern currentModule x)
in (let _181_337 = (let _181_336 = (FSharp_Format.text "::")
in (let _181_335 = (let _181_334 = (doc_of_pattern currentModule xs)
in (_181_334)::[])
in (_181_336)::_181_335))
in (_181_338)::_181_337))
in (FSharp_Format.reduce _181_339))
end
| (_78_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_78_440)::[]) -> begin
(let _181_344 = (let _181_343 = (FSharp_Format.text name)
in (let _181_342 = (let _181_341 = (let _181_340 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _181_340))
in (_181_341)::[])
in (_181_343)::_181_342))
in (FSharp_Format.reduce1 _181_344))
end
| _78_445 -> begin
(let _181_351 = (let _181_350 = (FSharp_Format.text name)
in (let _181_349 = (let _181_348 = (let _181_347 = (let _181_346 = (FSharp_Format.text ", ")
in (let _181_345 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _181_346 _181_345)))
in (FSharp_Format.parens _181_347))
in (_181_348)::[])
in (_181_350)::_181_349))
in (FSharp_Format.reduce1 _181_351))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _181_353 = (let _181_352 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _181_352 ps))
in (FSharp_Format.parens _181_353)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _181_354 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _181_354 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FSharp_Format.doc = (fun currentModule _78_458 -> (match (_78_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _181_360 = (let _181_359 = (FSharp_Format.text "|")
in (let _181_358 = (let _181_357 = (doc_of_pattern currentModule p)
in (_181_357)::[])
in (_181_359)::_181_358))
in (FSharp_Format.reduce1 _181_360))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _181_366 = (let _181_365 = (FSharp_Format.text "|")
in (let _181_364 = (let _181_363 = (doc_of_pattern currentModule p)
in (let _181_362 = (let _181_361 = (FSharp_Format.text "when")
in (_181_361)::(c)::[])
in (_181_363)::_181_362))
in (_181_365)::_181_364))
in (FSharp_Format.reduce1 _181_366)))
end)
in (let _181_377 = (let _181_376 = (let _181_371 = (let _181_370 = (let _181_369 = (FSharp_Format.text "->")
in (let _181_368 = (let _181_367 = (FSharp_Format.text "begin")
in (_181_367)::[])
in (_181_369)::_181_368))
in (case)::_181_370)
in (FSharp_Format.reduce1 _181_371))
in (let _181_375 = (let _181_374 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _181_373 = (let _181_372 = (FSharp_Format.text "end")
in (_181_372)::[])
in (_181_374)::_181_373))
in (_181_376)::_181_375))
in (FSharp_Format.combine FSharp_Format.hardline _181_377)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FSharp_Format.doc = (fun currentModule _78_468 -> (match (_78_468) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun _78_475 -> (match (_78_475) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _78_472; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (FStar_List.map (fun _78_481 -> (match (_78_481) with
| (x, _78_480) -> begin
(FSharp_Format.text x)
end)) ids)
in (let ty_annot = if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (_78_486::_78_484, _78_489) -> begin
(FSharp_Format.text "")
end
| ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _181_384 = (let _181_383 = (FSharp_Format.text ":")
in (_181_383)::(ty)::[])
in (FSharp_Format.reduce1 _181_384)))
end)
end else begin
if top_level then begin
(match (tys) with
| (_78_498::_78_496, _78_501) -> begin
(FSharp_Format.text "")
end
| ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) (Prims.snd tys))
in (let _181_386 = (let _181_385 = (FSharp_Format.text ":")
in (_181_385)::(ty)::[])
in (FSharp_Format.reduce1 _181_386)))
end)
end else begin
(FSharp_Format.text "")
end
end
in (let _181_393 = (let _181_392 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _181_391 = (let _181_390 = (FSharp_Format.reduce1 ids)
in (let _181_389 = (let _181_388 = (let _181_387 = (FSharp_Format.text "=")
in (_181_387)::(e)::[])
in (ty_annot)::_181_388)
in (_181_390)::_181_389))
in (_181_392)::_181_391))
in (FSharp_Format.reduce1 _181_393))))))
end))
in (let letdoc = if rec_ then begin
(let _181_397 = (let _181_396 = (FSharp_Format.text "let")
in (let _181_395 = (let _181_394 = (FSharp_Format.text "rec")
in (_181_394)::[])
in (_181_396)::_181_395))
in (FSharp_Format.reduce1 _181_397))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _181_401 = (let _181_400 = if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end
in (_181_400)::(doc)::[])
in (FSharp_Format.reduce1 _181_401))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FSharp_Format.doc = (fun currentModule decls -> (let for1 = (fun _78_519 -> (match (_78_519) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _78_524 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _181_410 = (let _181_409 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _181_409 doc))
in (FSharp_Format.parens _181_410)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _78_537 -> (match (_78_537) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _181_417 = (let _181_416 = (let _181_415 = (FSharp_Format.text ":")
in (_181_415)::(ty)::[])
in (name)::_181_416)
in (FSharp_Format.reduce1 _181_417))))
end))
in (let _181_420 = (let _181_419 = (FSharp_Format.text "; ")
in (let _181_418 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _181_419 _181_418)))
in (FSharp_Format.cbrackets _181_420)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _78_545 -> (match (_78_545) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _78_548 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _181_423 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _181_423 tys))
in (let _181_427 = (let _181_426 = (FSharp_Format.text name)
in (let _181_425 = (let _181_424 = (FSharp_Format.text "of")
in (_181_424)::(tys)::[])
in (_181_426)::_181_425))
in (FSharp_Format.reduce1 _181_427))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _181_430 = (let _181_429 = (FSharp_Format.text "|")
in (_181_429)::(d)::[])
in (FSharp_Format.reduce1 _181_430))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _181_434 = (let _181_433 = (let _181_432 = (let _181_431 = (ptsym currentModule ([], x))
in (FSharp_Format.text _181_431))
in (_181_432)::[])
in (tparams)::_181_433)
in (FSharp_Format.reduce1 _181_434))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _181_439 = (let _181_438 = (let _181_437 = (let _181_436 = (let _181_435 = (FSharp_Format.text "=")
in (_181_435)::[])
in (doc)::_181_436)
in (FSharp_Format.reduce1 _181_437))
in (_181_438)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _181_439)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = if ((FStar_List.length doc) > 0) then begin
(let _181_444 = (let _181_443 = (FSharp_Format.text "type")
in (let _181_442 = (let _181_441 = (let _181_440 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _181_440 doc))
in (_181_441)::[])
in (_181_443)::_181_442))
in (FSharp_Format.reduce1 _181_444))
end else begin
(FSharp_Format.text "")
end
in doc))))

let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FSharp_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _181_464 = (let _181_463 = (let _181_456 = (let _181_455 = (FSharp_Format.text "module")
in (let _181_454 = (let _181_453 = (FSharp_Format.text x)
in (let _181_452 = (let _181_451 = (FSharp_Format.text "=")
in (_181_451)::[])
in (_181_453)::_181_452))
in (_181_455)::_181_454))
in (FSharp_Format.reduce1 _181_456))
in (let _181_462 = (let _181_461 = (doc_of_sig currentModule subsig)
in (let _181_460 = (let _181_459 = (let _181_458 = (let _181_457 = (FSharp_Format.text "end")
in (_181_457)::[])
in (FSharp_Format.reduce1 _181_458))
in (_181_459)::[])
in (_181_461)::_181_460))
in (_181_463)::_181_462))
in (FSharp_Format.combine FSharp_Format.hardline _181_464))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _181_468 = (let _181_467 = (FSharp_Format.text "exception")
in (let _181_466 = (let _181_465 = (FSharp_Format.text x)
in (_181_465)::[])
in (_181_467)::_181_466))
in (FSharp_Format.reduce1 _181_468))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _181_470 = (let _181_469 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _181_469 args))
in (FSharp_Format.parens _181_470))
in (let _181_476 = (let _181_475 = (FSharp_Format.text "exception")
in (let _181_474 = (let _181_473 = (FSharp_Format.text x)
in (let _181_472 = (let _181_471 = (FSharp_Format.text "of")
in (_181_471)::(args)::[])
in (_181_473)::_181_472))
in (_181_475)::_181_474))
in (FSharp_Format.reduce1 _181_476))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_78_579, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _181_482 = (let _181_481 = (FSharp_Format.text "val")
in (let _181_480 = (let _181_479 = (FSharp_Format.text x)
in (let _181_478 = (let _181_477 = (FSharp_Format.text ": ")
in (_181_477)::(ty)::[])
in (_181_479)::_181_478))
in (_181_481)::_181_480))
in (FSharp_Format.reduce1 _181_482)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FSharp_Format.doc = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FSharp_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _181_493 = (let _181_492 = (FSharp_Format.text "exception")
in (let _181_491 = (let _181_490 = (FSharp_Format.text x)
in (_181_490)::[])
in (_181_492)::_181_491))
in (FSharp_Format.reduce1 _181_493))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _181_495 = (let _181_494 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _181_494 args))
in (FSharp_Format.parens _181_495))
in (let _181_501 = (let _181_500 = (FSharp_Format.text "exception")
in (let _181_499 = (let _181_498 = (FSharp_Format.text x)
in (let _181_497 = (let _181_496 = (FSharp_Format.text "of")
in (_181_496)::(args)::[])
in (_181_498)::_181_497))
in (_181_500)::_181_499))
in (FSharp_Format.reduce1 _181_501))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _181_509 = (let _181_508 = (FSharp_Format.text "let")
in (let _181_507 = (let _181_506 = (FSharp_Format.text "_")
in (let _181_505 = (let _181_504 = (FSharp_Format.text "=")
in (let _181_503 = (let _181_502 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_181_502)::[])
in (_181_504)::_181_503))
in (_181_506)::_181_505))
in (_181_508)::_181_507))
in (FSharp_Format.reduce1 _181_509))
end))

let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FSharp_Format.doc = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FSharp_Format.doc) Prims.list = (fun _78_618 -> (match (_78_618) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _78_625 -> (match (_78_625) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _181_528 = (let _181_527 = (FSharp_Format.text "module")
in (let _181_526 = (let _181_525 = (FSharp_Format.text x)
in (let _181_524 = (let _181_523 = (FSharp_Format.text ":")
in (let _181_522 = (let _181_521 = (FSharp_Format.text "sig")
in (_181_521)::[])
in (_181_523)::_181_522))
in (_181_525)::_181_524))
in (_181_527)::_181_526))
in (FSharp_Format.reduce1 _181_528))
in (let tail = (let _181_530 = (let _181_529 = (FSharp_Format.text "end")
in (_181_529)::[])
in (FSharp_Format.reduce1 _181_530))
in (let doc = (FStar_Option.map (fun _78_631 -> (match (_78_631) with
| (s, _78_630) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _181_540 = (let _181_539 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _181_538 = (let _181_537 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _181_536 = (let _181_535 = (FSharp_Format.reduce sub)
in (let _181_534 = (let _181_533 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_181_533)::[])
in (_181_535)::_181_534))
in (_181_537)::_181_536))
in (_181_539)::_181_538))
in (FSharp_Format.reduce _181_540)))))))
end))
and for1_mod = (fun istop _78_644 -> (match (_78_644) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _181_553 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _181_545 = (FSharp_Format.text "module")
in (let _181_544 = (let _181_543 = (FSharp_Format.text x)
in (_181_543)::[])
in (_181_545)::_181_544))
end else begin
if (not (istop)) then begin
(let _181_552 = (FSharp_Format.text "module")
in (let _181_551 = (let _181_550 = (FSharp_Format.text x)
in (let _181_549 = (let _181_548 = (FSharp_Format.text "=")
in (let _181_547 = (let _181_546 = (FSharp_Format.text "struct")
in (_181_546)::[])
in (_181_548)::_181_547))
in (_181_550)::_181_549))
in (_181_552)::_181_551))
end else begin
[]
end
end
in (FSharp_Format.reduce1 _181_553))
in (let tail = if (not (istop)) then begin
(let _181_555 = (let _181_554 = (FSharp_Format.text "end")
in (_181_554)::[])
in (FSharp_Format.reduce1 _181_555))
end else begin
(FSharp_Format.reduce1 [])
end
in (let doc = (FStar_Option.map (fun _78_650 -> (match (_78_650) with
| (_78_648, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _181_559 = (let _181_558 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _181_558 FSharp_Format.hardline))
in (_181_559)::[])
end else begin
[]
end
in (let _181_571 = (let _181_570 = (let _181_569 = (let _181_568 = (let _181_567 = (FSharp_Format.text "open Prims")
in (let _181_566 = (let _181_565 = (let _181_564 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _181_563 = (let _181_562 = (FSharp_Format.reduce sub)
in (let _181_561 = (let _181_560 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_181_560)::[])
in (_181_562)::_181_561))
in (_181_564)::_181_563))
in (FSharp_Format.hardline)::_181_565)
in (_181_567)::_181_566))
in (FSharp_Format.hardline)::_181_568)
in (head)::_181_569)
in (FStar_List.append prefix _181_570))
in (FStar_All.pipe_left FSharp_Format.reduce _181_571))))))))
end))
in (let docs = (FStar_List.map (fun _78_662 -> (match (_78_662) with
| (x, s, m) -> begin
(let _181_573 = (for1_mod true (x, s, m))
in (x, _181_573))
end)) mllib)
in docs))
end))

let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FSharp_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun env e -> (let doc = (let _181_580 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _181_580 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun env e -> (let doc = (let _181_585 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _181_585 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





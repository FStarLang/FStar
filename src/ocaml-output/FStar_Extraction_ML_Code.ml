
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
| Infix (_77_3) -> begin
_77_3
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
| ([], _77_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_77_18, _77_20) -> begin
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
(let _77_31 = (FStar_Util.first_N cg_len ns)
in (match (_77_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _179_31 = (let _179_30 = (let _179_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_179_29)::[])
in (FStar_List.append pfx _179_30))
in Some (_179_31))
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
| _77_41 -> begin
(let _77_44 = x
in (match (_77_44) with
| (ns, x) -> begin
(let _179_36 = (path_of_ns currentModule ns)
in (_179_36, x))
end))
end))

let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _179_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _179_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(let _77_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_77_50) with
| (p, s) -> begin
(let _179_46 = (let _179_45 = (let _179_44 = (ptsym_of_symbol s)
in (_179_44)::[])
in (FStar_List.append p _179_45))
in (FStar_String.concat "." _179_46))
end))
end)

let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (let _77_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_77_55) with
| (p, s) -> begin
(let s = if ((let _179_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _179_51)) <> (FStar_String.get s 0)) then begin
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

let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _77_60 -> (match (_77_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_66 -> (match (_77_66) with
| (y, _77_63, _77_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _77_70 -> (match (_77_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_74 -> (match (_77_74) with
| (y, _77_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

let as_standard_type = (fun _77_78 -> (match (_77_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_82 -> (match (_77_82) with
| (y, _77_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _77_86 -> (match (_77_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_90 -> (match (_77_90) with
| (y, _77_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FSharp_Format.doc  ->  FSharp_Format.doc = (fun _77_94 inner doc -> (match (_77_94) with
| (outer, side) -> begin
(let noparens = (fun _inner _outer side -> (let _77_103 = _inner
in (match (_77_103) with
| (pi, fi) -> begin
(let _77_106 = _outer
in (match (_77_106) with
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
| (_77_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_77_134, _77_136) -> begin
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
| _77_154 -> begin
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
(let _179_92 = (let _179_91 = (encode_char c)
in (Prims.strcat "\'" _179_91))
in (Prims.strcat _179_92 "\'"))
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
in (let _179_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _179_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _179_107 = (let _179_106 = (let _179_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _179_105 doc))
in (FSharp_Format.hbox _179_106))
in (FSharp_Format.parens _179_107))
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
| _77_198 -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _179_110 = (let _179_109 = (let _179_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _179_108 args))
in (FSharp_Format.hbox _179_109))
in (FSharp_Format.parens _179_110)))
end)
in (let name = if (is_standard_type name) then begin
(let _179_112 = (let _179_111 = (as_standard_type name)
in (FStar_Option.get _179_111))
in (Prims.snd _179_112))
end else begin
(ptsym currentModule name)
end
in (let _179_116 = (let _179_115 = (let _179_114 = (let _179_113 = (FSharp_Format.text name)
in (_179_113)::[])
in (args)::_179_114)
in (FSharp_Format.reduce1 _179_115))
in (FSharp_Format.hbox _179_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _77_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _179_121 = (let _179_120 = (let _179_119 = (let _179_118 = (let _179_117 = (FSharp_Format.text " -> ")
in (_179_117)::(d2)::[])
in (d1)::_179_118)
in (FSharp_Format.reduce1 _179_119))
in (FSharp_Format.hbox _179_120))
in (maybe_paren outer t_prio_fun _179_121))))
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
(let _179_146 = (let _179_145 = (let _179_144 = (FSharp_Format.text "Prims.checked_cast")
in (_179_144)::(doc)::[])
in (FSharp_Format.reduce _179_145))
in (FSharp_Format.parens _179_146))
end else begin
(let _179_151 = (let _179_150 = (let _179_149 = (FSharp_Format.text "Obj.magic ")
in (let _179_148 = (let _179_147 = (FSharp_Format.parens doc)
in (_179_147)::[])
in (_179_149)::_179_148))
in (FSharp_Format.reduce _179_150))
in (FSharp_Format.parens _179_151))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _179_155 = (let _179_154 = (let _179_153 = (FSharp_Format.text ";")
in (_179_153)::(FSharp_Format.hardline)::[])
in (d)::_179_154)
in (FSharp_Format.reduce _179_155))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _179_156 = (string_of_mlconstant c)
in (FSharp_Format.text _179_156))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _77_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _179_157 = (ptsym currentModule path)
in (FSharp_Format.text _179_157))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _77_244 -> (match (_77_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _179_164 = (let _179_163 = (let _179_160 = (ptsym currentModule (path, name))
in (FSharp_Format.text _179_160))
in (let _179_162 = (let _179_161 = (FSharp_Format.text "=")
in (_179_161)::(doc)::[])
in (_179_163)::_179_162))
in (FSharp_Format.reduce1 _179_164)))
end))
in (let _179_167 = (let _179_166 = (FSharp_Format.text "; ")
in (let _179_165 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _179_166 _179_165)))
in (FSharp_Format.cbrackets _179_167)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _179_169 = (let _179_168 = (as_standard_constructor ctor)
in (FStar_Option.get _179_168))
in (Prims.snd _179_169))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _179_171 = (let _179_170 = (as_standard_constructor ctor)
in (FStar_Option.get _179_170))
in (Prims.snd _179_171))
end else begin
(ptctor currentModule ctor)
end
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _179_175 = (let _179_174 = (FSharp_Format.parens x)
in (let _179_173 = (let _179_172 = (FSharp_Format.text "::")
in (_179_172)::(xs)::[])
in (_179_174)::_179_173))
in (FSharp_Format.reduce _179_175))
end
| (_77_263, _77_265) -> begin
(let _179_181 = (let _179_180 = (FSharp_Format.text name)
in (let _179_179 = (let _179_178 = (let _179_177 = (let _179_176 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _179_176 args))
in (FSharp_Format.parens _179_177))
in (_179_178)::[])
in (_179_180)::_179_179))
in (FSharp_Format.reduce1 _179_181))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _179_183 = (let _179_182 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _179_182 docs))
in (FSharp_Format.parens _179_183))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _179_189 = (let _179_188 = (let _179_187 = (let _179_186 = (let _179_185 = (let _179_184 = (FSharp_Format.text "in")
in (_179_184)::(body)::[])
in (FSharp_Format.reduce1 _179_185))
in (_179_186)::[])
in (doc)::_179_187)
in (FSharp_Format.combine FSharp_Format.hardline _179_188))
in (FSharp_Format.parens _179_189))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _77_291}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _77_309}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _77_321 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _179_190 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _179_190))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _179_195 = (let _179_194 = (let _179_193 = (FSharp_Format.text ".")
in (let _179_192 = (let _179_191 = (FSharp_Format.text (Prims.snd f))
in (_179_191)::[])
in (_179_193)::_179_192))
in (e)::_179_194)
in (FSharp_Format.reduce _179_195))
end else begin
(let _179_201 = (let _179_200 = (let _179_199 = (FSharp_Format.text ".")
in (let _179_198 = (let _179_197 = (let _179_196 = (ptsym currentModule f)
in (FSharp_Format.text _179_196))
in (_179_197)::[])
in (_179_199)::_179_198))
in (e)::_179_200)
in (FSharp_Format.reduce _179_201))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _179_217 = (let _179_216 = (FSharp_Format.text "(")
in (let _179_215 = (let _179_214 = (FSharp_Format.text x)
in (let _179_213 = (let _179_212 = (match (xt) with
| Some (xxt) -> begin
(let _179_209 = (let _179_208 = (FSharp_Format.text " : ")
in (let _179_207 = (let _179_206 = (doc_of_mltype currentModule outer xxt)
in (_179_206)::[])
in (_179_208)::_179_207))
in (FSharp_Format.reduce1 _179_209))
end
| _77_340 -> begin
(FSharp_Format.text "")
end)
in (let _179_211 = (let _179_210 = (FSharp_Format.text ")")
in (_179_210)::[])
in (_179_212)::_179_211))
in (_179_214)::_179_213))
in (_179_216)::_179_215))
in (FSharp_Format.reduce1 _179_217))
end else begin
(FSharp_Format.text x)
end)
in (let ids = (FStar_List.map (fun _77_346 -> (match (_77_346) with
| ((x, _77_343), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _179_224 = (let _179_223 = (FSharp_Format.text "fun")
in (let _179_222 = (let _179_221 = (FSharp_Format.reduce1 ids)
in (let _179_220 = (let _179_219 = (FSharp_Format.text "->")
in (_179_219)::(body)::[])
in (_179_221)::_179_220))
in (_179_223)::_179_222))
in (FSharp_Format.reduce1 _179_224))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _179_237 = (let _179_236 = (let _179_231 = (let _179_230 = (FSharp_Format.text "if")
in (let _179_229 = (let _179_228 = (let _179_227 = (FSharp_Format.text "then")
in (let _179_226 = (let _179_225 = (FSharp_Format.text "begin")
in (_179_225)::[])
in (_179_227)::_179_226))
in (cond)::_179_228)
in (_179_230)::_179_229))
in (FSharp_Format.reduce1 _179_231))
in (let _179_235 = (let _179_234 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _179_233 = (let _179_232 = (FSharp_Format.text "end")
in (_179_232)::[])
in (_179_234)::_179_233))
in (_179_236)::_179_235))
in (FSharp_Format.combine FSharp_Format.hardline _179_237))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _179_260 = (let _179_259 = (let _179_244 = (let _179_243 = (FSharp_Format.text "if")
in (let _179_242 = (let _179_241 = (let _179_240 = (FSharp_Format.text "then")
in (let _179_239 = (let _179_238 = (FSharp_Format.text "begin")
in (_179_238)::[])
in (_179_240)::_179_239))
in (cond)::_179_241)
in (_179_243)::_179_242))
in (FSharp_Format.reduce1 _179_244))
in (let _179_258 = (let _179_257 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _179_256 = (let _179_255 = (let _179_250 = (let _179_249 = (FSharp_Format.text "end")
in (let _179_248 = (let _179_247 = (FSharp_Format.text "else")
in (let _179_246 = (let _179_245 = (FSharp_Format.text "begin")
in (_179_245)::[])
in (_179_247)::_179_246))
in (_179_249)::_179_248))
in (FSharp_Format.reduce1 _179_250))
in (let _179_254 = (let _179_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _179_252 = (let _179_251 = (FSharp_Format.text "end")
in (_179_251)::[])
in (_179_253)::_179_252))
in (_179_255)::_179_254))
in (_179_257)::_179_256))
in (_179_259)::_179_258))
in (FSharp_Format.combine FSharp_Format.hardline _179_260))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _179_267 = (let _179_266 = (let _179_265 = (FSharp_Format.text "match")
in (let _179_264 = (let _179_263 = (FSharp_Format.parens cond)
in (let _179_262 = (let _179_261 = (FSharp_Format.text "with")
in (_179_261)::[])
in (_179_263)::_179_262))
in (_179_265)::_179_264))
in (FSharp_Format.reduce1 _179_266))
in (_179_267)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _179_272 = (let _179_271 = (FSharp_Format.text "raise")
in (let _179_270 = (let _179_269 = (let _179_268 = (ptctor currentModule exn)
in (FSharp_Format.text _179_268))
in (_179_269)::[])
in (_179_271)::_179_270))
in (FSharp_Format.reduce1 _179_272))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _179_281 = (let _179_280 = (FSharp_Format.text "raise")
in (let _179_279 = (let _179_278 = (let _179_273 = (ptctor currentModule exn)
in (FSharp_Format.text _179_273))
in (let _179_277 = (let _179_276 = (let _179_275 = (let _179_274 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _179_274 args))
in (FSharp_Format.parens _179_275))
in (_179_276)::[])
in (_179_278)::_179_277))
in (_179_280)::_179_279))
in (FSharp_Format.reduce1 _179_281)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _179_298 = (let _179_297 = (let _179_285 = (let _179_284 = (FSharp_Format.text "try")
in (let _179_283 = (let _179_282 = (FSharp_Format.text "begin")
in (_179_282)::[])
in (_179_284)::_179_283))
in (FSharp_Format.reduce1 _179_285))
in (let _179_296 = (let _179_295 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _179_294 = (let _179_293 = (let _179_289 = (let _179_288 = (FSharp_Format.text "end")
in (let _179_287 = (let _179_286 = (FSharp_Format.text "with")
in (_179_286)::[])
in (_179_288)::_179_287))
in (FSharp_Format.reduce1 _179_289))
in (let _179_292 = (let _179_291 = (let _179_290 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _179_290))
in (_179_291)::[])
in (_179_293)::_179_292))
in (_179_295)::_179_294))
in (_179_297)::_179_296))
in (FSharp_Format.combine FSharp_Format.hardline _179_298))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule p e1 e2 -> (let _77_394 = (let _179_303 = (as_bin_op p)
in (FStar_Option.get _179_303))
in (match (_77_394) with
| (_77_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _179_306 = (let _179_305 = (let _179_304 = (FSharp_Format.text txt)
in (_179_304)::(e2)::[])
in (e1)::_179_305)
in (FSharp_Format.reduce1 _179_306))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule p e1 -> (let _77_404 = (let _179_310 = (as_uni_op p)
in (FStar_Option.get _179_310))
in (match (_77_404) with
| (_77_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _179_314 = (let _179_313 = (FSharp_Format.text txt)
in (let _179_312 = (let _179_311 = (FSharp_Format.parens e1)
in (_179_311)::[])
in (_179_313)::_179_312))
in (FSharp_Format.reduce1 _179_314))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FSharp_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_317 = (string_of_mlconstant c)
in (FSharp_Format.text _179_317))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _77_421 -> (match (_77_421) with
| (name, p) -> begin
(let _179_326 = (let _179_325 = (let _179_320 = (ptsym currentModule (path, name))
in (FSharp_Format.text _179_320))
in (let _179_324 = (let _179_323 = (FSharp_Format.text "=")
in (let _179_322 = (let _179_321 = (doc_of_pattern currentModule p)
in (_179_321)::[])
in (_179_323)::_179_322))
in (_179_325)::_179_324))
in (FSharp_Format.reduce1 _179_326))
end))
in (let _179_329 = (let _179_328 = (FSharp_Format.text "; ")
in (let _179_327 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _179_328 _179_327)))
in (FSharp_Format.cbrackets _179_329)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _179_331 = (let _179_330 = (as_standard_constructor ctor)
in (FStar_Option.get _179_330))
in (Prims.snd _179_331))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _179_333 = (let _179_332 = (as_standard_constructor ctor)
in (FStar_Option.get _179_332))
in (Prims.snd _179_333))
end else begin
(ptctor currentModule ctor)
end
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _179_339 = (let _179_338 = (doc_of_pattern currentModule x)
in (let _179_337 = (let _179_336 = (FSharp_Format.text "::")
in (let _179_335 = (let _179_334 = (doc_of_pattern currentModule xs)
in (_179_334)::[])
in (_179_336)::_179_335))
in (_179_338)::_179_337))
in (FSharp_Format.reduce _179_339))
end
| (_77_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_77_440)::[]) -> begin
(let _179_344 = (let _179_343 = (FSharp_Format.text name)
in (let _179_342 = (let _179_341 = (let _179_340 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _179_340))
in (_179_341)::[])
in (_179_343)::_179_342))
in (FSharp_Format.reduce1 _179_344))
end
| _77_445 -> begin
(let _179_351 = (let _179_350 = (FSharp_Format.text name)
in (let _179_349 = (let _179_348 = (let _179_347 = (let _179_346 = (FSharp_Format.text ", ")
in (let _179_345 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _179_346 _179_345)))
in (FSharp_Format.parens _179_347))
in (_179_348)::[])
in (_179_350)::_179_349))
in (FSharp_Format.reduce1 _179_351))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _179_353 = (let _179_352 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _179_352 ps))
in (FSharp_Format.parens _179_353)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _179_354 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _179_354 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FSharp_Format.doc = (fun currentModule _77_458 -> (match (_77_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _179_360 = (let _179_359 = (FSharp_Format.text "|")
in (let _179_358 = (let _179_357 = (doc_of_pattern currentModule p)
in (_179_357)::[])
in (_179_359)::_179_358))
in (FSharp_Format.reduce1 _179_360))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _179_366 = (let _179_365 = (FSharp_Format.text "|")
in (let _179_364 = (let _179_363 = (doc_of_pattern currentModule p)
in (let _179_362 = (let _179_361 = (FSharp_Format.text "when")
in (_179_361)::(c)::[])
in (_179_363)::_179_362))
in (_179_365)::_179_364))
in (FSharp_Format.reduce1 _179_366)))
end)
in (let _179_377 = (let _179_376 = (let _179_371 = (let _179_370 = (let _179_369 = (FSharp_Format.text "->")
in (let _179_368 = (let _179_367 = (FSharp_Format.text "begin")
in (_179_367)::[])
in (_179_369)::_179_368))
in (case)::_179_370)
in (FSharp_Format.reduce1 _179_371))
in (let _179_375 = (let _179_374 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _179_373 = (let _179_372 = (FSharp_Format.text "end")
in (_179_372)::[])
in (_179_374)::_179_373))
in (_179_376)::_179_375))
in (FSharp_Format.combine FSharp_Format.hardline _179_377)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FSharp_Format.doc = (fun currentModule _77_468 -> (match (_77_468) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun _77_475 -> (match (_77_475) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _77_472; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (FStar_List.map (fun _77_481 -> (match (_77_481) with
| (x, _77_480) -> begin
(FSharp_Format.text x)
end)) ids)
in (let ty_annot = if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (_77_486::_77_484, _77_489) -> begin
(FSharp_Format.text "")
end
| ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _179_384 = (let _179_383 = (FSharp_Format.text ":")
in (_179_383)::(ty)::[])
in (FSharp_Format.reduce1 _179_384)))
end)
end else begin
if top_level then begin
(match (tys) with
| (_77_498::_77_496, _77_501) -> begin
(FSharp_Format.text "")
end
| ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) (Prims.snd tys))
in (let _179_386 = (let _179_385 = (FSharp_Format.text ":")
in (_179_385)::(ty)::[])
in (FSharp_Format.reduce1 _179_386)))
end)
end else begin
(FSharp_Format.text "")
end
end
in (let _179_393 = (let _179_392 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _179_391 = (let _179_390 = (FSharp_Format.reduce1 ids)
in (let _179_389 = (let _179_388 = (let _179_387 = (FSharp_Format.text "=")
in (_179_387)::(e)::[])
in (ty_annot)::_179_388)
in (_179_390)::_179_389))
in (_179_392)::_179_391))
in (FSharp_Format.reduce1 _179_393))))))
end))
in (let letdoc = if rec_ then begin
(let _179_397 = (let _179_396 = (FSharp_Format.text "let")
in (let _179_395 = (let _179_394 = (FSharp_Format.text "rec")
in (_179_394)::[])
in (_179_396)::_179_395))
in (FSharp_Format.reduce1 _179_397))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _179_401 = (let _179_400 = if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end
in (_179_400)::(doc)::[])
in (FSharp_Format.reduce1 _179_401))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FSharp_Format.doc = (fun currentModule decls -> (let for1 = (fun _77_519 -> (match (_77_519) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _77_524 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _179_410 = (let _179_409 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _179_409 doc))
in (FSharp_Format.parens _179_410)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _77_537 -> (match (_77_537) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _179_417 = (let _179_416 = (let _179_415 = (FSharp_Format.text ":")
in (_179_415)::(ty)::[])
in (name)::_179_416)
in (FSharp_Format.reduce1 _179_417))))
end))
in (let _179_420 = (let _179_419 = (FSharp_Format.text "; ")
in (let _179_418 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _179_419 _179_418)))
in (FSharp_Format.cbrackets _179_420)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _77_545 -> (match (_77_545) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _77_548 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _179_423 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _179_423 tys))
in (let _179_427 = (let _179_426 = (FSharp_Format.text name)
in (let _179_425 = (let _179_424 = (FSharp_Format.text "of")
in (_179_424)::(tys)::[])
in (_179_426)::_179_425))
in (FSharp_Format.reduce1 _179_427))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _179_430 = (let _179_429 = (FSharp_Format.text "|")
in (_179_429)::(d)::[])
in (FSharp_Format.reduce1 _179_430))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _179_434 = (let _179_433 = (let _179_432 = (let _179_431 = (ptsym currentModule ([], x))
in (FSharp_Format.text _179_431))
in (_179_432)::[])
in (tparams)::_179_433)
in (FSharp_Format.reduce1 _179_434))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _179_439 = (let _179_438 = (let _179_437 = (let _179_436 = (let _179_435 = (FSharp_Format.text "=")
in (_179_435)::[])
in (doc)::_179_436)
in (FSharp_Format.reduce1 _179_437))
in (_179_438)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _179_439)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = if ((FStar_List.length doc) > 0) then begin
(let _179_444 = (let _179_443 = (FSharp_Format.text "type")
in (let _179_442 = (let _179_441 = (let _179_440 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _179_440 doc))
in (_179_441)::[])
in (_179_443)::_179_442))
in (FSharp_Format.reduce1 _179_444))
end else begin
(FSharp_Format.text "")
end
in doc))))

let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FSharp_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _179_464 = (let _179_463 = (let _179_456 = (let _179_455 = (FSharp_Format.text "module")
in (let _179_454 = (let _179_453 = (FSharp_Format.text x)
in (let _179_452 = (let _179_451 = (FSharp_Format.text "=")
in (_179_451)::[])
in (_179_453)::_179_452))
in (_179_455)::_179_454))
in (FSharp_Format.reduce1 _179_456))
in (let _179_462 = (let _179_461 = (doc_of_sig currentModule subsig)
in (let _179_460 = (let _179_459 = (let _179_458 = (let _179_457 = (FSharp_Format.text "end")
in (_179_457)::[])
in (FSharp_Format.reduce1 _179_458))
in (_179_459)::[])
in (_179_461)::_179_460))
in (_179_463)::_179_462))
in (FSharp_Format.combine FSharp_Format.hardline _179_464))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _179_468 = (let _179_467 = (FSharp_Format.text "exception")
in (let _179_466 = (let _179_465 = (FSharp_Format.text x)
in (_179_465)::[])
in (_179_467)::_179_466))
in (FSharp_Format.reduce1 _179_468))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _179_470 = (let _179_469 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _179_469 args))
in (FSharp_Format.parens _179_470))
in (let _179_476 = (let _179_475 = (FSharp_Format.text "exception")
in (let _179_474 = (let _179_473 = (FSharp_Format.text x)
in (let _179_472 = (let _179_471 = (FSharp_Format.text "of")
in (_179_471)::(args)::[])
in (_179_473)::_179_472))
in (_179_475)::_179_474))
in (FSharp_Format.reduce1 _179_476))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_77_579, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _179_482 = (let _179_481 = (FSharp_Format.text "val")
in (let _179_480 = (let _179_479 = (FSharp_Format.text x)
in (let _179_478 = (let _179_477 = (FSharp_Format.text ": ")
in (_179_477)::(ty)::[])
in (_179_479)::_179_478))
in (_179_481)::_179_480))
in (FSharp_Format.reduce1 _179_482)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FSharp_Format.doc = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_loc : Prims.int  ->  Prims.string  ->  FSharp_Format.doc = (fun lineno file -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
FSharp_Format.empty
end else begin
(let _179_495 = (let _179_494 = (FSharp_Format.text "#")
in (let _179_493 = (let _179_492 = (FSharp_Format.num lineno)
in (let _179_491 = (let _179_490 = (FSharp_Format.text (Prims.strcat (Prims.strcat "\"" (FStar_Util.replace_string file "\\" "\\\\")) "\""))
in (_179_490)::[])
in (_179_492)::_179_491))
in (_179_494)::_179_493))
in (FSharp_Format.reduce1 _179_495))
end)

let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FSharp_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _179_503 = (let _179_502 = (FSharp_Format.text "exception")
in (let _179_501 = (let _179_500 = (FSharp_Format.text x)
in (_179_500)::[])
in (_179_502)::_179_501))
in (FSharp_Format.reduce1 _179_503))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _179_505 = (let _179_504 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _179_504 args))
in (FSharp_Format.parens _179_505))
in (let _179_511 = (let _179_510 = (FSharp_Format.text "exception")
in (let _179_509 = (let _179_508 = (FSharp_Format.text x)
in (let _179_507 = (let _179_506 = (FSharp_Format.text "of")
in (_179_506)::(args)::[])
in (_179_508)::_179_507))
in (_179_510)::_179_509))
in (FSharp_Format.reduce1 _179_511))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _179_519 = (let _179_518 = (FSharp_Format.text "let")
in (let _179_517 = (let _179_516 = (FSharp_Format.text "_")
in (let _179_515 = (let _179_514 = (FSharp_Format.text "=")
in (let _179_513 = (let _179_512 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_179_512)::[])
in (_179_514)::_179_513))
in (_179_516)::_179_515))
in (_179_518)::_179_517))
in (FSharp_Format.reduce1 _179_519))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (lineno, file) -> begin
(doc_of_loc lineno file)
end))

let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FSharp_Format.doc = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FSharp_Format.doc) Prims.list = (fun _77_624 -> (match (_77_624) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _77_631 -> (match (_77_631) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _179_538 = (let _179_537 = (FSharp_Format.text "module")
in (let _179_536 = (let _179_535 = (FSharp_Format.text x)
in (let _179_534 = (let _179_533 = (FSharp_Format.text ":")
in (let _179_532 = (let _179_531 = (FSharp_Format.text "sig")
in (_179_531)::[])
in (_179_533)::_179_532))
in (_179_535)::_179_534))
in (_179_537)::_179_536))
in (FSharp_Format.reduce1 _179_538))
in (let tail = (let _179_540 = (let _179_539 = (FSharp_Format.text "end")
in (_179_539)::[])
in (FSharp_Format.reduce1 _179_540))
in (let doc = (FStar_Option.map (fun _77_637 -> (match (_77_637) with
| (s, _77_636) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _179_550 = (let _179_549 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _179_548 = (let _179_547 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _179_546 = (let _179_545 = (FSharp_Format.reduce sub)
in (let _179_544 = (let _179_543 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_179_543)::[])
in (_179_545)::_179_544))
in (_179_547)::_179_546))
in (_179_549)::_179_548))
in (FSharp_Format.reduce _179_550)))))))
end))
and for1_mod = (fun istop _77_650 -> (match (_77_650) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _179_563 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _179_555 = (FSharp_Format.text "module")
in (let _179_554 = (let _179_553 = (FSharp_Format.text x)
in (_179_553)::[])
in (_179_555)::_179_554))
end else begin
if (not (istop)) then begin
(let _179_562 = (FSharp_Format.text "module")
in (let _179_561 = (let _179_560 = (FSharp_Format.text x)
in (let _179_559 = (let _179_558 = (FSharp_Format.text "=")
in (let _179_557 = (let _179_556 = (FSharp_Format.text "struct")
in (_179_556)::[])
in (_179_558)::_179_557))
in (_179_560)::_179_559))
in (_179_562)::_179_561))
end else begin
[]
end
end
in (FSharp_Format.reduce1 _179_563))
in (let tail = if (not (istop)) then begin
(let _179_565 = (let _179_564 = (FSharp_Format.text "end")
in (_179_564)::[])
in (FSharp_Format.reduce1 _179_565))
end else begin
(FSharp_Format.reduce1 [])
end
in (let doc = (FStar_Option.map (fun _77_656 -> (match (_77_656) with
| (_77_654, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _179_569 = (let _179_568 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _179_568 FSharp_Format.hardline))
in (_179_569)::[])
end else begin
[]
end
in (let _179_581 = (let _179_580 = (let _179_579 = (let _179_578 = (let _179_577 = (FSharp_Format.text "open Prims")
in (let _179_576 = (let _179_575 = (let _179_574 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _179_573 = (let _179_572 = (FSharp_Format.reduce sub)
in (let _179_571 = (let _179_570 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_179_570)::[])
in (_179_572)::_179_571))
in (_179_574)::_179_573))
in (FSharp_Format.hardline)::_179_575)
in (_179_577)::_179_576))
in (FSharp_Format.hardline)::_179_578)
in (head)::_179_579)
in (FStar_List.append prefix _179_580))
in (FStar_All.pipe_left FSharp_Format.reduce _179_581))))))))
end))
in (let docs = (FStar_List.map (fun _77_668 -> (match (_77_668) with
| (x, s, m) -> begin
(let _179_583 = (for1_mod true (x, s, m))
in (x, _179_583))
end)) mllib)
in docs))
end))

let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FSharp_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun env e -> (let doc = (let _179_590 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _179_590 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun env e -> (let doc = (let _179_595 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _179_595 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





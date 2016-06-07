
open Prims

type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc


let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft (_) -> begin
true
end
| _ -> begin
false
end))


let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight (_) -> begin
true
end
| _ -> begin
false
end))


let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))


let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))


let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
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
| Prefix (_) -> begin
true
end
| _ -> begin
false
end))


let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix (_) -> begin
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
| Infix (_73_4) -> begin
_73_4
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
| ([], _73_9) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_73_19, _73_21) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(

let cg_libs = (FStar_Options.codegen_libs ())
in (

let ns_len = (FStar_List.length ns)
in (

let found = (FStar_Util.find_map cg_libs (fun cg_path -> (

let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(

let _73_32 = (FStar_Util.first_N cg_len ns)
in (match (_73_32) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _163_31 = (let _163_30 = (let _163_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_163_29)::[])
in (FStar_List.append pfx _163_30))
in Some (_163_31))
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
| _73_42 -> begin
(

let _73_45 = x
in (match (_73_45) with
| (ns, x) -> begin
(let _163_36 = (path_of_ns currentModule ns)
in (_163_36, x))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _163_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _163_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(

let _73_51 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_51) with
| (p, s) -> begin
(let _163_46 = (let _163_45 = (let _163_44 = (ptsym_of_symbol s)
in (_163_44)::[])
in (FStar_List.append p _163_45))
in (FStar_String.concat "." _163_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _73_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_56) with
| (p, s) -> begin
(

let s = if ((let _163_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _163_51)) <> (FStar_String.get s 0)) then begin
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


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _73_61 -> (match (_73_61) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_67 -> (match (_73_67) with
| (y, _73_64, _73_66) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _73_71 -> (match (_73_71) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_75 -> (match (_73_75) with
| (y, _73_74) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))


let as_standard_type = (fun _73_79 -> (match (_73_79) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_83 -> (match (_73_83) with
| (y, _73_82) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _73_87 -> (match (_73_87) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_91 -> (match (_73_91) with
| (y, _73_90) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _73_95 inner doc -> (match (_73_95) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let _73_104 = _inner
in (match (_73_104) with
| (pi, fi) -> begin
(

let _73_107 = _outer
in (match (_73_107) with
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
| (_73_131, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_73_135, _73_137) -> begin
false
end))
end))
end)))
in if (noparens inner outer side) then begin
doc
end else begin
(FStar_Format.parens doc)
end)
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _73_1 -> (match (_73_1) with
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
| c -> begin
(fallback c)
end))


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
(let _163_101 = (let _163_100 = (escape_or escape_char_hex c)
in (Prims.strcat "\'" _163_100))
in (Prims.strcat _163_101 "\'"))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| (FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_, FStar_Const.Int8))) | (FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_, FStar_Const.Int16))) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, None) -> begin
if (FStar_Options.use_native_int ()) then begin
s
end else begin
(Prims.strcat (Prims.strcat "(Prims.parse_int \"" s) "\")")
end
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(let _163_103 = (let _163_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat "\"" _163_102))
in (Prims.strcat _163_103 "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _163_105 = (let _163_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat "\"" _163_104))
in (Prims.strcat _163_105 "\""))
end
| _73_203 -> begin
(FStar_All.failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _163_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _163_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (

let doc = (let _163_120 = (let _163_119 = (let _163_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _163_118 doc))
in (FStar_Format.hbox _163_119))
in (FStar_Format.parens _163_120))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(

let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _73_223 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _163_123 = (let _163_122 = (let _163_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _163_121 args))
in (FStar_Format.hbox _163_122))
in (FStar_Format.parens _163_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _163_125 = (let _163_124 = (as_standard_type name)
in (FStar_Option.get _163_124))
in (Prims.snd _163_125))
end else begin
(ptsym currentModule name)
end
in (let _163_129 = (let _163_128 = (let _163_127 = (let _163_126 = (FStar_Format.text name)
in (_163_126)::[])
in (args)::_163_127)
in (FStar_Format.reduce1 _163_128))
in (FStar_Format.hbox _163_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _73_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (

let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _163_134 = (let _163_133 = (let _163_132 = (let _163_131 = (let _163_130 = (FStar_Format.text " -> ")
in (_163_130)::(d2)::[])
in (d1)::_163_131)
in (FStar_Format.reduce1 _163_132))
in (FStar_Format.hbox _163_133))
in (maybe_paren outer t_prio_fun _163_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _163_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _163_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _163_161 = (let _163_160 = (let _163_159 = (FStar_Format.text "Prims.checked_cast")
in (_163_159)::(doc)::[])
in (FStar_Format.reduce _163_160))
in (FStar_Format.parens _163_161))
end else begin
(let _163_166 = (let _163_165 = (let _163_164 = (FStar_Format.text "Obj.magic ")
in (let _163_163 = (let _163_162 = (FStar_Format.parens doc)
in (_163_162)::[])
in (_163_164)::_163_163))
in (FStar_Format.reduce _163_165))
in (FStar_Format.parens _163_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (

let docs = (FStar_List.map (fun d -> (let _163_170 = (let _163_169 = (let _163_168 = (FStar_Format.text ";")
in (_163_168)::(FStar_Format.hardline)::[])
in (d)::_163_169)
in (FStar_Format.reduce _163_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _163_171 = (string_of_mlconstant c)
in (FStar_Format.text _163_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _73_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _163_172 = (ptsym currentModule path)
in (FStar_Format.text _163_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _73_269 -> (match (_73_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _163_179 = (let _163_178 = (let _163_175 = (ptsym currentModule (path, name))
in (FStar_Format.text _163_175))
in (let _163_177 = (let _163_176 = (FStar_Format.text "=")
in (_163_176)::(doc)::[])
in (_163_178)::_163_177))
in (FStar_Format.reduce1 _163_179)))
end))
in (let _163_182 = (let _163_181 = (FStar_Format.text "; ")
in (let _163_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _163_181 _163_180)))
in (FStar_Format.cbrackets _163_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _163_184 = (let _163_183 = (as_standard_constructor ctor)
in (FStar_Option.get _163_183))
in (Prims.snd _163_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _163_186 = (let _163_185 = (as_standard_constructor ctor)
in (FStar_Option.get _163_185))
in (Prims.snd _163_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (

let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _163_190 = (let _163_189 = (FStar_Format.parens x)
in (let _163_188 = (let _163_187 = (FStar_Format.text "::")
in (_163_187)::(xs)::[])
in (_163_189)::_163_188))
in (FStar_Format.reduce _163_190))
end
| (_73_288, _73_290) -> begin
(let _163_196 = (let _163_195 = (FStar_Format.text name)
in (let _163_194 = (let _163_193 = (let _163_192 = (let _163_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _163_191 args))
in (FStar_Format.parens _163_192))
in (_163_193)::[])
in (_163_195)::_163_194))
in (FStar_Format.reduce1 _163_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (

let docs = (let _163_198 = (let _163_197 = (FStar_Format.text ", ")
in (FStar_Format.combine _163_197 docs))
in (FStar_Format.parens _163_198))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _163_201 = (let _163_200 = (let _163_199 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_163_199)::[])
in (FStar_Format.hardline)::_163_200)
in (FStar_Format.reduce _163_201))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule (rec_, false, lets))
in (

let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _163_208 = (let _163_207 = (let _163_206 = (let _163_205 = (let _163_204 = (let _163_203 = (let _163_202 = (FStar_Format.text "in")
in (_163_202)::(body)::[])
in (FStar_Format.reduce1 _163_203))
in (_163_204)::[])
in (doc)::_163_205)
in (pre)::_163_206)
in (FStar_Format.combine FStar_Format.hardline _163_207))
in (FStar_Format.parens _163_208)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (_73_330::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _73_328; FStar_Extraction_ML_Syntax.loc = _73_326}::{FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((arg, _73_318)::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _73_315; FStar_Extraction_ML_Syntax.loc = _73_313}::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _73_345; FStar_Extraction_ML_Syntax.loc = _73_343}, branches); FStar_Extraction_ML_Syntax.mlty = _73_341; FStar_Extraction_ML_Syntax.loc = _73_339} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
branches
end
| e -> begin
((FStar_Extraction_ML_Syntax.MLP_Wild, None, e))::[]
end)
in (doc_of_expr currentModule outer {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Try ((scrutinee, branches)); FStar_Extraction_ML_Syntax.mlty = possible_match.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = possible_match.FStar_Extraction_ML_Syntax.loc}))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _73_364; FStar_Extraction_ML_Syntax.loc = _73_362}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _73_384; FStar_Extraction_ML_Syntax.loc = _73_382}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _73_396 -> begin
(

let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _163_209 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _163_209))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _163_214 = (let _163_213 = (let _163_212 = (FStar_Format.text ".")
in (let _163_211 = (let _163_210 = (FStar_Format.text (Prims.snd f))
in (_163_210)::[])
in (_163_212)::_163_211))
in (e)::_163_213)
in (FStar_Format.reduce _163_214))
end else begin
(let _163_220 = (let _163_219 = (let _163_218 = (FStar_Format.text ".")
in (let _163_217 = (let _163_216 = (let _163_215 = (ptsym currentModule f)
in (FStar_Format.text _163_215))
in (_163_216)::[])
in (_163_218)::_163_217))
in (e)::_163_219)
in (FStar_Format.reduce _163_220))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _163_236 = (let _163_235 = (FStar_Format.text "(")
in (let _163_234 = (let _163_233 = (FStar_Format.text x)
in (let _163_232 = (let _163_231 = (match (xt) with
| Some (xxt) -> begin
(let _163_228 = (let _163_227 = (FStar_Format.text " : ")
in (let _163_226 = (let _163_225 = (doc_of_mltype currentModule outer xxt)
in (_163_225)::[])
in (_163_227)::_163_226))
in (FStar_Format.reduce1 _163_228))
end
| _73_415 -> begin
(FStar_Format.text "")
end)
in (let _163_230 = (let _163_229 = (FStar_Format.text ")")
in (_163_229)::[])
in (_163_231)::_163_230))
in (_163_233)::_163_232))
in (_163_235)::_163_234))
in (FStar_Format.reduce1 _163_236))
end else begin
(FStar_Format.text x)
end)
in (

let ids = (FStar_List.map (fun _73_421 -> (match (_73_421) with
| ((x, _73_418), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (

let doc = (let _163_243 = (let _163_242 = (FStar_Format.text "fun")
in (let _163_241 = (let _163_240 = (FStar_Format.reduce1 ids)
in (let _163_239 = (let _163_238 = (FStar_Format.text "->")
in (_163_238)::(body)::[])
in (_163_240)::_163_239))
in (_163_242)::_163_241))
in (FStar_Format.reduce1 _163_243))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let doc = (let _163_256 = (let _163_255 = (let _163_250 = (let _163_249 = (FStar_Format.text "if")
in (let _163_248 = (let _163_247 = (let _163_246 = (FStar_Format.text "then")
in (let _163_245 = (let _163_244 = (FStar_Format.text "begin")
in (_163_244)::[])
in (_163_246)::_163_245))
in (cond)::_163_247)
in (_163_249)::_163_248))
in (FStar_Format.reduce1 _163_250))
in (let _163_254 = (let _163_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _163_252 = (let _163_251 = (FStar_Format.text "end")
in (_163_251)::[])
in (_163_253)::_163_252))
in (_163_255)::_163_254))
in (FStar_Format.combine FStar_Format.hardline _163_256))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let doc = (let _163_279 = (let _163_278 = (let _163_263 = (let _163_262 = (FStar_Format.text "if")
in (let _163_261 = (let _163_260 = (let _163_259 = (FStar_Format.text "then")
in (let _163_258 = (let _163_257 = (FStar_Format.text "begin")
in (_163_257)::[])
in (_163_259)::_163_258))
in (cond)::_163_260)
in (_163_262)::_163_261))
in (FStar_Format.reduce1 _163_263))
in (let _163_277 = (let _163_276 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _163_275 = (let _163_274 = (let _163_269 = (let _163_268 = (FStar_Format.text "end")
in (let _163_267 = (let _163_266 = (FStar_Format.text "else")
in (let _163_265 = (let _163_264 = (FStar_Format.text "begin")
in (_163_264)::[])
in (_163_266)::_163_265))
in (_163_268)::_163_267))
in (FStar_Format.reduce1 _163_269))
in (let _163_273 = (let _163_272 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _163_271 = (let _163_270 = (FStar_Format.text "end")
in (_163_270)::[])
in (_163_272)::_163_271))
in (_163_274)::_163_273))
in (_163_276)::_163_275))
in (_163_278)::_163_277))
in (FStar_Format.combine FStar_Format.hardline _163_279))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _163_286 = (let _163_285 = (let _163_284 = (FStar_Format.text "match")
in (let _163_283 = (let _163_282 = (FStar_Format.parens cond)
in (let _163_281 = (let _163_280 = (FStar_Format.text "with")
in (_163_280)::[])
in (_163_282)::_163_281))
in (_163_284)::_163_283))
in (FStar_Format.reduce1 _163_285))
in (_163_286)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _163_291 = (let _163_290 = (FStar_Format.text "raise")
in (let _163_289 = (let _163_288 = (let _163_287 = (ptctor currentModule exn)
in (FStar_Format.text _163_287))
in (_163_288)::[])
in (_163_290)::_163_289))
in (FStar_Format.reduce1 _163_291))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _163_300 = (let _163_299 = (FStar_Format.text "raise")
in (let _163_298 = (let _163_297 = (let _163_292 = (ptctor currentModule exn)
in (FStar_Format.text _163_292))
in (let _163_296 = (let _163_295 = (let _163_294 = (let _163_293 = (FStar_Format.text ", ")
in (FStar_Format.combine _163_293 args))
in (FStar_Format.parens _163_294))
in (_163_295)::[])
in (_163_297)::_163_296))
in (_163_299)::_163_298))
in (FStar_Format.reduce1 _163_300)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _163_309 = (let _163_308 = (FStar_Format.text "try")
in (let _163_307 = (let _163_306 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _163_305 = (let _163_304 = (FStar_Format.text "with")
in (let _163_303 = (let _163_302 = (let _163_301 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _163_301))
in (_163_302)::[])
in (_163_304)::_163_303))
in (_163_306)::_163_305))
in (_163_308)::_163_307))
in (FStar_Format.combine FStar_Format.hardline _163_309))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _73_469 = (let _163_314 = (as_bin_op p)
in (FStar_Option.get _163_314))
in (match (_73_469) with
| (_73_466, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (

let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (

let doc = (let _163_317 = (let _163_316 = (let _163_315 = (FStar_Format.text txt)
in (_163_315)::(e2)::[])
in (e1)::_163_316)
in (FStar_Format.reduce1 _163_317))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _73_479 = (let _163_321 = (as_uni_op p)
in (FStar_Option.get _163_321))
in (match (_73_479) with
| (_73_477, txt) -> begin
(

let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (

let doc = (let _163_325 = (let _163_324 = (FStar_Format.text txt)
in (let _163_323 = (let _163_322 = (FStar_Format.parens e1)
in (_163_322)::[])
in (_163_324)::_163_323))
in (FStar_Format.reduce1 _163_325))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _163_328 = (string_of_mlconstant c)
in (FStar_Format.text _163_328))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _73_496 -> (match (_73_496) with
| (name, p) -> begin
(let _163_337 = (let _163_336 = (let _163_331 = (ptsym currentModule (path, name))
in (FStar_Format.text _163_331))
in (let _163_335 = (let _163_334 = (FStar_Format.text "=")
in (let _163_333 = (let _163_332 = (doc_of_pattern currentModule p)
in (_163_332)::[])
in (_163_334)::_163_333))
in (_163_336)::_163_335))
in (FStar_Format.reduce1 _163_337))
end))
in (let _163_340 = (let _163_339 = (FStar_Format.text "; ")
in (let _163_338 = (FStar_List.map for1 fields)
in (FStar_Format.combine _163_339 _163_338)))
in (FStar_Format.cbrackets _163_340)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _163_342 = (let _163_341 = (as_standard_constructor ctor)
in (FStar_Option.get _163_341))
in (Prims.snd _163_342))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _163_344 = (let _163_343 = (as_standard_constructor ctor)
in (FStar_Option.get _163_343))
in (Prims.snd _163_344))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _163_350 = (let _163_349 = (doc_of_pattern currentModule x)
in (let _163_348 = (let _163_347 = (FStar_Format.text "::")
in (let _163_346 = (let _163_345 = (doc_of_pattern currentModule xs)
in (_163_345)::[])
in (_163_347)::_163_346))
in (_163_349)::_163_348))
in (FStar_Format.reduce _163_350))
end
| (_73_513, FStar_Extraction_ML_Syntax.MLP_Tuple (_73_515)::[]) -> begin
(let _163_355 = (let _163_354 = (FStar_Format.text name)
in (let _163_353 = (let _163_352 = (let _163_351 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _163_351))
in (_163_352)::[])
in (_163_354)::_163_353))
in (FStar_Format.reduce1 _163_355))
end
| _73_520 -> begin
(let _163_362 = (let _163_361 = (FStar_Format.text name)
in (let _163_360 = (let _163_359 = (let _163_358 = (let _163_357 = (FStar_Format.text ", ")
in (let _163_356 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _163_357 _163_356)))
in (FStar_Format.parens _163_358))
in (_163_359)::[])
in (_163_361)::_163_360))
in (FStar_Format.reduce1 _163_362))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _163_364 = (let _163_363 = (FStar_Format.text ", ")
in (FStar_Format.combine _163_363 ps))
in (FStar_Format.parens _163_364)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _163_365 = (FStar_Format.text " | ")
in (FStar_Format.combine _163_365 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _73_533 -> (match (_73_533) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _163_371 = (let _163_370 = (FStar_Format.text "|")
in (let _163_369 = (let _163_368 = (doc_of_pattern currentModule p)
in (_163_368)::[])
in (_163_370)::_163_369))
in (FStar_Format.reduce1 _163_371))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _163_377 = (let _163_376 = (FStar_Format.text "|")
in (let _163_375 = (let _163_374 = (doc_of_pattern currentModule p)
in (let _163_373 = (let _163_372 = (FStar_Format.text "when")
in (_163_372)::(c)::[])
in (_163_374)::_163_373))
in (_163_376)::_163_375))
in (FStar_Format.reduce1 _163_377)))
end)
in (let _163_388 = (let _163_387 = (let _163_382 = (let _163_381 = (let _163_380 = (FStar_Format.text "->")
in (let _163_379 = (let _163_378 = (FStar_Format.text "begin")
in (_163_378)::[])
in (_163_380)::_163_379))
in (case)::_163_381)
in (FStar_Format.reduce1 _163_382))
in (let _163_386 = (let _163_385 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _163_384 = (let _163_383 = (FStar_Format.text "end")
in (_163_383)::[])
in (_163_385)::_163_384))
in (_163_387)::_163_386))
in (FStar_Format.combine FStar_Format.hardline _163_388)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _73_543 -> (match (_73_543) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun _73_551 -> (match (_73_551) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _73_548; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun _73_557 -> (match (_73_557) with
| (x, _73_556) -> begin
(FStar_Format.text x)
end)) ids)
in (

let ty_annot = if (not (pt)) then begin
(FStar_Format.text "")
end else begin
if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level)) then begin
(match (tys) with
| (Some (_::_, _)) | (None) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _163_395 = (let _163_394 = (FStar_Format.text ":")
in (_163_394)::(ty)::[])
in (FStar_Format.reduce1 _163_395)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _163_397 = (let _163_396 = (FStar_Format.text ":")
in (_163_396)::(ty)::[])
in (FStar_Format.reduce1 _163_397)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _163_404 = (let _163_403 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _163_402 = (let _163_401 = (FStar_Format.reduce1 ids)
in (let _163_400 = (let _163_399 = (let _163_398 = (FStar_Format.text "=")
in (_163_398)::(e)::[])
in (ty_annot)::_163_399)
in (_163_401)::_163_400))
in (_163_403)::_163_402))
in (FStar_Format.reduce1 _163_404))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(let _163_408 = (let _163_407 = (FStar_Format.text "let")
in (let _163_406 = (let _163_405 = (FStar_Format.text "rec")
in (_163_405)::[])
in (_163_407)::_163_406))
in (FStar_Format.reduce1 _163_408))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _163_412 = (let _163_411 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_163_411)::(doc)::[])
in (FStar_Format.reduce1 _163_412))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _73_597 -> (match (_73_597) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _163_419 = (let _163_418 = (FStar_Format.text "#")
in (let _163_417 = (let _163_416 = (FStar_Format.num lineno)
in (let _163_415 = (let _163_414 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_163_414)::[])
in (_163_416)::_163_415))
in (_163_418)::_163_417))
in (FStar_Format.reduce1 _163_419)))
end
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun _73_605 -> (match (_73_605) with
| (x, tparams, body) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| x::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _73_610 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _163_428 = (let _163_427 = (FStar_Format.text ", ")
in (FStar_Format.combine _163_427 doc))
in (FStar_Format.parens _163_428)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun _73_623 -> (match (_73_623) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _163_435 = (let _163_434 = (let _163_433 = (FStar_Format.text ":")
in (_163_433)::(ty)::[])
in (name)::_163_434)
in (FStar_Format.reduce1 _163_435))))
end))
in (let _163_438 = (let _163_437 = (FStar_Format.text "; ")
in (let _163_436 = (FStar_List.map forfield fields)
in (FStar_Format.combine _163_437 _163_436)))
in (FStar_Format.cbrackets _163_438)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun _73_631 -> (match (_73_631) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _73_634 -> begin
(

let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (

let tys = (let _163_441 = (FStar_Format.text " * ")
in (FStar_Format.combine _163_441 tys))
in (let _163_445 = (let _163_444 = (FStar_Format.text name)
in (let _163_443 = (let _163_442 = (FStar_Format.text "of")
in (_163_442)::(tys)::[])
in (_163_444)::_163_443))
in (FStar_Format.reduce1 _163_445))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _163_448 = (let _163_447 = (FStar_Format.text "|")
in (_163_447)::(d)::[])
in (FStar_Format.reduce1 _163_448))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _163_452 = (let _163_451 = (let _163_450 = (let _163_449 = (ptsym currentModule ([], x))
in (FStar_Format.text _163_449))
in (_163_450)::[])
in (tparams)::_163_451)
in (FStar_Format.reduce1 _163_452))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _163_457 = (let _163_456 = (let _163_455 = (let _163_454 = (let _163_453 = (FStar_Format.text "=")
in (_163_453)::[])
in (doc)::_163_454)
in (FStar_Format.reduce1 _163_455))
in (_163_456)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _163_457)))
end))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > 0) then begin
(let _163_462 = (let _163_461 = (FStar_Format.text "type")
in (let _163_460 = (let _163_459 = (let _163_458 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _163_458 doc))
in (_163_459)::[])
in (_163_461)::_163_460))
in (FStar_Format.reduce1 _163_462))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _163_482 = (let _163_481 = (let _163_474 = (let _163_473 = (FStar_Format.text "module")
in (let _163_472 = (let _163_471 = (FStar_Format.text x)
in (let _163_470 = (let _163_469 = (FStar_Format.text "=")
in (_163_469)::[])
in (_163_471)::_163_470))
in (_163_473)::_163_472))
in (FStar_Format.reduce1 _163_474))
in (let _163_480 = (let _163_479 = (doc_of_sig currentModule subsig)
in (let _163_478 = (let _163_477 = (let _163_476 = (let _163_475 = (FStar_Format.text "end")
in (_163_475)::[])
in (FStar_Format.reduce1 _163_476))
in (_163_477)::[])
in (_163_479)::_163_478))
in (_163_481)::_163_480))
in (FStar_Format.combine FStar_Format.hardline _163_482))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _163_486 = (let _163_485 = (FStar_Format.text "exception")
in (let _163_484 = (let _163_483 = (FStar_Format.text x)
in (_163_483)::[])
in (_163_485)::_163_484))
in (FStar_Format.reduce1 _163_486))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (

let args = (let _163_488 = (let _163_487 = (FStar_Format.text " * ")
in (FStar_Format.combine _163_487 args))
in (FStar_Format.parens _163_488))
in (let _163_494 = (let _163_493 = (FStar_Format.text "exception")
in (let _163_492 = (let _163_491 = (FStar_Format.text x)
in (let _163_490 = (let _163_489 = (FStar_Format.text "of")
in (_163_489)::(args)::[])
in (_163_491)::_163_490))
in (_163_493)::_163_492))
in (FStar_Format.reduce1 _163_494))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_73_665, ty)) -> begin
(

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _163_500 = (let _163_499 = (FStar_Format.text "val")
in (let _163_498 = (let _163_497 = (FStar_Format.text x)
in (let _163_496 = (let _163_495 = (FStar_Format.text ": ")
in (_163_495)::(ty)::[])
in (_163_497)::_163_496))
in (_163_499)::_163_498))
in (FStar_Format.reduce1 _163_500)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (

let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (

let docs = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs))))


let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _163_511 = (let _163_510 = (FStar_Format.text "exception")
in (let _163_509 = (let _163_508 = (FStar_Format.text x)
in (_163_508)::[])
in (_163_510)::_163_509))
in (FStar_Format.reduce1 _163_511))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (

let args = (let _163_513 = (let _163_512 = (FStar_Format.text " * ")
in (FStar_Format.combine _163_512 args))
in (FStar_Format.parens _163_513))
in (let _163_519 = (let _163_518 = (FStar_Format.text "exception")
in (let _163_517 = (let _163_516 = (FStar_Format.text x)
in (let _163_515 = (let _163_514 = (FStar_Format.text "of")
in (_163_514)::(args)::[])
in (_163_516)::_163_515))
in (_163_518)::_163_517))
in (FStar_Format.reduce1 _163_519))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _163_527 = (let _163_526 = (FStar_Format.text "let")
in (let _163_525 = (let _163_524 = (FStar_Format.text "_")
in (let _163_523 = (let _163_522 = (FStar_Format.text "=")
in (let _163_521 = (let _163_520 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_163_520)::[])
in (_163_522)::_163_521))
in (_163_524)::_163_523))
in (_163_526)::_163_525))
in (FStar_Format.reduce1 _163_527))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_73_705) -> begin
FStar_Format.empty
end
| _73_708 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _73_711 -> (match (_73_711) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun _73_718 -> (match (_73_718) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let head = (let _163_546 = (let _163_545 = (FStar_Format.text "module")
in (let _163_544 = (let _163_543 = (FStar_Format.text x)
in (let _163_542 = (let _163_541 = (FStar_Format.text ":")
in (let _163_540 = (let _163_539 = (FStar_Format.text "sig")
in (_163_539)::[])
in (_163_541)::_163_540))
in (_163_543)::_163_542))
in (_163_545)::_163_544))
in (FStar_Format.reduce1 _163_546))
in (

let tail = (let _163_548 = (let _163_547 = (FStar_Format.text "end")
in (_163_547)::[])
in (FStar_Format.reduce1 _163_548))
in (

let doc = (FStar_Option.map (fun _73_724 -> (match (_73_724) with
| (s, _73_723) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _163_558 = (let _163_557 = (FStar_Format.cat head FStar_Format.hardline)
in (let _163_556 = (let _163_555 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _163_554 = (let _163_553 = (FStar_Format.reduce sub)
in (let _163_552 = (let _163_551 = (FStar_Format.cat tail FStar_Format.hardline)
in (_163_551)::[])
in (_163_553)::_163_552))
in (_163_555)::_163_554))
in (_163_557)::_163_556))
in (FStar_Format.reduce _163_558)))))))
end))
and for1_mod = (fun istop _73_737 -> (match (_73_737) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let head = (let _163_571 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _163_563 = (FStar_Format.text "module")
in (let _163_562 = (let _163_561 = (FStar_Format.text x)
in (_163_561)::[])
in (_163_563)::_163_562))
end else begin
if (not (istop)) then begin
(let _163_570 = (FStar_Format.text "module")
in (let _163_569 = (let _163_568 = (FStar_Format.text x)
in (let _163_567 = (let _163_566 = (FStar_Format.text "=")
in (let _163_565 = (let _163_564 = (FStar_Format.text "struct")
in (_163_564)::[])
in (_163_566)::_163_565))
in (_163_568)::_163_567))
in (_163_570)::_163_569))
end else begin
[]
end
end
in (FStar_Format.reduce1 _163_571))
in (

let tail = if (not (istop)) then begin
(let _163_573 = (let _163_572 = (FStar_Format.text "end")
in (_163_572)::[])
in (FStar_Format.reduce1 _163_573))
end else begin
(FStar_Format.reduce1 [])
end
in (

let doc = (FStar_Option.map (fun _73_743 -> (match (_73_743) with
| (_73_741, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _163_577 = (let _163_576 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _163_576 FStar_Format.hardline))
in (_163_577)::[])
end else begin
[]
end
in (let _163_589 = (let _163_588 = (let _163_587 = (let _163_586 = (let _163_585 = (FStar_Format.text "open Prims")
in (let _163_584 = (let _163_583 = (let _163_582 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _163_581 = (let _163_580 = (FStar_Format.reduce sub)
in (let _163_579 = (let _163_578 = (FStar_Format.cat tail FStar_Format.hardline)
in (_163_578)::[])
in (_163_580)::_163_579))
in (_163_582)::_163_581))
in (FStar_Format.hardline)::_163_583)
in (_163_585)::_163_584))
in (FStar_Format.hardline)::_163_586)
in (head)::_163_587)
in (FStar_List.append prefix _163_588))
in (FStar_All.pipe_left FStar_Format.reduce _163_589))))))))
end))
in (

let docs = (FStar_List.map (fun _73_755 -> (match (_73_755) with
| (x, s, m) -> begin
(let _163_591 = (for1_mod true (x, s, m))
in (x, _163_591))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _163_598 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _163_598 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _163_603 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _163_603 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))






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
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
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
(let _164_31 = (let _164_30 = (let _164_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_164_29)::[])
in (FStar_List.append pfx _164_30))
in Some (_164_31))
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
(let _164_36 = (path_of_ns currentModule ns)
in (_164_36, x))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _164_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _164_39)) <> (FStar_String.get s 0)) then begin
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
(let _164_46 = (let _164_45 = (let _164_44 = (ptsym_of_symbol s)
in (_164_44)::[])
in (FStar_List.append p _164_45))
in (FStar_String.concat "." _164_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _73_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_56) with
| (p, s) -> begin
(

let s = if ((let _164_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _164_51)) <> (FStar_String.get s 0)) then begin
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
(let _164_101 = (let _164_100 = (escape_or escape_char_hex c)
in (Prims.strcat "\'" _164_100))
in (Prims.strcat _164_101 "\'"))
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
(let _164_103 = (let _164_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat "\"" _164_102))
in (Prims.strcat _164_103 "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _164_105 = (let _164_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat "\"" _164_104))
in (Prims.strcat _164_105 "\""))
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
in (let _164_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _164_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (

let doc = (let _164_120 = (let _164_119 = (let _164_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _164_118 doc))
in (FStar_Format.hbox _164_119))
in (FStar_Format.parens _164_120))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(

let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| (arg)::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _73_223 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _164_123 = (let _164_122 = (let _164_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _164_121 args))
in (FStar_Format.hbox _164_122))
in (FStar_Format.parens _164_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _164_125 = (let _164_124 = (as_standard_type name)
in (FStar_Option.get _164_124))
in (Prims.snd _164_125))
end else begin
(ptsym currentModule name)
end
in (let _164_129 = (let _164_128 = (let _164_127 = (let _164_126 = (FStar_Format.text name)
in (_164_126)::[])
in (args)::_164_127)
in (FStar_Format.reduce1 _164_128))
in (FStar_Format.hbox _164_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _73_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (

let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _164_134 = (let _164_133 = (let _164_132 = (let _164_131 = (let _164_130 = (FStar_Format.text " -> ")
in (_164_130)::(d2)::[])
in (d1)::_164_131)
in (FStar_Format.reduce1 _164_132))
in (FStar_Format.hbox _164_133))
in (maybe_paren outer t_prio_fun _164_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _164_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _164_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _164_161 = (let _164_160 = (let _164_159 = (FStar_Format.text "Prims.checked_cast")
in (_164_159)::(doc)::[])
in (FStar_Format.reduce _164_160))
in (FStar_Format.parens _164_161))
end else begin
(let _164_166 = (let _164_165 = (let _164_164 = (FStar_Format.text "Obj.magic ")
in (let _164_163 = (let _164_162 = (FStar_Format.parens doc)
in (_164_162)::[])
in (_164_164)::_164_163))
in (FStar_Format.reduce _164_165))
in (FStar_Format.parens _164_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (

let docs = (FStar_List.map (fun d -> (let _164_170 = (let _164_169 = (let _164_168 = (FStar_Format.text ";")
in (_164_168)::(FStar_Format.hardline)::[])
in (d)::_164_169)
in (FStar_Format.reduce _164_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _164_171 = (string_of_mlconstant c)
in (FStar_Format.text _164_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _73_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _164_172 = (ptsym currentModule path)
in (FStar_Format.text _164_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _73_269 -> (match (_73_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _164_179 = (let _164_178 = (let _164_175 = (ptsym currentModule (path, name))
in (FStar_Format.text _164_175))
in (let _164_177 = (let _164_176 = (FStar_Format.text "=")
in (_164_176)::(doc)::[])
in (_164_178)::_164_177))
in (FStar_Format.reduce1 _164_179)))
end))
in (let _164_182 = (let _164_181 = (FStar_Format.text "; ")
in (let _164_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _164_181 _164_180)))
in (FStar_Format.cbrackets _164_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _164_184 = (let _164_183 = (as_standard_constructor ctor)
in (FStar_Option.get _164_183))
in (Prims.snd _164_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _164_186 = (let _164_185 = (as_standard_constructor ctor)
in (FStar_Option.get _164_185))
in (Prims.snd _164_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (

let doc = (match ((name, args)) with
| ("::", (x)::(xs)::[]) -> begin
(let _164_190 = (let _164_189 = (FStar_Format.parens x)
in (let _164_188 = (let _164_187 = (FStar_Format.text "::")
in (_164_187)::(xs)::[])
in (_164_189)::_164_188))
in (FStar_Format.reduce _164_190))
end
| (_73_288, _73_290) -> begin
(let _164_196 = (let _164_195 = (FStar_Format.text name)
in (let _164_194 = (let _164_193 = (let _164_192 = (let _164_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _164_191 args))
in (FStar_Format.parens _164_192))
in (_164_193)::[])
in (_164_195)::_164_194))
in (FStar_Format.reduce1 _164_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (

let docs = (let _164_198 = (let _164_197 = (FStar_Format.text ", ")
in (FStar_Format.combine _164_197 docs))
in (FStar_Format.parens _164_198))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _164_201 = (let _164_200 = (let _164_199 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_164_199)::[])
in (FStar_Format.hardline)::_164_200)
in (FStar_Format.reduce _164_201))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule (rec_, false, lets))
in (

let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _164_208 = (let _164_207 = (let _164_206 = (let _164_205 = (let _164_204 = (let _164_203 = (let _164_202 = (FStar_Format.text "in")
in (_164_202)::(body)::[])
in (FStar_Format.reduce1 _164_203))
in (_164_204)::[])
in (doc)::_164_205)
in (pre)::_164_206)
in (FStar_Format.combine FStar_Format.hardline _164_207))
in (FStar_Format.parens _164_208)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((_73_330)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _73_328; FStar_Extraction_ML_Syntax.loc = _73_326})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, _73_318))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _73_315; FStar_Extraction_ML_Syntax.loc = _73_313})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::(e2)::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _73_364; FStar_Extraction_ML_Syntax.loc = _73_362}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _73_384; FStar_Extraction_ML_Syntax.loc = _73_382}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _73_396 -> begin
(

let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _164_209 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _164_209))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _164_214 = (let _164_213 = (let _164_212 = (FStar_Format.text ".")
in (let _164_211 = (let _164_210 = (FStar_Format.text (Prims.snd f))
in (_164_210)::[])
in (_164_212)::_164_211))
in (e)::_164_213)
in (FStar_Format.reduce _164_214))
end else begin
(let _164_220 = (let _164_219 = (let _164_218 = (FStar_Format.text ".")
in (let _164_217 = (let _164_216 = (let _164_215 = (ptsym currentModule f)
in (FStar_Format.text _164_215))
in (_164_216)::[])
in (_164_218)::_164_217))
in (e)::_164_219)
in (FStar_Format.reduce _164_220))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _164_236 = (let _164_235 = (FStar_Format.text "(")
in (let _164_234 = (let _164_233 = (FStar_Format.text x)
in (let _164_232 = (let _164_231 = (match (xt) with
| Some (xxt) -> begin
(let _164_228 = (let _164_227 = (FStar_Format.text " : ")
in (let _164_226 = (let _164_225 = (doc_of_mltype currentModule outer xxt)
in (_164_225)::[])
in (_164_227)::_164_226))
in (FStar_Format.reduce1 _164_228))
end
| _73_415 -> begin
(FStar_Format.text "")
end)
in (let _164_230 = (let _164_229 = (FStar_Format.text ")")
in (_164_229)::[])
in (_164_231)::_164_230))
in (_164_233)::_164_232))
in (_164_235)::_164_234))
in (FStar_Format.reduce1 _164_236))
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

let doc = (let _164_243 = (let _164_242 = (FStar_Format.text "fun")
in (let _164_241 = (let _164_240 = (FStar_Format.reduce1 ids)
in (let _164_239 = (let _164_238 = (FStar_Format.text "->")
in (_164_238)::(body)::[])
in (_164_240)::_164_239))
in (_164_242)::_164_241))
in (FStar_Format.reduce1 _164_243))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let doc = (let _164_256 = (let _164_255 = (let _164_250 = (let _164_249 = (FStar_Format.text "if")
in (let _164_248 = (let _164_247 = (let _164_246 = (FStar_Format.text "then")
in (let _164_245 = (let _164_244 = (FStar_Format.text "begin")
in (_164_244)::[])
in (_164_246)::_164_245))
in (cond)::_164_247)
in (_164_249)::_164_248))
in (FStar_Format.reduce1 _164_250))
in (let _164_254 = (let _164_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _164_252 = (let _164_251 = (FStar_Format.text "end")
in (_164_251)::[])
in (_164_253)::_164_252))
in (_164_255)::_164_254))
in (FStar_Format.combine FStar_Format.hardline _164_256))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let doc = (let _164_279 = (let _164_278 = (let _164_263 = (let _164_262 = (FStar_Format.text "if")
in (let _164_261 = (let _164_260 = (let _164_259 = (FStar_Format.text "then")
in (let _164_258 = (let _164_257 = (FStar_Format.text "begin")
in (_164_257)::[])
in (_164_259)::_164_258))
in (cond)::_164_260)
in (_164_262)::_164_261))
in (FStar_Format.reduce1 _164_263))
in (let _164_277 = (let _164_276 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _164_275 = (let _164_274 = (let _164_269 = (let _164_268 = (FStar_Format.text "end")
in (let _164_267 = (let _164_266 = (FStar_Format.text "else")
in (let _164_265 = (let _164_264 = (FStar_Format.text "begin")
in (_164_264)::[])
in (_164_266)::_164_265))
in (_164_268)::_164_267))
in (FStar_Format.reduce1 _164_269))
in (let _164_273 = (let _164_272 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _164_271 = (let _164_270 = (FStar_Format.text "end")
in (_164_270)::[])
in (_164_272)::_164_271))
in (_164_274)::_164_273))
in (_164_276)::_164_275))
in (_164_278)::_164_277))
in (FStar_Format.combine FStar_Format.hardline _164_279))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _164_286 = (let _164_285 = (let _164_284 = (FStar_Format.text "match")
in (let _164_283 = (let _164_282 = (FStar_Format.parens cond)
in (let _164_281 = (let _164_280 = (FStar_Format.text "with")
in (_164_280)::[])
in (_164_282)::_164_281))
in (_164_284)::_164_283))
in (FStar_Format.reduce1 _164_285))
in (_164_286)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _164_291 = (let _164_290 = (FStar_Format.text "raise")
in (let _164_289 = (let _164_288 = (let _164_287 = (ptctor currentModule exn)
in (FStar_Format.text _164_287))
in (_164_288)::[])
in (_164_290)::_164_289))
in (FStar_Format.reduce1 _164_291))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _164_300 = (let _164_299 = (FStar_Format.text "raise")
in (let _164_298 = (let _164_297 = (let _164_292 = (ptctor currentModule exn)
in (FStar_Format.text _164_292))
in (let _164_296 = (let _164_295 = (let _164_294 = (let _164_293 = (FStar_Format.text ", ")
in (FStar_Format.combine _164_293 args))
in (FStar_Format.parens _164_294))
in (_164_295)::[])
in (_164_297)::_164_296))
in (_164_299)::_164_298))
in (FStar_Format.reduce1 _164_300)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _164_309 = (let _164_308 = (FStar_Format.text "try")
in (let _164_307 = (let _164_306 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _164_305 = (let _164_304 = (FStar_Format.text "with")
in (let _164_303 = (let _164_302 = (let _164_301 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _164_301))
in (_164_302)::[])
in (_164_304)::_164_303))
in (_164_306)::_164_305))
in (_164_308)::_164_307))
in (FStar_Format.combine FStar_Format.hardline _164_309))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _73_469 = (let _164_314 = (as_bin_op p)
in (FStar_Option.get _164_314))
in (match (_73_469) with
| (_73_466, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (

let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (

let doc = (let _164_317 = (let _164_316 = (let _164_315 = (FStar_Format.text txt)
in (_164_315)::(e2)::[])
in (e1)::_164_316)
in (FStar_Format.reduce1 _164_317))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _73_479 = (let _164_321 = (as_uni_op p)
in (FStar_Option.get _164_321))
in (match (_73_479) with
| (_73_477, txt) -> begin
(

let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (

let doc = (let _164_325 = (let _164_324 = (FStar_Format.text txt)
in (let _164_323 = (let _164_322 = (FStar_Format.parens e1)
in (_164_322)::[])
in (_164_324)::_164_323))
in (FStar_Format.reduce1 _164_325))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _164_328 = (string_of_mlconstant c)
in (FStar_Format.text _164_328))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _73_496 -> (match (_73_496) with
| (name, p) -> begin
(let _164_337 = (let _164_336 = (let _164_331 = (ptsym currentModule (path, name))
in (FStar_Format.text _164_331))
in (let _164_335 = (let _164_334 = (FStar_Format.text "=")
in (let _164_333 = (let _164_332 = (doc_of_pattern currentModule p)
in (_164_332)::[])
in (_164_334)::_164_333))
in (_164_336)::_164_335))
in (FStar_Format.reduce1 _164_337))
end))
in (let _164_340 = (let _164_339 = (FStar_Format.text "; ")
in (let _164_338 = (FStar_List.map for1 fields)
in (FStar_Format.combine _164_339 _164_338)))
in (FStar_Format.cbrackets _164_340)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _164_342 = (let _164_341 = (as_standard_constructor ctor)
in (FStar_Option.get _164_341))
in (Prims.snd _164_342))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _164_344 = (let _164_343 = (as_standard_constructor ctor)
in (FStar_Option.get _164_343))
in (Prims.snd _164_344))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match ((name, pats)) with
| ("::", (x)::(xs)::[]) -> begin
(let _164_351 = (let _164_350 = (let _164_345 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _164_345))
in (let _164_349 = (let _164_348 = (FStar_Format.text "::")
in (let _164_347 = (let _164_346 = (doc_of_pattern currentModule xs)
in (_164_346)::[])
in (_164_348)::_164_347))
in (_164_350)::_164_349))
in (FStar_Format.reduce _164_351))
end
| (_73_513, (FStar_Extraction_ML_Syntax.MLP_Tuple (_73_515))::[]) -> begin
(let _164_356 = (let _164_355 = (FStar_Format.text name)
in (let _164_354 = (let _164_353 = (let _164_352 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _164_352))
in (_164_353)::[])
in (_164_355)::_164_354))
in (FStar_Format.reduce1 _164_356))
end
| _73_520 -> begin
(let _164_363 = (let _164_362 = (FStar_Format.text name)
in (let _164_361 = (let _164_360 = (let _164_359 = (let _164_358 = (FStar_Format.text ", ")
in (let _164_357 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _164_358 _164_357)))
in (FStar_Format.parens _164_359))
in (_164_360)::[])
in (_164_362)::_164_361))
in (FStar_Format.reduce1 _164_363))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _164_365 = (let _164_364 = (FStar_Format.text ", ")
in (FStar_Format.combine _164_364 ps))
in (FStar_Format.parens _164_365)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _164_366 = (FStar_Format.text " | ")
in (FStar_Format.combine _164_366 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _73_533 -> (match (_73_533) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _164_372 = (let _164_371 = (FStar_Format.text "|")
in (let _164_370 = (let _164_369 = (doc_of_pattern currentModule p)
in (_164_369)::[])
in (_164_371)::_164_370))
in (FStar_Format.reduce1 _164_372))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _164_378 = (let _164_377 = (FStar_Format.text "|")
in (let _164_376 = (let _164_375 = (doc_of_pattern currentModule p)
in (let _164_374 = (let _164_373 = (FStar_Format.text "when")
in (_164_373)::(c)::[])
in (_164_375)::_164_374))
in (_164_377)::_164_376))
in (FStar_Format.reduce1 _164_378)))
end)
in (let _164_389 = (let _164_388 = (let _164_383 = (let _164_382 = (let _164_381 = (FStar_Format.text "->")
in (let _164_380 = (let _164_379 = (FStar_Format.text "begin")
in (_164_379)::[])
in (_164_381)::_164_380))
in (case)::_164_382)
in (FStar_Format.reduce1 _164_383))
in (let _164_387 = (let _164_386 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _164_385 = (let _164_384 = (FStar_Format.text "end")
in (_164_384)::[])
in (_164_386)::_164_385))
in (_164_388)::_164_387))
in (FStar_Format.combine FStar_Format.hardline _164_389)))
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
| (Some ((_)::_, _)) | (None) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _164_396 = (let _164_395 = (FStar_Format.text ":")
in (_164_395)::(ty)::[])
in (FStar_Format.reduce1 _164_396)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some ((_)::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _164_398 = (let _164_397 = (FStar_Format.text ":")
in (_164_397)::(ty)::[])
in (FStar_Format.reduce1 _164_398)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _164_405 = (let _164_404 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _164_403 = (let _164_402 = (FStar_Format.reduce1 ids)
in (let _164_401 = (let _164_400 = (let _164_399 = (FStar_Format.text "=")
in (_164_399)::(e)::[])
in (ty_annot)::_164_400)
in (_164_402)::_164_401))
in (_164_404)::_164_403))
in (FStar_Format.reduce1 _164_405))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(let _164_409 = (let _164_408 = (FStar_Format.text "let")
in (let _164_407 = (let _164_406 = (FStar_Format.text "rec")
in (_164_406)::[])
in (_164_408)::_164_407))
in (FStar_Format.reduce1 _164_409))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _164_413 = (let _164_412 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_164_412)::(doc)::[])
in (FStar_Format.reduce1 _164_413))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _73_597 -> (match (_73_597) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _164_420 = (let _164_419 = (FStar_Format.text "#")
in (let _164_418 = (let _164_417 = (FStar_Format.num lineno)
in (let _164_416 = (let _164_415 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_164_415)::[])
in (_164_417)::_164_416))
in (_164_419)::_164_418))
in (FStar_Format.reduce1 _164_420)))
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
| (x)::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _73_610 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _164_429 = (let _164_428 = (FStar_Format.text ", ")
in (FStar_Format.combine _164_428 doc))
in (FStar_Format.parens _164_429)))
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
in (let _164_436 = (let _164_435 = (let _164_434 = (FStar_Format.text ":")
in (_164_434)::(ty)::[])
in (name)::_164_435)
in (FStar_Format.reduce1 _164_436))))
end))
in (let _164_439 = (let _164_438 = (FStar_Format.text "; ")
in (let _164_437 = (FStar_List.map forfield fields)
in (FStar_Format.combine _164_438 _164_437)))
in (FStar_Format.cbrackets _164_439)))
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

let tys = (let _164_442 = (FStar_Format.text " * ")
in (FStar_Format.combine _164_442 tys))
in (let _164_446 = (let _164_445 = (FStar_Format.text name)
in (let _164_444 = (let _164_443 = (FStar_Format.text "of")
in (_164_443)::(tys)::[])
in (_164_445)::_164_444))
in (FStar_Format.reduce1 _164_446))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _164_449 = (let _164_448 = (FStar_Format.text "|")
in (_164_448)::(d)::[])
in (FStar_Format.reduce1 _164_449))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _164_453 = (let _164_452 = (let _164_451 = (let _164_450 = (ptsym currentModule ([], x))
in (FStar_Format.text _164_450))
in (_164_451)::[])
in (tparams)::_164_452)
in (FStar_Format.reduce1 _164_453))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _164_458 = (let _164_457 = (let _164_456 = (let _164_455 = (let _164_454 = (FStar_Format.text "=")
in (_164_454)::[])
in (doc)::_164_455)
in (FStar_Format.reduce1 _164_456))
in (_164_457)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _164_458)))
end))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > 0) then begin
(let _164_463 = (let _164_462 = (FStar_Format.text "type")
in (let _164_461 = (let _164_460 = (let _164_459 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _164_459 doc))
in (_164_460)::[])
in (_164_462)::_164_461))
in (FStar_Format.reduce1 _164_463))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _164_483 = (let _164_482 = (let _164_475 = (let _164_474 = (FStar_Format.text "module")
in (let _164_473 = (let _164_472 = (FStar_Format.text x)
in (let _164_471 = (let _164_470 = (FStar_Format.text "=")
in (_164_470)::[])
in (_164_472)::_164_471))
in (_164_474)::_164_473))
in (FStar_Format.reduce1 _164_475))
in (let _164_481 = (let _164_480 = (doc_of_sig currentModule subsig)
in (let _164_479 = (let _164_478 = (let _164_477 = (let _164_476 = (FStar_Format.text "end")
in (_164_476)::[])
in (FStar_Format.reduce1 _164_477))
in (_164_478)::[])
in (_164_480)::_164_479))
in (_164_482)::_164_481))
in (FStar_Format.combine FStar_Format.hardline _164_483))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _164_487 = (let _164_486 = (FStar_Format.text "exception")
in (let _164_485 = (let _164_484 = (FStar_Format.text x)
in (_164_484)::[])
in (_164_486)::_164_485))
in (FStar_Format.reduce1 _164_487))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (

let args = (let _164_489 = (let _164_488 = (FStar_Format.text " * ")
in (FStar_Format.combine _164_488 args))
in (FStar_Format.parens _164_489))
in (let _164_495 = (let _164_494 = (FStar_Format.text "exception")
in (let _164_493 = (let _164_492 = (FStar_Format.text x)
in (let _164_491 = (let _164_490 = (FStar_Format.text "of")
in (_164_490)::(args)::[])
in (_164_492)::_164_491))
in (_164_494)::_164_493))
in (FStar_Format.reduce1 _164_495))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_73_665, ty)) -> begin
(

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _164_501 = (let _164_500 = (FStar_Format.text "val")
in (let _164_499 = (let _164_498 = (FStar_Format.text x)
in (let _164_497 = (let _164_496 = (FStar_Format.text ": ")
in (_164_496)::(ty)::[])
in (_164_498)::_164_497))
in (_164_500)::_164_499))
in (FStar_Format.reduce1 _164_501)))
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
(let _164_512 = (let _164_511 = (FStar_Format.text "exception")
in (let _164_510 = (let _164_509 = (FStar_Format.text x)
in (_164_509)::[])
in (_164_511)::_164_510))
in (FStar_Format.reduce1 _164_512))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (

let args = (let _164_514 = (let _164_513 = (FStar_Format.text " * ")
in (FStar_Format.combine _164_513 args))
in (FStar_Format.parens _164_514))
in (let _164_520 = (let _164_519 = (FStar_Format.text "exception")
in (let _164_518 = (let _164_517 = (FStar_Format.text x)
in (let _164_516 = (let _164_515 = (FStar_Format.text "of")
in (_164_515)::(args)::[])
in (_164_517)::_164_516))
in (_164_519)::_164_518))
in (FStar_Format.reduce1 _164_520))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _164_528 = (let _164_527 = (FStar_Format.text "let")
in (let _164_526 = (let _164_525 = (FStar_Format.text "_")
in (let _164_524 = (let _164_523 = (FStar_Format.text "=")
in (let _164_522 = (let _164_521 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_164_521)::[])
in (_164_523)::_164_522))
in (_164_525)::_164_524))
in (_164_527)::_164_526))
in (FStar_Format.reduce1 _164_528))
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

let head = (let _164_547 = (let _164_546 = (FStar_Format.text "module")
in (let _164_545 = (let _164_544 = (FStar_Format.text x)
in (let _164_543 = (let _164_542 = (FStar_Format.text ":")
in (let _164_541 = (let _164_540 = (FStar_Format.text "sig")
in (_164_540)::[])
in (_164_542)::_164_541))
in (_164_544)::_164_543))
in (_164_546)::_164_545))
in (FStar_Format.reduce1 _164_547))
in (

let tail = (let _164_549 = (let _164_548 = (FStar_Format.text "end")
in (_164_548)::[])
in (FStar_Format.reduce1 _164_549))
in (

let doc = (FStar_Option.map (fun _73_724 -> (match (_73_724) with
| (s, _73_723) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _164_559 = (let _164_558 = (FStar_Format.cat head FStar_Format.hardline)
in (let _164_557 = (let _164_556 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _164_555 = (let _164_554 = (FStar_Format.reduce sub)
in (let _164_553 = (let _164_552 = (FStar_Format.cat tail FStar_Format.hardline)
in (_164_552)::[])
in (_164_554)::_164_553))
in (_164_556)::_164_555))
in (_164_558)::_164_557))
in (FStar_Format.reduce _164_559)))))))
end))
and for1_mod = (fun istop _73_737 -> (match (_73_737) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let head = (let _164_572 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _164_564 = (FStar_Format.text "module")
in (let _164_563 = (let _164_562 = (FStar_Format.text x)
in (_164_562)::[])
in (_164_564)::_164_563))
end else begin
if (not (istop)) then begin
(let _164_571 = (FStar_Format.text "module")
in (let _164_570 = (let _164_569 = (FStar_Format.text x)
in (let _164_568 = (let _164_567 = (FStar_Format.text "=")
in (let _164_566 = (let _164_565 = (FStar_Format.text "struct")
in (_164_565)::[])
in (_164_567)::_164_566))
in (_164_569)::_164_568))
in (_164_571)::_164_570))
end else begin
[]
end
end
in (FStar_Format.reduce1 _164_572))
in (

let tail = if (not (istop)) then begin
(let _164_574 = (let _164_573 = (FStar_Format.text "end")
in (_164_573)::[])
in (FStar_Format.reduce1 _164_574))
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
(let _164_578 = (let _164_577 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _164_577 FStar_Format.hardline))
in (_164_578)::[])
end else begin
[]
end
in (let _164_590 = (let _164_589 = (let _164_588 = (let _164_587 = (let _164_586 = (FStar_Format.text "open Prims")
in (let _164_585 = (let _164_584 = (let _164_583 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _164_582 = (let _164_581 = (FStar_Format.reduce sub)
in (let _164_580 = (let _164_579 = (FStar_Format.cat tail FStar_Format.hardline)
in (_164_579)::[])
in (_164_581)::_164_580))
in (_164_583)::_164_582))
in (FStar_Format.hardline)::_164_584)
in (_164_586)::_164_585))
in (FStar_Format.hardline)::_164_587)
in (head)::_164_588)
in (FStar_List.append prefix _164_589))
in (FStar_All.pipe_left FStar_Format.reduce _164_590))))))))
end))
in (

let docs = (FStar_List.map (fun _73_755 -> (match (_73_755) with
| (x, s, m) -> begin
(let _164_592 = (for1_mod true (x, s, m))
in (x, _164_592))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _164_599 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _164_599 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _164_604 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _164_604 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))





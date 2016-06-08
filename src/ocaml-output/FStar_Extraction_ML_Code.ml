
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
(let _162_31 = (let _162_30 = (let _162_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_162_29)::[])
in (FStar_List.append pfx _162_30))
in Some (_162_31))
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
(let _162_36 = (path_of_ns currentModule ns)
in (_162_36, x))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _162_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _162_39)) <> (FStar_String.get s 0)) then begin
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
(let _162_46 = (let _162_45 = (let _162_44 = (ptsym_of_symbol s)
in (_162_44)::[])
in (FStar_List.append p _162_45))
in (FStar_String.concat "." _162_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _73_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_56) with
| (p, s) -> begin
(

let s = if ((let _162_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _162_51)) <> (FStar_String.get s 0)) then begin
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
(let _162_101 = (let _162_100 = (escape_or escape_char_hex c)
in (Prims.strcat "\'" _162_100))
in (Prims.strcat _162_101 "\'"))
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
(let _162_103 = (let _162_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat "\"" _162_102))
in (Prims.strcat _162_103 "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _162_105 = (let _162_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat "\"" _162_104))
in (Prims.strcat _162_105 "\""))
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
in (let _162_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _162_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (

let doc = (let _162_120 = (let _162_119 = (let _162_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_118 doc))
in (FStar_Format.hbox _162_119))
in (FStar_Format.parens _162_120))
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
in (let _162_123 = (let _162_122 = (let _162_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_121 args))
in (FStar_Format.hbox _162_122))
in (FStar_Format.parens _162_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _162_125 = (let _162_124 = (as_standard_type name)
in (FStar_Option.get _162_124))
in (Prims.snd _162_125))
end else begin
(ptsym currentModule name)
end
in (let _162_129 = (let _162_128 = (let _162_127 = (let _162_126 = (FStar_Format.text name)
in (_162_126)::[])
in (args)::_162_127)
in (FStar_Format.reduce1 _162_128))
in (FStar_Format.hbox _162_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _73_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (

let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _162_134 = (let _162_133 = (let _162_132 = (let _162_131 = (let _162_130 = (FStar_Format.text " -> ")
in (_162_130)::(d2)::[])
in (d1)::_162_131)
in (FStar_Format.reduce1 _162_132))
in (FStar_Format.hbox _162_133))
in (maybe_paren outer t_prio_fun _162_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _162_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _162_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_161 = (let _162_160 = (let _162_159 = (FStar_Format.text "Prims.checked_cast")
in (_162_159)::(doc)::[])
in (FStar_Format.reduce _162_160))
in (FStar_Format.parens _162_161))
end else begin
(let _162_166 = (let _162_165 = (let _162_164 = (FStar_Format.text "Obj.magic ")
in (let _162_163 = (let _162_162 = (FStar_Format.parens doc)
in (_162_162)::[])
in (_162_164)::_162_163))
in (FStar_Format.reduce _162_165))
in (FStar_Format.parens _162_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (

let docs = (FStar_List.map (fun d -> (let _162_170 = (let _162_169 = (let _162_168 = (FStar_Format.text ";")
in (_162_168)::(FStar_Format.hardline)::[])
in (d)::_162_169)
in (FStar_Format.reduce _162_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _162_171 = (string_of_mlconstant c)
in (FStar_Format.text _162_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _73_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _162_172 = (ptsym currentModule path)
in (FStar_Format.text _162_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _73_269 -> (match (_73_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_179 = (let _162_178 = (let _162_175 = (ptsym currentModule (path, name))
in (FStar_Format.text _162_175))
in (let _162_177 = (let _162_176 = (FStar_Format.text "=")
in (_162_176)::(doc)::[])
in (_162_178)::_162_177))
in (FStar_Format.reduce1 _162_179)))
end))
in (let _162_182 = (let _162_181 = (FStar_Format.text "; ")
in (let _162_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _162_181 _162_180)))
in (FStar_Format.cbrackets _162_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _162_184 = (let _162_183 = (as_standard_constructor ctor)
in (FStar_Option.get _162_183))
in (Prims.snd _162_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _162_186 = (let _162_185 = (as_standard_constructor ctor)
in (FStar_Option.get _162_185))
in (Prims.snd _162_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (

let doc = (match ((name, args)) with
| ("::", (x)::(xs)::[]) -> begin
(let _162_190 = (let _162_189 = (FStar_Format.parens x)
in (let _162_188 = (let _162_187 = (FStar_Format.text "::")
in (_162_187)::(xs)::[])
in (_162_189)::_162_188))
in (FStar_Format.reduce _162_190))
end
| (_73_288, _73_290) -> begin
(let _162_196 = (let _162_195 = (FStar_Format.text name)
in (let _162_194 = (let _162_193 = (let _162_192 = (let _162_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_191 args))
in (FStar_Format.parens _162_192))
in (_162_193)::[])
in (_162_195)::_162_194))
in (FStar_Format.reduce1 _162_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (

let docs = (let _162_198 = (let _162_197 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_197 docs))
in (FStar_Format.parens _162_198))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _162_201 = (let _162_200 = (let _162_199 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_162_199)::[])
in (FStar_Format.hardline)::_162_200)
in (FStar_Format.reduce _162_201))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule (rec_, false, lets))
in (

let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _162_208 = (let _162_207 = (let _162_206 = (let _162_205 = (let _162_204 = (let _162_203 = (let _162_202 = (FStar_Format.text "in")
in (_162_202)::(body)::[])
in (FStar_Format.reduce1 _162_203))
in (_162_204)::[])
in (doc)::_162_205)
in (pre)::_162_206)
in (FStar_Format.combine FStar_Format.hardline _162_207))
in (FStar_Format.parens _162_208)))))
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
in (let _162_209 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _162_209))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_214 = (let _162_213 = (let _162_212 = (FStar_Format.text ".")
in (let _162_211 = (let _162_210 = (FStar_Format.text (Prims.snd f))
in (_162_210)::[])
in (_162_212)::_162_211))
in (e)::_162_213)
in (FStar_Format.reduce _162_214))
end else begin
(let _162_220 = (let _162_219 = (let _162_218 = (FStar_Format.text ".")
in (let _162_217 = (let _162_216 = (let _162_215 = (ptsym currentModule f)
in (FStar_Format.text _162_215))
in (_162_216)::[])
in (_162_218)::_162_217))
in (e)::_162_219)
in (FStar_Format.reduce _162_220))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_236 = (let _162_235 = (FStar_Format.text "(")
in (let _162_234 = (let _162_233 = (FStar_Format.text x)
in (let _162_232 = (let _162_231 = (match (xt) with
| Some (xxt) -> begin
(let _162_228 = (let _162_227 = (FStar_Format.text " : ")
in (let _162_226 = (let _162_225 = (doc_of_mltype currentModule outer xxt)
in (_162_225)::[])
in (_162_227)::_162_226))
in (FStar_Format.reduce1 _162_228))
end
| _73_415 -> begin
(FStar_Format.text "")
end)
in (let _162_230 = (let _162_229 = (FStar_Format.text ")")
in (_162_229)::[])
in (_162_231)::_162_230))
in (_162_233)::_162_232))
in (_162_235)::_162_234))
in (FStar_Format.reduce1 _162_236))
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

let doc = (let _162_243 = (let _162_242 = (FStar_Format.text "fun")
in (let _162_241 = (let _162_240 = (FStar_Format.reduce1 ids)
in (let _162_239 = (let _162_238 = (FStar_Format.text "->")
in (_162_238)::(body)::[])
in (_162_240)::_162_239))
in (_162_242)::_162_241))
in (FStar_Format.reduce1 _162_243))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let doc = (let _162_256 = (let _162_255 = (let _162_250 = (let _162_249 = (FStar_Format.text "if")
in (let _162_248 = (let _162_247 = (let _162_246 = (FStar_Format.text "then")
in (let _162_245 = (let _162_244 = (FStar_Format.text "begin")
in (_162_244)::[])
in (_162_246)::_162_245))
in (cond)::_162_247)
in (_162_249)::_162_248))
in (FStar_Format.reduce1 _162_250))
in (let _162_254 = (let _162_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _162_252 = (let _162_251 = (FStar_Format.text "end")
in (_162_251)::[])
in (_162_253)::_162_252))
in (_162_255)::_162_254))
in (FStar_Format.combine FStar_Format.hardline _162_256))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let doc = (let _162_279 = (let _162_278 = (let _162_263 = (let _162_262 = (FStar_Format.text "if")
in (let _162_261 = (let _162_260 = (let _162_259 = (FStar_Format.text "then")
in (let _162_258 = (let _162_257 = (FStar_Format.text "begin")
in (_162_257)::[])
in (_162_259)::_162_258))
in (cond)::_162_260)
in (_162_262)::_162_261))
in (FStar_Format.reduce1 _162_263))
in (let _162_277 = (let _162_276 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _162_275 = (let _162_274 = (let _162_269 = (let _162_268 = (FStar_Format.text "end")
in (let _162_267 = (let _162_266 = (FStar_Format.text "else")
in (let _162_265 = (let _162_264 = (FStar_Format.text "begin")
in (_162_264)::[])
in (_162_266)::_162_265))
in (_162_268)::_162_267))
in (FStar_Format.reduce1 _162_269))
in (let _162_273 = (let _162_272 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _162_271 = (let _162_270 = (FStar_Format.text "end")
in (_162_270)::[])
in (_162_272)::_162_271))
in (_162_274)::_162_273))
in (_162_276)::_162_275))
in (_162_278)::_162_277))
in (FStar_Format.combine FStar_Format.hardline _162_279))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _162_286 = (let _162_285 = (let _162_284 = (FStar_Format.text "match")
in (let _162_283 = (let _162_282 = (FStar_Format.parens cond)
in (let _162_281 = (let _162_280 = (FStar_Format.text "with")
in (_162_280)::[])
in (_162_282)::_162_281))
in (_162_284)::_162_283))
in (FStar_Format.reduce1 _162_285))
in (_162_286)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _162_291 = (let _162_290 = (FStar_Format.text "raise")
in (let _162_289 = (let _162_288 = (let _162_287 = (ptctor currentModule exn)
in (FStar_Format.text _162_287))
in (_162_288)::[])
in (_162_290)::_162_289))
in (FStar_Format.reduce1 _162_291))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _162_300 = (let _162_299 = (FStar_Format.text "raise")
in (let _162_298 = (let _162_297 = (let _162_292 = (ptctor currentModule exn)
in (FStar_Format.text _162_292))
in (let _162_296 = (let _162_295 = (let _162_294 = (let _162_293 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_293 args))
in (FStar_Format.parens _162_294))
in (_162_295)::[])
in (_162_297)::_162_296))
in (_162_299)::_162_298))
in (FStar_Format.reduce1 _162_300)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _162_309 = (let _162_308 = (FStar_Format.text "try")
in (let _162_307 = (let _162_306 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_305 = (let _162_304 = (FStar_Format.text "with")
in (let _162_303 = (let _162_302 = (let _162_301 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _162_301))
in (_162_302)::[])
in (_162_304)::_162_303))
in (_162_306)::_162_305))
in (_162_308)::_162_307))
in (FStar_Format.combine FStar_Format.hardline _162_309))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _73_469 = (let _162_314 = (as_bin_op p)
in (FStar_Option.get _162_314))
in (match (_73_469) with
| (_73_466, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (

let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (

let doc = (let _162_317 = (let _162_316 = (let _162_315 = (FStar_Format.text txt)
in (_162_315)::(e2)::[])
in (e1)::_162_316)
in (FStar_Format.reduce1 _162_317))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _73_479 = (let _162_321 = (as_uni_op p)
in (FStar_Option.get _162_321))
in (match (_73_479) with
| (_73_477, txt) -> begin
(

let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (

let doc = (let _162_325 = (let _162_324 = (FStar_Format.text txt)
in (let _162_323 = (let _162_322 = (FStar_Format.parens e1)
in (_162_322)::[])
in (_162_324)::_162_323))
in (FStar_Format.reduce1 _162_325))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _162_328 = (string_of_mlconstant c)
in (FStar_Format.text _162_328))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _73_496 -> (match (_73_496) with
| (name, p) -> begin
(let _162_337 = (let _162_336 = (let _162_331 = (ptsym currentModule (path, name))
in (FStar_Format.text _162_331))
in (let _162_335 = (let _162_334 = (FStar_Format.text "=")
in (let _162_333 = (let _162_332 = (doc_of_pattern currentModule p)
in (_162_332)::[])
in (_162_334)::_162_333))
in (_162_336)::_162_335))
in (FStar_Format.reduce1 _162_337))
end))
in (let _162_340 = (let _162_339 = (FStar_Format.text "; ")
in (let _162_338 = (FStar_List.map for1 fields)
in (FStar_Format.combine _162_339 _162_338)))
in (FStar_Format.cbrackets _162_340)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _162_342 = (let _162_341 = (as_standard_constructor ctor)
in (FStar_Option.get _162_341))
in (Prims.snd _162_342))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _162_344 = (let _162_343 = (as_standard_constructor ctor)
in (FStar_Option.get _162_343))
in (Prims.snd _162_344))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match ((name, pats)) with
| ("::", (x)::(xs)::[]) -> begin
(let _162_351 = (let _162_350 = (let _162_345 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _162_345))
in (let _162_349 = (let _162_348 = (FStar_Format.text "::")
in (let _162_347 = (let _162_346 = (doc_of_pattern currentModule xs)
in (_162_346)::[])
in (_162_348)::_162_347))
in (_162_350)::_162_349))
in (FStar_Format.reduce _162_351))
end
| (_73_513, (FStar_Extraction_ML_Syntax.MLP_Tuple (_73_515))::[]) -> begin
(let _162_356 = (let _162_355 = (FStar_Format.text name)
in (let _162_354 = (let _162_353 = (let _162_352 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _162_352))
in (_162_353)::[])
in (_162_355)::_162_354))
in (FStar_Format.reduce1 _162_356))
end
| _73_520 -> begin
(let _162_363 = (let _162_362 = (FStar_Format.text name)
in (let _162_361 = (let _162_360 = (let _162_359 = (let _162_358 = (FStar_Format.text ", ")
in (let _162_357 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _162_358 _162_357)))
in (FStar_Format.parens _162_359))
in (_162_360)::[])
in (_162_362)::_162_361))
in (FStar_Format.reduce1 _162_363))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _162_365 = (let _162_364 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_364 ps))
in (FStar_Format.parens _162_365)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _162_366 = (FStar_Format.text " | ")
in (FStar_Format.combine _162_366 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _73_533 -> (match (_73_533) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _162_372 = (let _162_371 = (FStar_Format.text "|")
in (let _162_370 = (let _162_369 = (doc_of_pattern currentModule p)
in (_162_369)::[])
in (_162_371)::_162_370))
in (FStar_Format.reduce1 _162_372))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _162_378 = (let _162_377 = (FStar_Format.text "|")
in (let _162_376 = (let _162_375 = (doc_of_pattern currentModule p)
in (let _162_374 = (let _162_373 = (FStar_Format.text "when")
in (_162_373)::(c)::[])
in (_162_375)::_162_374))
in (_162_377)::_162_376))
in (FStar_Format.reduce1 _162_378)))
end)
in (let _162_389 = (let _162_388 = (let _162_383 = (let _162_382 = (let _162_381 = (FStar_Format.text "->")
in (let _162_380 = (let _162_379 = (FStar_Format.text "begin")
in (_162_379)::[])
in (_162_381)::_162_380))
in (case)::_162_382)
in (FStar_Format.reduce1 _162_383))
in (let _162_387 = (let _162_386 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_385 = (let _162_384 = (FStar_Format.text "end")
in (_162_384)::[])
in (_162_386)::_162_385))
in (_162_388)::_162_387))
in (FStar_Format.combine FStar_Format.hardline _162_389)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _73_543 -> (match (_73_543) with
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
if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (Some ((_)::_, _)) | (None) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_396 = (let _162_395 = (FStar_Format.text ":")
in (_162_395)::(ty)::[])
in (FStar_Format.reduce1 _162_396)))
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
in (let _162_398 = (let _162_397 = (FStar_Format.text ":")
in (_162_397)::(ty)::[])
in (FStar_Format.reduce1 _162_398)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _162_405 = (let _162_404 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _162_403 = (let _162_402 = (FStar_Format.reduce1 ids)
in (let _162_401 = (let _162_400 = (let _162_399 = (FStar_Format.text "=")
in (_162_399)::(e)::[])
in (ty_annot)::_162_400)
in (_162_402)::_162_401))
in (_162_404)::_162_403))
in (FStar_Format.reduce1 _162_405))))))
end))
in (

let letdoc = if rec_ then begin
(let _162_409 = (let _162_408 = (FStar_Format.text "let")
in (let _162_407 = (let _162_406 = (FStar_Format.text "rec")
in (_162_406)::[])
in (_162_408)::_162_407))
in (FStar_Format.reduce1 _162_409))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _162_413 = (let _162_412 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_162_412)::(doc)::[])
in (FStar_Format.reduce1 _162_413))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _73_597 -> (match (_73_597) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _162_420 = (let _162_419 = (FStar_Format.text "#")
in (let _162_418 = (let _162_417 = (FStar_Format.num lineno)
in (let _162_416 = (let _162_415 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_162_415)::[])
in (_162_417)::_162_416))
in (_162_419)::_162_418))
in (FStar_Format.reduce1 _162_420)))
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
in (let _162_429 = (let _162_428 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_428 doc))
in (FStar_Format.parens _162_429)))
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
in (let _162_436 = (let _162_435 = (let _162_434 = (FStar_Format.text ":")
in (_162_434)::(ty)::[])
in (name)::_162_435)
in (FStar_Format.reduce1 _162_436))))
end))
in (let _162_439 = (let _162_438 = (FStar_Format.text "; ")
in (let _162_437 = (FStar_List.map forfield fields)
in (FStar_Format.combine _162_438 _162_437)))
in (FStar_Format.cbrackets _162_439)))
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

let tys = (let _162_442 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_442 tys))
in (let _162_446 = (let _162_445 = (FStar_Format.text name)
in (let _162_444 = (let _162_443 = (FStar_Format.text "of")
in (_162_443)::(tys)::[])
in (_162_445)::_162_444))
in (FStar_Format.reduce1 _162_446))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _162_449 = (let _162_448 = (FStar_Format.text "|")
in (_162_448)::(d)::[])
in (FStar_Format.reduce1 _162_449))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _162_453 = (let _162_452 = (let _162_451 = (let _162_450 = (ptsym currentModule ([], x))
in (FStar_Format.text _162_450))
in (_162_451)::[])
in (tparams)::_162_452)
in (FStar_Format.reduce1 _162_453))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _162_458 = (let _162_457 = (let _162_456 = (let _162_455 = (let _162_454 = (FStar_Format.text "=")
in (_162_454)::[])
in (doc)::_162_455)
in (FStar_Format.reduce1 _162_456))
in (_162_457)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _162_458)))
end))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > 0) then begin
(let _162_463 = (let _162_462 = (FStar_Format.text "type")
in (let _162_461 = (let _162_460 = (let _162_459 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _162_459 doc))
in (_162_460)::[])
in (_162_462)::_162_461))
in (FStar_Format.reduce1 _162_463))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _162_483 = (let _162_482 = (let _162_475 = (let _162_474 = (FStar_Format.text "module")
in (let _162_473 = (let _162_472 = (FStar_Format.text x)
in (let _162_471 = (let _162_470 = (FStar_Format.text "=")
in (_162_470)::[])
in (_162_472)::_162_471))
in (_162_474)::_162_473))
in (FStar_Format.reduce1 _162_475))
in (let _162_481 = (let _162_480 = (doc_of_sig currentModule subsig)
in (let _162_479 = (let _162_478 = (let _162_477 = (let _162_476 = (FStar_Format.text "end")
in (_162_476)::[])
in (FStar_Format.reduce1 _162_477))
in (_162_478)::[])
in (_162_480)::_162_479))
in (_162_482)::_162_481))
in (FStar_Format.combine FStar_Format.hardline _162_483))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _162_487 = (let _162_486 = (FStar_Format.text "exception")
in (let _162_485 = (let _162_484 = (FStar_Format.text x)
in (_162_484)::[])
in (_162_486)::_162_485))
in (FStar_Format.reduce1 _162_487))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (

let args = (let _162_489 = (let _162_488 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_488 args))
in (FStar_Format.parens _162_489))
in (let _162_495 = (let _162_494 = (FStar_Format.text "exception")
in (let _162_493 = (let _162_492 = (FStar_Format.text x)
in (let _162_491 = (let _162_490 = (FStar_Format.text "of")
in (_162_490)::(args)::[])
in (_162_492)::_162_491))
in (_162_494)::_162_493))
in (FStar_Format.reduce1 _162_495))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_73_665, ty)) -> begin
(

let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_501 = (let _162_500 = (FStar_Format.text "val")
in (let _162_499 = (let _162_498 = (FStar_Format.text x)
in (let _162_497 = (let _162_496 = (FStar_Format.text ": ")
in (_162_496)::(ty)::[])
in (_162_498)::_162_497))
in (_162_500)::_162_499))
in (FStar_Format.reduce1 _162_501)))
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
(let _162_512 = (let _162_511 = (FStar_Format.text "exception")
in (let _162_510 = (let _162_509 = (FStar_Format.text x)
in (_162_509)::[])
in (_162_511)::_162_510))
in (FStar_Format.reduce1 _162_512))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (

let args = (let _162_514 = (let _162_513 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_513 args))
in (FStar_Format.parens _162_514))
in (let _162_520 = (let _162_519 = (FStar_Format.text "exception")
in (let _162_518 = (let _162_517 = (FStar_Format.text x)
in (let _162_516 = (let _162_515 = (FStar_Format.text "of")
in (_162_515)::(args)::[])
in (_162_517)::_162_516))
in (_162_519)::_162_518))
in (FStar_Format.reduce1 _162_520))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _162_528 = (let _162_527 = (FStar_Format.text "let")
in (let _162_526 = (let _162_525 = (FStar_Format.text "_")
in (let _162_524 = (let _162_523 = (FStar_Format.text "=")
in (let _162_522 = (let _162_521 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_162_521)::[])
in (_162_523)::_162_522))
in (_162_525)::_162_524))
in (_162_527)::_162_526))
in (FStar_Format.reduce1 _162_528))
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

let head = (let _162_547 = (let _162_546 = (FStar_Format.text "module")
in (let _162_545 = (let _162_544 = (FStar_Format.text x)
in (let _162_543 = (let _162_542 = (FStar_Format.text ":")
in (let _162_541 = (let _162_540 = (FStar_Format.text "sig")
in (_162_540)::[])
in (_162_542)::_162_541))
in (_162_544)::_162_543))
in (_162_546)::_162_545))
in (FStar_Format.reduce1 _162_547))
in (

let tail = (let _162_549 = (let _162_548 = (FStar_Format.text "end")
in (_162_548)::[])
in (FStar_Format.reduce1 _162_549))
in (

let doc = (FStar_Option.map (fun _73_724 -> (match (_73_724) with
| (s, _73_723) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _162_559 = (let _162_558 = (FStar_Format.cat head FStar_Format.hardline)
in (let _162_557 = (let _162_556 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _162_555 = (let _162_554 = (FStar_Format.reduce sub)
in (let _162_553 = (let _162_552 = (FStar_Format.cat tail FStar_Format.hardline)
in (_162_552)::[])
in (_162_554)::_162_553))
in (_162_556)::_162_555))
in (_162_558)::_162_557))
in (FStar_Format.reduce _162_559)))))))
end))
and for1_mod = (fun istop _73_737 -> (match (_73_737) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let head = (let _162_572 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_564 = (FStar_Format.text "module")
in (let _162_563 = (let _162_562 = (FStar_Format.text x)
in (_162_562)::[])
in (_162_564)::_162_563))
end else begin
if (not (istop)) then begin
(let _162_571 = (FStar_Format.text "module")
in (let _162_570 = (let _162_569 = (FStar_Format.text x)
in (let _162_568 = (let _162_567 = (FStar_Format.text "=")
in (let _162_566 = (let _162_565 = (FStar_Format.text "struct")
in (_162_565)::[])
in (_162_567)::_162_566))
in (_162_569)::_162_568))
in (_162_571)::_162_570))
end else begin
[]
end
end
in (FStar_Format.reduce1 _162_572))
in (

let tail = if (not (istop)) then begin
(let _162_574 = (let _162_573 = (FStar_Format.text "end")
in (_162_573)::[])
in (FStar_Format.reduce1 _162_574))
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
(let _162_578 = (let _162_577 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _162_577 FStar_Format.hardline))
in (_162_578)::[])
end else begin
[]
end
in (let _162_590 = (let _162_589 = (let _162_588 = (let _162_587 = (let _162_586 = (FStar_Format.text "open Prims")
in (let _162_585 = (let _162_584 = (let _162_583 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _162_582 = (let _162_581 = (FStar_Format.reduce sub)
in (let _162_580 = (let _162_579 = (FStar_Format.cat tail FStar_Format.hardline)
in (_162_579)::[])
in (_162_581)::_162_580))
in (_162_583)::_162_582))
in (FStar_Format.hardline)::_162_584)
in (_162_586)::_162_585))
in (FStar_Format.hardline)::_162_587)
in (head)::_162_588)
in (FStar_List.append prefix _162_589))
in (FStar_All.pipe_left FStar_Format.reduce _162_590))))))))
end))
in (

let docs = (FStar_List.map (fun _73_755 -> (match (_73_755) with
| (x, s, m) -> begin
(let _162_592 = (for1_mod true (x, s, m))
in (x, _162_592))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _162_599 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _162_599 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _162_604 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _162_604 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))






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
| Infix (_77_4) -> begin
_77_4
end))


type opprec =
(Prims.int * fixity)


type level =
(opprec * assoc)


let t_prio_fun : (Prims.int * fixity) = (((Prims.parse_int "10")), (Infix (Right)))


let t_prio_tpl : (Prims.int * fixity) = (((Prims.parse_int "20")), (Infix (NonAssoc)))


let t_prio_name : (Prims.int * fixity) = (((Prims.parse_int "30")), (Postfix))


let e_bin_prio_lambda : (Prims.int * fixity) = (((Prims.parse_int "5")), (Prefix))


let e_bin_prio_if : (Prims.int * fixity) = (((Prims.parse_int "15")), (Prefix))


let e_bin_prio_letin : (Prims.int * fixity) = (((Prims.parse_int "19")), (Prefix))


let e_bin_prio_or : (Prims.int * fixity) = (((Prims.parse_int "20")), (Infix (Left)))


let e_bin_prio_and : (Prims.int * fixity) = (((Prims.parse_int "25")), (Infix (Left)))


let e_bin_prio_eq : (Prims.int * fixity) = (((Prims.parse_int "27")), (Infix (NonAssoc)))


let e_bin_prio_order : (Prims.int * fixity) = (((Prims.parse_int "29")), (Infix (NonAssoc)))


let e_bin_prio_op1 : (Prims.int * fixity) = (((Prims.parse_int "30")), (Infix (Left)))


let e_bin_prio_op2 : (Prims.int * fixity) = (((Prims.parse_int "40")), (Infix (Left)))


let e_bin_prio_op3 : (Prims.int * fixity) = (((Prims.parse_int "50")), (Infix (Left)))


let e_bin_prio_op4 : (Prims.int * fixity) = (((Prims.parse_int "60")), (Infix (Left)))


let e_bin_prio_comb : (Prims.int * fixity) = (((Prims.parse_int "70")), (Infix (Left)))


let e_bin_prio_seq : (Prims.int * fixity) = (((Prims.parse_int "100")), (Infix (Left)))


let e_app_prio : (Prims.int * fixity) = (((Prims.parse_int "10000")), (Infix (Left)))


let min_op_prec : (Prims.int * fixity) = (((~- ((Prims.parse_int "1")))), (Infix (NonAssoc)))


let max_op_prec : (Prims.int * fixity) = ((FStar_Util.max_int), (Infix (NonAssoc)))


let rec in_ns = (fun x -> (match (x) with
| ([], _77_9) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (_77_19, _77_21) -> begin
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

let _77_32 = (FStar_Util.first_N cg_len ns)
in (match (_77_32) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _174_31 = (let _174_30 = (let _174_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_174_29)::[])
in (FStar_List.append pfx _174_30))
in Some (_174_31))
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
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| _77_42 -> begin
(

let _77_45 = x
in (match (_77_45) with
| (ns, x) -> begin
(let _174_36 = (path_of_ns currentModule ns)
in ((_174_36), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _174_39 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase _174_39)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
(Prims.strcat "l__" s)
end else begin
s
end)


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(

let _77_51 = (mlpath_of_mlpath currentModule mlp)
in (match (_77_51) with
| (p, s) -> begin
(let _174_46 = (let _174_45 = (let _174_44 = (ptsym_of_symbol s)
in (_174_44)::[])
in (FStar_List.append p _174_45))
in (FStar_String.concat "." _174_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _77_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_77_56) with
| (p, s) -> begin
(

let s = if ((let _174_51 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase _174_51)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types = []


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _77_61 -> (match (_77_61) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_67 -> (match (_77_67) with
| (y, _77_64, _77_66) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _77_71 -> (match (_77_71) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_75 -> (match (_77_75) with
| (y, _77_74) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))


let as_standard_type = (fun _77_79 -> (match (_77_79) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_83 -> (match (_77_83) with
| (y, _77_82) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _77_87 -> (match (_77_87) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_91 -> (match (_77_91) with
| (y, _77_90) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _77_95 inner doc -> (match (_77_95) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let _77_104 = _inner
in (match (_77_104) with
| (pi, fi) -> begin
(

let _77_107 = _outer
in (match (_77_107) with
| (po, fo) -> begin
((pi > po) || (match (((fi), (side))) with
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
| (_77_131, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_77_135, _77_137) -> begin
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


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _77_1 -> (match (_77_1) with
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
(let _174_101 = (let _174_100 = (escape_or escape_char_hex c)
in (Prims.strcat _174_100 "\'"))
in (Prims.strcat "\'" _174_101))
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
(Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")"))
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(let _174_103 = (let _174_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _174_102 "\""))
in (Prims.strcat "\"" _174_103))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _174_105 = (let _174_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _174_104 "\""))
in (Prims.strcat "\"" _174_105))
end
| _77_203 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _174_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _174_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (let _174_120 = (let _174_119 = (let _174_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _174_118 doc))
in (FStar_Format.hbox _174_119))
in (FStar_Format.parens _174_120))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(

let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| (arg)::[] -> begin
(doc_of_mltype currentModule ((t_prio_name), (Left)) arg)
end
| _77_223 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (let _174_123 = (let _174_122 = (let _174_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _174_121 args))
in (FStar_Format.hbox _174_122))
in (FStar_Format.parens _174_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _174_125 = (let _174_124 = (as_standard_type name)
in (FStar_Option.get _174_124))
in (Prims.snd _174_125))
end else begin
(ptsym currentModule name)
end
in (let _174_129 = (let _174_128 = (let _174_127 = (let _174_126 = (FStar_Format.text name)
in (_174_126)::[])
in (args)::_174_127)
in (FStar_Format.reduce1 _174_128))
in (FStar_Format.hbox _174_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _77_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _174_134 = (let _174_133 = (let _174_132 = (let _174_131 = (let _174_130 = (FStar_Format.text " -> ")
in (_174_130)::(d2)::[])
in (d1)::_174_131)
in (FStar_Format.reduce1 _174_132))
in (FStar_Format.hbox _174_133))
in (maybe_paren outer t_prio_fun _174_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _174_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _174_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _174_161 = (let _174_160 = (let _174_159 = (FStar_Format.text "Prims.checked_cast")
in (_174_159)::(doc)::[])
in (FStar_Format.reduce _174_160))
in (FStar_Format.parens _174_161))
end else begin
(let _174_166 = (let _174_165 = (let _174_164 = (FStar_Format.text "Obj.magic ")
in (let _174_163 = (let _174_162 = (FStar_Format.parens doc)
in (_174_162)::[])
in (_174_164)::_174_163))
in (FStar_Format.reduce _174_165))
in (FStar_Format.parens _174_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (let _174_170 = (let _174_169 = (let _174_168 = (FStar_Format.text ";")
in (_174_168)::(FStar_Format.hardline)::[])
in (d)::_174_169)
in (FStar_Format.reduce _174_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _174_171 = (string_of_mlconstant c)
in (FStar_Format.text _174_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _77_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _174_172 = (ptsym currentModule path)
in (FStar_Format.text _174_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _77_269 -> (match (_77_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _174_179 = (let _174_178 = (let _174_175 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _174_175))
in (let _174_177 = (let _174_176 = (FStar_Format.text "=")
in (_174_176)::(doc)::[])
in (_174_178)::_174_177))
in (FStar_Format.reduce1 _174_179)))
end))
in (let _174_182 = (let _174_181 = (FStar_Format.text "; ")
in (let _174_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _174_181 _174_180)))
in (FStar_Format.cbrackets _174_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _174_184 = (let _174_183 = (as_standard_constructor ctor)
in (FStar_Option.get _174_183))
in (Prims.snd _174_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _174_186 = (let _174_185 = (as_standard_constructor ctor)
in (FStar_Option.get _174_185))
in (Prims.snd _174_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(let _174_190 = (let _174_189 = (FStar_Format.parens x)
in (let _174_188 = (let _174_187 = (FStar_Format.text "::")
in (_174_187)::(xs)::[])
in (_174_189)::_174_188))
in (FStar_Format.reduce _174_190))
end
| (_77_288, _77_290) -> begin
(let _174_196 = (let _174_195 = (FStar_Format.text name)
in (let _174_194 = (let _174_193 = (let _174_192 = (let _174_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _174_191 args))
in (FStar_Format.parens _174_192))
in (_174_193)::[])
in (_174_195)::_174_194))
in (FStar_Format.reduce1 _174_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (let _174_198 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _174_198))) es)
in (

let docs = (let _174_200 = (let _174_199 = (FStar_Format.text ", ")
in (FStar_Format.combine _174_199 docs))
in (FStar_Format.parens _174_200))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, _77_300, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _174_203 = (let _174_202 = (let _174_201 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_174_201)::[])
in (FStar_Format.hardline)::_174_202)
in (FStar_Format.reduce _174_203))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _174_210 = (let _174_209 = (let _174_208 = (let _174_207 = (let _174_206 = (let _174_205 = (let _174_204 = (FStar_Format.text "in")
in (_174_204)::(body)::[])
in (FStar_Format.reduce1 _174_205))
in (_174_206)::[])
in (doc)::_174_207)
in (pre)::_174_208)
in (FStar_Format.combine FStar_Format.hardline _174_209))
in (FStar_Format.parens _174_210)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((_77_333)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _77_331; FStar_Extraction_ML_Syntax.loc = _77_329})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, _77_321))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _77_318; FStar_Extraction_ML_Syntax.loc = _77_316})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _77_348; FStar_Extraction_ML_Syntax.loc = _77_346}, branches); FStar_Extraction_ML_Syntax.mlty = _77_344; FStar_Extraction_ML_Syntax.loc = _77_342} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
branches
end
| e -> begin
(((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (e)))::[]
end)
in (doc_of_expr currentModule outer {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Try (((scrutinee), (branches))); FStar_Extraction_ML_Syntax.mlty = possible_match.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = possible_match.FStar_Extraction_ML_Syntax.loc}))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::(e2)::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _77_367; FStar_Extraction_ML_Syntax.loc = _77_365}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _77_387; FStar_Extraction_ML_Syntax.loc = _77_385}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _77_399 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (let _174_211 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _174_211))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _174_216 = (let _174_215 = (let _174_214 = (FStar_Format.text ".")
in (let _174_213 = (let _174_212 = (FStar_Format.text (Prims.snd f))
in (_174_212)::[])
in (_174_214)::_174_213))
in (e)::_174_215)
in (FStar_Format.reduce _174_216))
end else begin
(let _174_222 = (let _174_221 = (let _174_220 = (FStar_Format.text ".")
in (let _174_219 = (let _174_218 = (let _174_217 = (ptsym currentModule f)
in (FStar_Format.text _174_217))
in (_174_218)::[])
in (_174_220)::_174_219))
in (e)::_174_221)
in (FStar_Format.reduce _174_222))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _174_238 = (let _174_237 = (FStar_Format.text "(")
in (let _174_236 = (let _174_235 = (FStar_Format.text x)
in (let _174_234 = (let _174_233 = (match (xt) with
| Some (xxt) -> begin
(let _174_230 = (let _174_229 = (FStar_Format.text " : ")
in (let _174_228 = (let _174_227 = (doc_of_mltype currentModule outer xxt)
in (_174_227)::[])
in (_174_229)::_174_228))
in (FStar_Format.reduce1 _174_230))
end
| _77_418 -> begin
(FStar_Format.text "")
end)
in (let _174_232 = (let _174_231 = (FStar_Format.text ")")
in (_174_231)::[])
in (_174_233)::_174_232))
in (_174_235)::_174_234))
in (_174_237)::_174_236))
in (FStar_Format.reduce1 _174_238))
end else begin
(FStar_Format.text x)
end)
in (

let ids = (FStar_List.map (fun _77_424 -> (match (_77_424) with
| ((x, _77_421), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (let _174_245 = (let _174_244 = (FStar_Format.text "fun")
in (let _174_243 = (let _174_242 = (FStar_Format.reduce1 ids)
in (let _174_241 = (let _174_240 = (FStar_Format.text "->")
in (_174_240)::(body)::[])
in (_174_242)::_174_241))
in (_174_244)::_174_243))
in (FStar_Format.reduce1 _174_245))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _174_258 = (let _174_257 = (let _174_252 = (let _174_251 = (FStar_Format.text "if")
in (let _174_250 = (let _174_249 = (let _174_248 = (FStar_Format.text "then")
in (let _174_247 = (let _174_246 = (FStar_Format.text "begin")
in (_174_246)::[])
in (_174_248)::_174_247))
in (cond)::_174_249)
in (_174_251)::_174_250))
in (FStar_Format.reduce1 _174_252))
in (let _174_256 = (let _174_255 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _174_254 = (let _174_253 = (FStar_Format.text "end")
in (_174_253)::[])
in (_174_255)::_174_254))
in (_174_257)::_174_256))
in (FStar_Format.combine FStar_Format.hardline _174_258))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _174_281 = (let _174_280 = (let _174_265 = (let _174_264 = (FStar_Format.text "if")
in (let _174_263 = (let _174_262 = (let _174_261 = (FStar_Format.text "then")
in (let _174_260 = (let _174_259 = (FStar_Format.text "begin")
in (_174_259)::[])
in (_174_261)::_174_260))
in (cond)::_174_262)
in (_174_264)::_174_263))
in (FStar_Format.reduce1 _174_265))
in (let _174_279 = (let _174_278 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _174_277 = (let _174_276 = (let _174_271 = (let _174_270 = (FStar_Format.text "end")
in (let _174_269 = (let _174_268 = (FStar_Format.text "else")
in (let _174_267 = (let _174_266 = (FStar_Format.text "begin")
in (_174_266)::[])
in (_174_268)::_174_267))
in (_174_270)::_174_269))
in (FStar_Format.reduce1 _174_271))
in (let _174_275 = (let _174_274 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (let _174_273 = (let _174_272 = (FStar_Format.text "end")
in (_174_272)::[])
in (_174_274)::_174_273))
in (_174_276)::_174_275))
in (_174_278)::_174_277))
in (_174_280)::_174_279))
in (FStar_Format.combine FStar_Format.hardline _174_281))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _174_288 = (let _174_287 = (let _174_286 = (FStar_Format.text "match")
in (let _174_285 = (let _174_284 = (FStar_Format.parens cond)
in (let _174_283 = (let _174_282 = (FStar_Format.text "with")
in (_174_282)::[])
in (_174_284)::_174_283))
in (_174_286)::_174_285))
in (FStar_Format.reduce1 _174_287))
in (_174_288)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _174_293 = (let _174_292 = (FStar_Format.text "raise")
in (let _174_291 = (let _174_290 = (let _174_289 = (ptctor currentModule exn)
in (FStar_Format.text _174_289))
in (_174_290)::[])
in (_174_292)::_174_291))
in (FStar_Format.reduce1 _174_293))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _174_302 = (let _174_301 = (FStar_Format.text "raise")
in (let _174_300 = (let _174_299 = (let _174_294 = (ptctor currentModule exn)
in (FStar_Format.text _174_294))
in (let _174_298 = (let _174_297 = (let _174_296 = (let _174_295 = (FStar_Format.text ", ")
in (FStar_Format.combine _174_295 args))
in (FStar_Format.parens _174_296))
in (_174_297)::[])
in (_174_299)::_174_298))
in (_174_301)::_174_300))
in (FStar_Format.reduce1 _174_302)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _174_311 = (let _174_310 = (FStar_Format.text "try")
in (let _174_309 = (let _174_308 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _174_307 = (let _174_306 = (FStar_Format.text "with")
in (let _174_305 = (let _174_304 = (let _174_303 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _174_303))
in (_174_304)::[])
in (_174_306)::_174_305))
in (_174_308)::_174_307))
in (_174_310)::_174_309))
in (FStar_Format.combine FStar_Format.hardline _174_311))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _77_472 = (let _174_316 = (as_bin_op p)
in (FStar_Option.get _174_316))
in (match (_77_472) with
| (_77_469, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (let _174_319 = (let _174_318 = (let _174_317 = (FStar_Format.text txt)
in (_174_317)::(e2)::[])
in (e1)::_174_318)
in (FStar_Format.reduce1 _174_319))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _77_482 = (let _174_323 = (as_uni_op p)
in (FStar_Option.get _174_323))
in (match (_77_482) with
| (_77_480, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc = (let _174_327 = (let _174_326 = (FStar_Format.text txt)
in (let _174_325 = (let _174_324 = (FStar_Format.parens e1)
in (_174_324)::[])
in (_174_326)::_174_325))
in (FStar_Format.reduce1 _174_327))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _174_330 = (string_of_mlconstant c)
in (FStar_Format.text _174_330))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _77_499 -> (match (_77_499) with
| (name, p) -> begin
(let _174_339 = (let _174_338 = (let _174_333 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _174_333))
in (let _174_337 = (let _174_336 = (FStar_Format.text "=")
in (let _174_335 = (let _174_334 = (doc_of_pattern currentModule p)
in (_174_334)::[])
in (_174_336)::_174_335))
in (_174_338)::_174_337))
in (FStar_Format.reduce1 _174_339))
end))
in (let _174_342 = (let _174_341 = (FStar_Format.text "; ")
in (let _174_340 = (FStar_List.map for1 fields)
in (FStar_Format.combine _174_341 _174_340)))
in (FStar_Format.cbrackets _174_342)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _174_344 = (let _174_343 = (as_standard_constructor ctor)
in (FStar_Option.get _174_343))
in (Prims.snd _174_344))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _174_346 = (let _174_345 = (as_standard_constructor ctor)
in (FStar_Option.get _174_345))
in (Prims.snd _174_346))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _174_353 = (let _174_352 = (let _174_347 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _174_347))
in (let _174_351 = (let _174_350 = (FStar_Format.text "::")
in (let _174_349 = (let _174_348 = (doc_of_pattern currentModule xs)
in (_174_348)::[])
in (_174_350)::_174_349))
in (_174_352)::_174_351))
in (FStar_Format.reduce _174_353))
end
| (_77_516, (FStar_Extraction_ML_Syntax.MLP_Tuple (_77_518))::[]) -> begin
(let _174_358 = (let _174_357 = (FStar_Format.text name)
in (let _174_356 = (let _174_355 = (let _174_354 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _174_354))
in (_174_355)::[])
in (_174_357)::_174_356))
in (FStar_Format.reduce1 _174_358))
end
| _77_523 -> begin
(let _174_365 = (let _174_364 = (FStar_Format.text name)
in (let _174_363 = (let _174_362 = (let _174_361 = (let _174_360 = (FStar_Format.text ", ")
in (let _174_359 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _174_360 _174_359)))
in (FStar_Format.parens _174_361))
in (_174_362)::[])
in (_174_364)::_174_363))
in (FStar_Format.reduce1 _174_365))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _174_367 = (let _174_366 = (FStar_Format.text ", ")
in (FStar_Format.combine _174_366 ps))
in (FStar_Format.parens _174_367)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _174_368 = (FStar_Format.text " | ")
in (FStar_Format.combine _174_368 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _77_536 -> (match (_77_536) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _174_374 = (let _174_373 = (FStar_Format.text "|")
in (let _174_372 = (let _174_371 = (doc_of_pattern currentModule p)
in (_174_371)::[])
in (_174_373)::_174_372))
in (FStar_Format.reduce1 _174_374))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _174_380 = (let _174_379 = (FStar_Format.text "|")
in (let _174_378 = (let _174_377 = (doc_of_pattern currentModule p)
in (let _174_376 = (let _174_375 = (FStar_Format.text "when")
in (_174_375)::(c)::[])
in (_174_377)::_174_376))
in (_174_379)::_174_378))
in (FStar_Format.reduce1 _174_380)))
end)
in (let _174_391 = (let _174_390 = (let _174_385 = (let _174_384 = (let _174_383 = (FStar_Format.text "->")
in (let _174_382 = (let _174_381 = (FStar_Format.text "begin")
in (_174_381)::[])
in (_174_383)::_174_382))
in (case)::_174_384)
in (FStar_Format.reduce1 _174_385))
in (let _174_389 = (let _174_388 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _174_387 = (let _174_386 = (FStar_Format.text "end")
in (_174_386)::[])
in (_174_388)::_174_387))
in (_174_390)::_174_389))
in (FStar_Format.combine FStar_Format.hardline _174_391)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _77_546 -> (match (_77_546) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun _77_554 -> (match (_77_554) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _77_551; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun _77_560 -> (match (_77_560) with
| (x, _77_559) -> begin
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

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _174_398 = (let _174_397 = (FStar_Format.text ":")
in (_174_397)::(ty)::[])
in (FStar_Format.reduce1 _174_398)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some ((_)::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _174_400 = (let _174_399 = (FStar_Format.text ":")
in (_174_399)::(ty)::[])
in (FStar_Format.reduce1 _174_400)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _174_407 = (let _174_406 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _174_405 = (let _174_404 = (FStar_Format.reduce1 ids)
in (let _174_403 = (let _174_402 = (let _174_401 = (FStar_Format.text "=")
in (_174_401)::(e)::[])
in (ty_annot)::_174_402)
in (_174_404)::_174_403))
in (_174_406)::_174_405))
in (FStar_Format.reduce1 _174_407))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(let _174_411 = (let _174_410 = (FStar_Format.text "let")
in (let _174_409 = (let _174_408 = (FStar_Format.text "rec")
in (_174_408)::[])
in (_174_410)::_174_409))
in (FStar_Format.reduce1 _174_411))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _174_415 = (let _174_414 = if (i = (Prims.parse_int "0")) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_174_414)::(doc)::[])
in (FStar_Format.reduce1 _174_415))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _77_600 -> (match (_77_600) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _174_422 = (let _174_421 = (FStar_Format.text "#")
in (let _174_420 = (let _174_419 = (FStar_Format.num lineno)
in (let _174_418 = (let _174_417 = (FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\"")))
in (_174_417)::[])
in (_174_419)::_174_418))
in (_174_421)::_174_420))
in (FStar_Format.reduce1 _174_422)))
end
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun _77_611 -> (match (_77_611) with
| (_77_606, x, mangle_opt, tparams, body) -> begin
(

let x = (match (mangle_opt) with
| None -> begin
x
end
| Some (y) -> begin
y
end)
in (

let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| (x)::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _77_620 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _174_431 = (let _174_430 = (FStar_Format.text ", ")
in (FStar_Format.combine _174_430 doc))
in (FStar_Format.parens _174_431)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun _77_633 -> (match (_77_633) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _174_438 = (let _174_437 = (let _174_436 = (FStar_Format.text ":")
in (_174_436)::(ty)::[])
in (name)::_174_437)
in (FStar_Format.reduce1 _174_438))))
end))
in (let _174_441 = (let _174_440 = (FStar_Format.text "; ")
in (let _174_439 = (FStar_List.map forfield fields)
in (FStar_Format.combine _174_440 _174_439)))
in (FStar_Format.cbrackets _174_441)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun _77_641 -> (match (_77_641) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _77_644 -> begin
(

let tys = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let tys = (let _174_444 = (FStar_Format.text " * ")
in (FStar_Format.combine _174_444 tys))
in (let _174_448 = (let _174_447 = (FStar_Format.text name)
in (let _174_446 = (let _174_445 = (FStar_Format.text "of")
in (_174_445)::(tys)::[])
in (_174_447)::_174_446))
in (FStar_Format.reduce1 _174_448))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _174_451 = (let _174_450 = (FStar_Format.text "|")
in (_174_450)::(d)::[])
in (FStar_Format.reduce1 _174_451))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _174_455 = (let _174_454 = (let _174_453 = (let _174_452 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _174_452))
in (_174_453)::[])
in (tparams)::_174_454)
in (FStar_Format.reduce1 _174_455))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _174_460 = (let _174_459 = (let _174_458 = (let _174_457 = (let _174_456 = (FStar_Format.text "=")
in (_174_456)::[])
in (doc)::_174_457)
in (FStar_Format.reduce1 _174_458))
in (_174_459)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _174_460)))
end)))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > (Prims.parse_int "0")) then begin
(let _174_465 = (let _174_464 = (FStar_Format.text "type")
in (let _174_463 = (let _174_462 = (let _174_461 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _174_461 doc))
in (_174_462)::[])
in (_174_464)::_174_463))
in (FStar_Format.reduce1 _174_465))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _174_485 = (let _174_484 = (let _174_477 = (let _174_476 = (FStar_Format.text "module")
in (let _174_475 = (let _174_474 = (FStar_Format.text x)
in (let _174_473 = (let _174_472 = (FStar_Format.text "=")
in (_174_472)::[])
in (_174_474)::_174_473))
in (_174_476)::_174_475))
in (FStar_Format.reduce1 _174_477))
in (let _174_483 = (let _174_482 = (doc_of_sig currentModule subsig)
in (let _174_481 = (let _174_480 = (let _174_479 = (let _174_478 = (FStar_Format.text "end")
in (_174_478)::[])
in (FStar_Format.reduce1 _174_479))
in (_174_480)::[])
in (_174_482)::_174_481))
in (_174_484)::_174_483))
in (FStar_Format.combine FStar_Format.hardline _174_485))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _174_489 = (let _174_488 = (FStar_Format.text "exception")
in (let _174_487 = (let _174_486 = (FStar_Format.text x)
in (_174_486)::[])
in (_174_488)::_174_487))
in (FStar_Format.reduce1 _174_489))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _174_491 = (let _174_490 = (FStar_Format.text " * ")
in (FStar_Format.combine _174_490 args))
in (FStar_Format.parens _174_491))
in (let _174_497 = (let _174_496 = (FStar_Format.text "exception")
in (let _174_495 = (let _174_494 = (FStar_Format.text x)
in (let _174_493 = (let _174_492 = (FStar_Format.text "of")
in (_174_492)::(args)::[])
in (_174_494)::_174_493))
in (_174_496)::_174_495))
in (FStar_Format.reduce1 _174_497))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_77_675, ty)) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _174_503 = (let _174_502 = (FStar_Format.text "val")
in (let _174_501 = (let _174_500 = (FStar_Format.text x)
in (let _174_499 = (let _174_498 = (FStar_Format.text ": ")
in (_174_498)::(ty)::[])
in (_174_500)::_174_499))
in (_174_502)::_174_501))
in (FStar_Format.reduce1 _174_503)))
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
(let _174_514 = (let _174_513 = (FStar_Format.text "exception")
in (let _174_512 = (let _174_511 = (FStar_Format.text x)
in (_174_511)::[])
in (_174_513)::_174_512))
in (FStar_Format.reduce1 _174_514))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _174_516 = (let _174_515 = (FStar_Format.text " * ")
in (FStar_Format.combine _174_515 args))
in (FStar_Format.parens _174_516))
in (let _174_522 = (let _174_521 = (FStar_Format.text "exception")
in (let _174_520 = (let _174_519 = (FStar_Format.text x)
in (let _174_518 = (let _174_517 = (FStar_Format.text "of")
in (_174_517)::(args)::[])
in (_174_519)::_174_518))
in (_174_521)::_174_520))
in (FStar_Format.reduce1 _174_522))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, _77_704, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _174_530 = (let _174_529 = (FStar_Format.text "let")
in (let _174_528 = (let _174_527 = (FStar_Format.text "_")
in (let _174_526 = (let _174_525 = (FStar_Format.text "=")
in (let _174_524 = (let _174_523 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_174_523)::[])
in (_174_525)::_174_524))
in (_174_527)::_174_526))
in (_174_529)::_174_528))
in (FStar_Format.reduce1 _174_530))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_77_717) -> begin
FStar_Format.empty
end
| _77_720 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _77_723 -> (match (_77_723) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun _77_730 -> (match (_77_730) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _174_549 = (let _174_548 = (FStar_Format.text "module")
in (let _174_547 = (let _174_546 = (FStar_Format.text x)
in (let _174_545 = (let _174_544 = (FStar_Format.text ":")
in (let _174_543 = (let _174_542 = (FStar_Format.text "sig")
in (_174_542)::[])
in (_174_544)::_174_543))
in (_174_546)::_174_545))
in (_174_548)::_174_547))
in (FStar_Format.reduce1 _174_549))
in (

let tail = (let _174_551 = (let _174_550 = (FStar_Format.text "end")
in (_174_550)::[])
in (FStar_Format.reduce1 _174_551))
in (

let doc = (FStar_Option.map (fun _77_737 -> (match (_77_737) with
| (s, _77_736) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _174_561 = (let _174_560 = (FStar_Format.cat head FStar_Format.hardline)
in (let _174_559 = (let _174_558 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _174_557 = (let _174_556 = (FStar_Format.reduce sub)
in (let _174_555 = (let _174_554 = (FStar_Format.cat tail FStar_Format.hardline)
in (_174_554)::[])
in (_174_556)::_174_555))
in (_174_558)::_174_557))
in (_174_560)::_174_559))
in (FStar_Format.reduce _174_561))))))))
end))
and for1_mod = (fun istop _77_750 -> (match (_77_750) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _174_574 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _174_566 = (FStar_Format.text "module")
in (let _174_565 = (let _174_564 = (FStar_Format.text x)
in (_174_564)::[])
in (_174_566)::_174_565))
end else begin
if (not (istop)) then begin
(let _174_573 = (FStar_Format.text "module")
in (let _174_572 = (let _174_571 = (FStar_Format.text x)
in (let _174_570 = (let _174_569 = (FStar_Format.text "=")
in (let _174_568 = (let _174_567 = (FStar_Format.text "struct")
in (_174_567)::[])
in (_174_569)::_174_568))
in (_174_571)::_174_570))
in (_174_573)::_174_572))
end else begin
[]
end
end
in (FStar_Format.reduce1 _174_574))
in (

let tail = if (not (istop)) then begin
(let _174_576 = (let _174_575 = (FStar_Format.text "end")
in (_174_575)::[])
in (FStar_Format.reduce1 _174_576))
end else begin
(FStar_Format.reduce1 [])
end
in (

let doc = (FStar_Option.map (fun _77_757 -> (match (_77_757) with
| (_77_755, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _174_580 = (let _174_579 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _174_579 FStar_Format.hardline))
in (_174_580)::[])
end else begin
[]
end
in (let _174_592 = (let _174_591 = (let _174_590 = (let _174_589 = (let _174_588 = (FStar_Format.text "open Prims")
in (let _174_587 = (let _174_586 = (let _174_585 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _174_584 = (let _174_583 = (FStar_Format.reduce sub)
in (let _174_582 = (let _174_581 = (FStar_Format.cat tail FStar_Format.hardline)
in (_174_581)::[])
in (_174_583)::_174_582))
in (_174_585)::_174_584))
in (FStar_Format.hardline)::_174_586)
in (_174_588)::_174_587))
in (FStar_Format.hardline)::_174_589)
in (head)::_174_590)
in (FStar_List.append prefix _174_591))
in (FStar_All.pipe_left FStar_Format.reduce _174_592)))))))))
end))
in (

let docs = (FStar_List.map (fun _77_769 -> (match (_77_769) with
| (x, s, m) -> begin
(let _174_595 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _174_594 = (for1_mod true ((x), (s), (m)))
in ((_174_595), (_174_594))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _174_602 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _174_602 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _174_607 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _174_607 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))






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
| Infix (_78_4) -> begin
_78_4
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
| ([], _78_9) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (_78_19, _78_21) -> begin
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

let _78_32 = (FStar_Util.first_N cg_len ns)
in (match (_78_32) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _177_31 = (let _177_30 = (let _177_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_177_29)::[])
in (FStar_List.append pfx _177_30))
in Some (_177_31))
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
| _78_42 -> begin
(

let _78_45 = x
in (match (_78_45) with
| (ns, x) -> begin
(let _177_36 = (path_of_ns currentModule ns)
in ((_177_36), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _177_39 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase _177_39)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
(Prims.strcat "l__" s)
end else begin
s
end)


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(

let _78_51 = (mlpath_of_mlpath currentModule mlp)
in (match (_78_51) with
| (p, s) -> begin
(let _177_46 = (let _177_45 = (let _177_44 = (ptsym_of_symbol s)
in (_177_44)::[])
in (FStar_List.append p _177_45))
in (FStar_String.concat "." _177_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _78_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_78_56) with
| (p, s) -> begin
(

let s = if ((let _177_51 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase _177_51)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
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


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _78_61 -> (match (_78_61) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _78_67 -> (match (_78_67) with
| (y, _78_64, _78_66) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _78_71 -> (match (_78_71) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _78_75 -> (match (_78_75) with
| (y, _78_74) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))


let as_standard_type = (fun _78_79 -> (match (_78_79) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _78_83 -> (match (_78_83) with
| (y, _78_82) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _78_87 -> (match (_78_87) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _78_91 -> (match (_78_91) with
| (y, _78_90) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _78_95 inner doc -> (match (_78_95) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let _78_104 = _inner
in (match (_78_104) with
| (pi, fi) -> begin
(

let _78_107 = _outer
in (match (_78_107) with
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
| (_78_131, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_78_135, _78_137) -> begin
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


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _78_1 -> (match (_78_1) with
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
(let _177_101 = (let _177_100 = (escape_or escape_char_hex c)
in (Prims.strcat _177_100 "\'"))
in (Prims.strcat "\'" _177_101))
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
(let _177_103 = (let _177_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _177_102 "\""))
in (Prims.strcat "\"" _177_103))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _177_105 = (let _177_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _177_104 "\""))
in (Prims.strcat "\"" _177_105))
end
| _78_203 -> begin
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
in (let _177_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _177_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (let _177_120 = (let _177_119 = (let _177_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _177_118 doc))
in (FStar_Format.hbox _177_119))
in (FStar_Format.parens _177_120))
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
| _78_223 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (let _177_123 = (let _177_122 = (let _177_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _177_121 args))
in (FStar_Format.hbox _177_122))
in (FStar_Format.parens _177_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _177_125 = (let _177_124 = (as_standard_type name)
in (FStar_Option.get _177_124))
in (Prims.snd _177_125))
end else begin
(ptsym currentModule name)
end
in (let _177_129 = (let _177_128 = (let _177_127 = (let _177_126 = (FStar_Format.text name)
in (_177_126)::[])
in (args)::_177_127)
in (FStar_Format.reduce1 _177_128))
in (FStar_Format.hbox _177_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _78_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _177_134 = (let _177_133 = (let _177_132 = (let _177_131 = (let _177_130 = (FStar_Format.text " -> ")
in (_177_130)::(d2)::[])
in (d1)::_177_131)
in (FStar_Format.reduce1 _177_132))
in (FStar_Format.hbox _177_133))
in (maybe_paren outer t_prio_fun _177_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _177_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _177_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _177_161 = (let _177_160 = (let _177_159 = (FStar_Format.text "Prims.checked_cast")
in (_177_159)::(doc)::[])
in (FStar_Format.reduce _177_160))
in (FStar_Format.parens _177_161))
end else begin
(let _177_166 = (let _177_165 = (let _177_164 = (FStar_Format.text "Obj.magic ")
in (let _177_163 = (let _177_162 = (FStar_Format.parens doc)
in (_177_162)::[])
in (_177_164)::_177_163))
in (FStar_Format.reduce _177_165))
in (FStar_Format.parens _177_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (let _177_170 = (let _177_169 = (let _177_168 = (FStar_Format.text ";")
in (_177_168)::(FStar_Format.hardline)::[])
in (d)::_177_169)
in (FStar_Format.reduce _177_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _177_171 = (string_of_mlconstant c)
in (FStar_Format.text _177_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _78_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _177_172 = (ptsym currentModule path)
in (FStar_Format.text _177_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _78_269 -> (match (_78_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _177_179 = (let _177_178 = (let _177_175 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _177_175))
in (let _177_177 = (let _177_176 = (FStar_Format.text "=")
in (_177_176)::(doc)::[])
in (_177_178)::_177_177))
in (FStar_Format.reduce1 _177_179)))
end))
in (let _177_182 = (let _177_181 = (FStar_Format.text "; ")
in (let _177_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _177_181 _177_180)))
in (FStar_Format.cbrackets _177_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _177_184 = (let _177_183 = (as_standard_constructor ctor)
in (FStar_Option.get _177_183))
in (Prims.snd _177_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _177_186 = (let _177_185 = (as_standard_constructor ctor)
in (FStar_Option.get _177_185))
in (Prims.snd _177_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(let _177_190 = (let _177_189 = (FStar_Format.parens x)
in (let _177_188 = (let _177_187 = (FStar_Format.text "::")
in (_177_187)::(xs)::[])
in (_177_189)::_177_188))
in (FStar_Format.reduce _177_190))
end
| (_78_288, _78_290) -> begin
(let _177_196 = (let _177_195 = (FStar_Format.text name)
in (let _177_194 = (let _177_193 = (let _177_192 = (let _177_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _177_191 args))
in (FStar_Format.parens _177_192))
in (_177_193)::[])
in (_177_195)::_177_194))
in (FStar_Format.reduce1 _177_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (let _177_198 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _177_198))) es)
in (

let docs = (let _177_200 = (let _177_199 = (FStar_Format.text ", ")
in (FStar_Format.combine _177_199 docs))
in (FStar_Format.parens _177_200))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, _78_300, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _177_203 = (let _177_202 = (let _177_201 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_177_201)::[])
in (FStar_Format.hardline)::_177_202)
in (FStar_Format.reduce _177_203))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _177_210 = (let _177_209 = (let _177_208 = (let _177_207 = (let _177_206 = (let _177_205 = (let _177_204 = (FStar_Format.text "in")
in (_177_204)::(body)::[])
in (FStar_Format.reduce1 _177_205))
in (_177_206)::[])
in (doc)::_177_207)
in (pre)::_177_208)
in (FStar_Format.combine FStar_Format.hardline _177_209))
in (FStar_Format.parens _177_210)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((_78_333)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _78_331; FStar_Extraction_ML_Syntax.loc = _78_329})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, _78_321))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _78_318; FStar_Extraction_ML_Syntax.loc = _78_316})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _78_348; FStar_Extraction_ML_Syntax.loc = _78_346}, branches); FStar_Extraction_ML_Syntax.mlty = _78_344; FStar_Extraction_ML_Syntax.loc = _78_342} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _78_367; FStar_Extraction_ML_Syntax.loc = _78_365}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _78_387; FStar_Extraction_ML_Syntax.loc = _78_385}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _78_399 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (let _177_211 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _177_211))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _177_216 = (let _177_215 = (let _177_214 = (FStar_Format.text ".")
in (let _177_213 = (let _177_212 = (FStar_Format.text (Prims.snd f))
in (_177_212)::[])
in (_177_214)::_177_213))
in (e)::_177_215)
in (FStar_Format.reduce _177_216))
end else begin
(let _177_222 = (let _177_221 = (let _177_220 = (FStar_Format.text ".")
in (let _177_219 = (let _177_218 = (let _177_217 = (ptsym currentModule f)
in (FStar_Format.text _177_217))
in (_177_218)::[])
in (_177_220)::_177_219))
in (e)::_177_221)
in (FStar_Format.reduce _177_222))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _177_238 = (let _177_237 = (FStar_Format.text "(")
in (let _177_236 = (let _177_235 = (FStar_Format.text x)
in (let _177_234 = (let _177_233 = (match (xt) with
| Some (xxt) -> begin
(let _177_230 = (let _177_229 = (FStar_Format.text " : ")
in (let _177_228 = (let _177_227 = (doc_of_mltype currentModule outer xxt)
in (_177_227)::[])
in (_177_229)::_177_228))
in (FStar_Format.reduce1 _177_230))
end
| _78_418 -> begin
(FStar_Format.text "")
end)
in (let _177_232 = (let _177_231 = (FStar_Format.text ")")
in (_177_231)::[])
in (_177_233)::_177_232))
in (_177_235)::_177_234))
in (_177_237)::_177_236))
in (FStar_Format.reduce1 _177_238))
end else begin
(FStar_Format.text x)
end)
in (

let ids = (FStar_List.map (fun _78_424 -> (match (_78_424) with
| ((x, _78_421), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (let _177_245 = (let _177_244 = (FStar_Format.text "fun")
in (let _177_243 = (let _177_242 = (FStar_Format.reduce1 ids)
in (let _177_241 = (let _177_240 = (FStar_Format.text "->")
in (_177_240)::(body)::[])
in (_177_242)::_177_241))
in (_177_244)::_177_243))
in (FStar_Format.reduce1 _177_245))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _177_258 = (let _177_257 = (let _177_252 = (let _177_251 = (FStar_Format.text "if")
in (let _177_250 = (let _177_249 = (let _177_248 = (FStar_Format.text "then")
in (let _177_247 = (let _177_246 = (FStar_Format.text "begin")
in (_177_246)::[])
in (_177_248)::_177_247))
in (cond)::_177_249)
in (_177_251)::_177_250))
in (FStar_Format.reduce1 _177_252))
in (let _177_256 = (let _177_255 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _177_254 = (let _177_253 = (FStar_Format.text "end")
in (_177_253)::[])
in (_177_255)::_177_254))
in (_177_257)::_177_256))
in (FStar_Format.combine FStar_Format.hardline _177_258))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _177_281 = (let _177_280 = (let _177_265 = (let _177_264 = (FStar_Format.text "if")
in (let _177_263 = (let _177_262 = (let _177_261 = (FStar_Format.text "then")
in (let _177_260 = (let _177_259 = (FStar_Format.text "begin")
in (_177_259)::[])
in (_177_261)::_177_260))
in (cond)::_177_262)
in (_177_264)::_177_263))
in (FStar_Format.reduce1 _177_265))
in (let _177_279 = (let _177_278 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _177_277 = (let _177_276 = (let _177_271 = (let _177_270 = (FStar_Format.text "end")
in (let _177_269 = (let _177_268 = (FStar_Format.text "else")
in (let _177_267 = (let _177_266 = (FStar_Format.text "begin")
in (_177_266)::[])
in (_177_268)::_177_267))
in (_177_270)::_177_269))
in (FStar_Format.reduce1 _177_271))
in (let _177_275 = (let _177_274 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (let _177_273 = (let _177_272 = (FStar_Format.text "end")
in (_177_272)::[])
in (_177_274)::_177_273))
in (_177_276)::_177_275))
in (_177_278)::_177_277))
in (_177_280)::_177_279))
in (FStar_Format.combine FStar_Format.hardline _177_281))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _177_288 = (let _177_287 = (let _177_286 = (FStar_Format.text "match")
in (let _177_285 = (let _177_284 = (FStar_Format.parens cond)
in (let _177_283 = (let _177_282 = (FStar_Format.text "with")
in (_177_282)::[])
in (_177_284)::_177_283))
in (_177_286)::_177_285))
in (FStar_Format.reduce1 _177_287))
in (_177_288)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _177_293 = (let _177_292 = (FStar_Format.text "raise")
in (let _177_291 = (let _177_290 = (let _177_289 = (ptctor currentModule exn)
in (FStar_Format.text _177_289))
in (_177_290)::[])
in (_177_292)::_177_291))
in (FStar_Format.reduce1 _177_293))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _177_302 = (let _177_301 = (FStar_Format.text "raise")
in (let _177_300 = (let _177_299 = (let _177_294 = (ptctor currentModule exn)
in (FStar_Format.text _177_294))
in (let _177_298 = (let _177_297 = (let _177_296 = (let _177_295 = (FStar_Format.text ", ")
in (FStar_Format.combine _177_295 args))
in (FStar_Format.parens _177_296))
in (_177_297)::[])
in (_177_299)::_177_298))
in (_177_301)::_177_300))
in (FStar_Format.reduce1 _177_302)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _177_311 = (let _177_310 = (FStar_Format.text "try")
in (let _177_309 = (let _177_308 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _177_307 = (let _177_306 = (FStar_Format.text "with")
in (let _177_305 = (let _177_304 = (let _177_303 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _177_303))
in (_177_304)::[])
in (_177_306)::_177_305))
in (_177_308)::_177_307))
in (_177_310)::_177_309))
in (FStar_Format.combine FStar_Format.hardline _177_311))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _78_472 = (let _177_316 = (as_bin_op p)
in (FStar_Option.get _177_316))
in (match (_78_472) with
| (_78_469, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (let _177_319 = (let _177_318 = (let _177_317 = (FStar_Format.text txt)
in (_177_317)::(e2)::[])
in (e1)::_177_318)
in (FStar_Format.reduce1 _177_319))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _78_482 = (let _177_323 = (as_uni_op p)
in (FStar_Option.get _177_323))
in (match (_78_482) with
| (_78_480, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc = (let _177_327 = (let _177_326 = (FStar_Format.text txt)
in (let _177_325 = (let _177_324 = (FStar_Format.parens e1)
in (_177_324)::[])
in (_177_326)::_177_325))
in (FStar_Format.reduce1 _177_327))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _177_330 = (string_of_mlconstant c)
in (FStar_Format.text _177_330))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _78_499 -> (match (_78_499) with
| (name, p) -> begin
(let _177_339 = (let _177_338 = (let _177_333 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _177_333))
in (let _177_337 = (let _177_336 = (FStar_Format.text "=")
in (let _177_335 = (let _177_334 = (doc_of_pattern currentModule p)
in (_177_334)::[])
in (_177_336)::_177_335))
in (_177_338)::_177_337))
in (FStar_Format.reduce1 _177_339))
end))
in (let _177_342 = (let _177_341 = (FStar_Format.text "; ")
in (let _177_340 = (FStar_List.map for1 fields)
in (FStar_Format.combine _177_341 _177_340)))
in (FStar_Format.cbrackets _177_342)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _177_344 = (let _177_343 = (as_standard_constructor ctor)
in (FStar_Option.get _177_343))
in (Prims.snd _177_344))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _177_346 = (let _177_345 = (as_standard_constructor ctor)
in (FStar_Option.get _177_345))
in (Prims.snd _177_346))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _177_353 = (let _177_352 = (let _177_347 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _177_347))
in (let _177_351 = (let _177_350 = (FStar_Format.text "::")
in (let _177_349 = (let _177_348 = (doc_of_pattern currentModule xs)
in (_177_348)::[])
in (_177_350)::_177_349))
in (_177_352)::_177_351))
in (FStar_Format.reduce _177_353))
end
| (_78_516, (FStar_Extraction_ML_Syntax.MLP_Tuple (_78_518))::[]) -> begin
(let _177_358 = (let _177_357 = (FStar_Format.text name)
in (let _177_356 = (let _177_355 = (let _177_354 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _177_354))
in (_177_355)::[])
in (_177_357)::_177_356))
in (FStar_Format.reduce1 _177_358))
end
| _78_523 -> begin
(let _177_365 = (let _177_364 = (FStar_Format.text name)
in (let _177_363 = (let _177_362 = (let _177_361 = (let _177_360 = (FStar_Format.text ", ")
in (let _177_359 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _177_360 _177_359)))
in (FStar_Format.parens _177_361))
in (_177_362)::[])
in (_177_364)::_177_363))
in (FStar_Format.reduce1 _177_365))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _177_367 = (let _177_366 = (FStar_Format.text ", ")
in (FStar_Format.combine _177_366 ps))
in (FStar_Format.parens _177_367)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _177_368 = (FStar_Format.text " | ")
in (FStar_Format.combine _177_368 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _78_536 -> (match (_78_536) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _177_374 = (let _177_373 = (FStar_Format.text "|")
in (let _177_372 = (let _177_371 = (doc_of_pattern currentModule p)
in (_177_371)::[])
in (_177_373)::_177_372))
in (FStar_Format.reduce1 _177_374))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _177_380 = (let _177_379 = (FStar_Format.text "|")
in (let _177_378 = (let _177_377 = (doc_of_pattern currentModule p)
in (let _177_376 = (let _177_375 = (FStar_Format.text "when")
in (_177_375)::(c)::[])
in (_177_377)::_177_376))
in (_177_379)::_177_378))
in (FStar_Format.reduce1 _177_380)))
end)
in (let _177_391 = (let _177_390 = (let _177_385 = (let _177_384 = (let _177_383 = (FStar_Format.text "->")
in (let _177_382 = (let _177_381 = (FStar_Format.text "begin")
in (_177_381)::[])
in (_177_383)::_177_382))
in (case)::_177_384)
in (FStar_Format.reduce1 _177_385))
in (let _177_389 = (let _177_388 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _177_387 = (let _177_386 = (FStar_Format.text "end")
in (_177_386)::[])
in (_177_388)::_177_387))
in (_177_390)::_177_389))
in (FStar_Format.combine FStar_Format.hardline _177_391)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _78_546 -> (match (_78_546) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun _78_554 -> (match (_78_554) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _78_551; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun _78_560 -> (match (_78_560) with
| (x, _78_559) -> begin
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
in (let _177_398 = (let _177_397 = (FStar_Format.text ":")
in (_177_397)::(ty)::[])
in (FStar_Format.reduce1 _177_398)))
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
in (let _177_400 = (let _177_399 = (FStar_Format.text ":")
in (_177_399)::(ty)::[])
in (FStar_Format.reduce1 _177_400)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _177_407 = (let _177_406 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _177_405 = (let _177_404 = (FStar_Format.reduce1 ids)
in (let _177_403 = (let _177_402 = (let _177_401 = (FStar_Format.text "=")
in (_177_401)::(e)::[])
in (ty_annot)::_177_402)
in (_177_404)::_177_403))
in (_177_406)::_177_405))
in (FStar_Format.reduce1 _177_407))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(let _177_411 = (let _177_410 = (FStar_Format.text "let")
in (let _177_409 = (let _177_408 = (FStar_Format.text "rec")
in (_177_408)::[])
in (_177_410)::_177_409))
in (FStar_Format.reduce1 _177_411))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _177_415 = (let _177_414 = if (i = (Prims.parse_int "0")) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_177_414)::(doc)::[])
in (FStar_Format.reduce1 _177_415))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _78_600 -> (match (_78_600) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _177_422 = (let _177_421 = (FStar_Format.text "#")
in (let _177_420 = (let _177_419 = (FStar_Format.num lineno)
in (let _177_418 = (let _177_417 = (FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\"")))
in (_177_417)::[])
in (_177_419)::_177_418))
in (_177_421)::_177_420))
in (FStar_Format.reduce1 _177_422)))
end
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun _78_611 -> (match (_78_611) with
| (_78_606, x, mangle_opt, tparams, body) -> begin
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
| _78_620 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _177_431 = (let _177_430 = (FStar_Format.text ", ")
in (FStar_Format.combine _177_430 doc))
in (FStar_Format.parens _177_431)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun _78_633 -> (match (_78_633) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _177_438 = (let _177_437 = (let _177_436 = (FStar_Format.text ":")
in (_177_436)::(ty)::[])
in (name)::_177_437)
in (FStar_Format.reduce1 _177_438))))
end))
in (let _177_441 = (let _177_440 = (FStar_Format.text "; ")
in (let _177_439 = (FStar_List.map forfield fields)
in (FStar_Format.combine _177_440 _177_439)))
in (FStar_Format.cbrackets _177_441)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun _78_641 -> (match (_78_641) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _78_644 -> begin
(

let tys = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let tys = (let _177_444 = (FStar_Format.text " * ")
in (FStar_Format.combine _177_444 tys))
in (let _177_448 = (let _177_447 = (FStar_Format.text name)
in (let _177_446 = (let _177_445 = (FStar_Format.text "of")
in (_177_445)::(tys)::[])
in (_177_447)::_177_446))
in (FStar_Format.reduce1 _177_448))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _177_451 = (let _177_450 = (FStar_Format.text "|")
in (_177_450)::(d)::[])
in (FStar_Format.reduce1 _177_451))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _177_455 = (let _177_454 = (let _177_453 = (let _177_452 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _177_452))
in (_177_453)::[])
in (tparams)::_177_454)
in (FStar_Format.reduce1 _177_455))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _177_460 = (let _177_459 = (let _177_458 = (let _177_457 = (let _177_456 = (FStar_Format.text "=")
in (_177_456)::[])
in (doc)::_177_457)
in (FStar_Format.reduce1 _177_458))
in (_177_459)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _177_460)))
end)))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > (Prims.parse_int "0")) then begin
(let _177_465 = (let _177_464 = (FStar_Format.text "type")
in (let _177_463 = (let _177_462 = (let _177_461 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _177_461 doc))
in (_177_462)::[])
in (_177_464)::_177_463))
in (FStar_Format.reduce1 _177_465))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _177_485 = (let _177_484 = (let _177_477 = (let _177_476 = (FStar_Format.text "module")
in (let _177_475 = (let _177_474 = (FStar_Format.text x)
in (let _177_473 = (let _177_472 = (FStar_Format.text "=")
in (_177_472)::[])
in (_177_474)::_177_473))
in (_177_476)::_177_475))
in (FStar_Format.reduce1 _177_477))
in (let _177_483 = (let _177_482 = (doc_of_sig currentModule subsig)
in (let _177_481 = (let _177_480 = (let _177_479 = (let _177_478 = (FStar_Format.text "end")
in (_177_478)::[])
in (FStar_Format.reduce1 _177_479))
in (_177_480)::[])
in (_177_482)::_177_481))
in (_177_484)::_177_483))
in (FStar_Format.combine FStar_Format.hardline _177_485))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _177_489 = (let _177_488 = (FStar_Format.text "exception")
in (let _177_487 = (let _177_486 = (FStar_Format.text x)
in (_177_486)::[])
in (_177_488)::_177_487))
in (FStar_Format.reduce1 _177_489))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _177_491 = (let _177_490 = (FStar_Format.text " * ")
in (FStar_Format.combine _177_490 args))
in (FStar_Format.parens _177_491))
in (let _177_497 = (let _177_496 = (FStar_Format.text "exception")
in (let _177_495 = (let _177_494 = (FStar_Format.text x)
in (let _177_493 = (let _177_492 = (FStar_Format.text "of")
in (_177_492)::(args)::[])
in (_177_494)::_177_493))
in (_177_496)::_177_495))
in (FStar_Format.reduce1 _177_497))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_78_675, ty)) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _177_503 = (let _177_502 = (FStar_Format.text "val")
in (let _177_501 = (let _177_500 = (FStar_Format.text x)
in (let _177_499 = (let _177_498 = (FStar_Format.text ": ")
in (_177_498)::(ty)::[])
in (_177_500)::_177_499))
in (_177_502)::_177_501))
in (FStar_Format.reduce1 _177_503)))
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
(let _177_514 = (let _177_513 = (FStar_Format.text "exception")
in (let _177_512 = (let _177_511 = (FStar_Format.text x)
in (_177_511)::[])
in (_177_513)::_177_512))
in (FStar_Format.reduce1 _177_514))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _177_516 = (let _177_515 = (FStar_Format.text " * ")
in (FStar_Format.combine _177_515 args))
in (FStar_Format.parens _177_516))
in (let _177_522 = (let _177_521 = (FStar_Format.text "exception")
in (let _177_520 = (let _177_519 = (FStar_Format.text x)
in (let _177_518 = (let _177_517 = (FStar_Format.text "of")
in (_177_517)::(args)::[])
in (_177_519)::_177_518))
in (_177_521)::_177_520))
in (FStar_Format.reduce1 _177_522))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, _78_704, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _177_530 = (let _177_529 = (FStar_Format.text "let")
in (let _177_528 = (let _177_527 = (FStar_Format.text "_")
in (let _177_526 = (let _177_525 = (FStar_Format.text "=")
in (let _177_524 = (let _177_523 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_177_523)::[])
in (_177_525)::_177_524))
in (_177_527)::_177_526))
in (_177_529)::_177_528))
in (FStar_Format.reduce1 _177_530))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_78_717) -> begin
FStar_Format.empty
end
| _78_720 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _78_723 -> (match (_78_723) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun _78_730 -> (match (_78_730) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _177_549 = (let _177_548 = (FStar_Format.text "module")
in (let _177_547 = (let _177_546 = (FStar_Format.text x)
in (let _177_545 = (let _177_544 = (FStar_Format.text ":")
in (let _177_543 = (let _177_542 = (FStar_Format.text "sig")
in (_177_542)::[])
in (_177_544)::_177_543))
in (_177_546)::_177_545))
in (_177_548)::_177_547))
in (FStar_Format.reduce1 _177_549))
in (

let tail = (let _177_551 = (let _177_550 = (FStar_Format.text "end")
in (_177_550)::[])
in (FStar_Format.reduce1 _177_551))
in (

let doc = (FStar_Option.map (fun _78_737 -> (match (_78_737) with
| (s, _78_736) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _177_561 = (let _177_560 = (FStar_Format.cat head FStar_Format.hardline)
in (let _177_559 = (let _177_558 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _177_557 = (let _177_556 = (FStar_Format.reduce sub)
in (let _177_555 = (let _177_554 = (FStar_Format.cat tail FStar_Format.hardline)
in (_177_554)::[])
in (_177_556)::_177_555))
in (_177_558)::_177_557))
in (_177_560)::_177_559))
in (FStar_Format.reduce _177_561))))))))
end))
and for1_mod = (fun istop _78_750 -> (match (_78_750) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _177_574 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _177_566 = (FStar_Format.text "module")
in (let _177_565 = (let _177_564 = (FStar_Format.text x)
in (_177_564)::[])
in (_177_566)::_177_565))
end else begin
if (not (istop)) then begin
(let _177_573 = (FStar_Format.text "module")
in (let _177_572 = (let _177_571 = (FStar_Format.text x)
in (let _177_570 = (let _177_569 = (FStar_Format.text "=")
in (let _177_568 = (let _177_567 = (FStar_Format.text "struct")
in (_177_567)::[])
in (_177_569)::_177_568))
in (_177_571)::_177_570))
in (_177_573)::_177_572))
end else begin
[]
end
end
in (FStar_Format.reduce1 _177_574))
in (

let tail = if (not (istop)) then begin
(let _177_576 = (let _177_575 = (FStar_Format.text "end")
in (_177_575)::[])
in (FStar_Format.reduce1 _177_576))
end else begin
(FStar_Format.reduce1 [])
end
in (

let doc = (FStar_Option.map (fun _78_757 -> (match (_78_757) with
| (_78_755, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _177_580 = (let _177_579 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _177_579 FStar_Format.hardline))
in (_177_580)::[])
end else begin
[]
end
in (let _177_592 = (let _177_591 = (let _177_590 = (let _177_589 = (let _177_588 = (FStar_Format.text "open Prims")
in (let _177_587 = (let _177_586 = (let _177_585 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _177_584 = (let _177_583 = (FStar_Format.reduce sub)
in (let _177_582 = (let _177_581 = (FStar_Format.cat tail FStar_Format.hardline)
in (_177_581)::[])
in (_177_583)::_177_582))
in (_177_585)::_177_584))
in (FStar_Format.hardline)::_177_586)
in (_177_588)::_177_587))
in (FStar_Format.hardline)::_177_589)
in (head)::_177_590)
in (FStar_List.append prefix _177_591))
in (FStar_All.pipe_left FStar_Format.reduce _177_592)))))))))
end))
in (

let docs = (FStar_List.map (fun _78_769 -> (match (_78_769) with
| (x, s, m) -> begin
(let _177_595 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _177_594 = (for1_mod true ((x), (s), (m)))
in ((_177_595), (_177_594))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _177_602 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _177_602 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _177_607 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _177_607 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





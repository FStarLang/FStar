
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
| Infix (_75_4) -> begin
_75_4
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
| ([], _75_9) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (_75_19, _75_21) -> begin
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

let _75_32 = (FStar_Util.first_N cg_len ns)
in (match (_75_32) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _169_31 = (let _169_30 = (let _169_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_169_29)::[])
in (FStar_List.append pfx _169_30))
in Some (_169_31))
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
| _75_42 -> begin
(

let _75_45 = x
in (match (_75_45) with
| (ns, x) -> begin
(let _169_36 = (path_of_ns currentModule ns)
in ((_169_36), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _169_39 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase _169_39)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
(Prims.strcat "l__" s)
end else begin
s
end)


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(

let _75_51 = (mlpath_of_mlpath currentModule mlp)
in (match (_75_51) with
| (p, s) -> begin
(let _169_46 = (let _169_45 = (let _169_44 = (ptsym_of_symbol s)
in (_169_44)::[])
in (FStar_List.append p _169_45))
in (FStar_String.concat "." _169_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _75_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_75_56) with
| (p, s) -> begin
(

let s = if ((let _169_51 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase _169_51)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
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


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _75_61 -> (match (_75_61) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _75_67 -> (match (_75_67) with
| (y, _75_64, _75_66) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _75_71 -> (match (_75_71) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _75_75 -> (match (_75_75) with
| (y, _75_74) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))


let as_standard_type = (fun _75_79 -> (match (_75_79) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _75_83 -> (match (_75_83) with
| (y, _75_82) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _75_87 -> (match (_75_87) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _75_91 -> (match (_75_91) with
| (y, _75_90) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _75_95 inner doc -> (match (_75_95) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let _75_104 = _inner
in (match (_75_104) with
| (pi, fi) -> begin
(

let _75_107 = _outer
in (match (_75_107) with
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
| (_75_131, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_75_135, _75_137) -> begin
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


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _75_1 -> (match (_75_1) with
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
(let _169_101 = (let _169_100 = (escape_or escape_char_hex c)
in (Prims.strcat _169_100 "\'"))
in (Prims.strcat "\'" _169_101))
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
(let _169_103 = (let _169_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _169_102 "\""))
in (Prims.strcat "\"" _169_103))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _169_105 = (let _169_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _169_104 "\""))
in (Prims.strcat "\"" _169_105))
end
| _75_203 -> begin
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
in (let _169_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _169_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (let _169_120 = (let _169_119 = (let _169_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _169_118 doc))
in (FStar_Format.hbox _169_119))
in (FStar_Format.parens _169_120))
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
| _75_223 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (let _169_123 = (let _169_122 = (let _169_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _169_121 args))
in (FStar_Format.hbox _169_122))
in (FStar_Format.parens _169_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _169_125 = (let _169_124 = (as_standard_type name)
in (FStar_Option.get _169_124))
in (Prims.snd _169_125))
end else begin
(ptsym currentModule name)
end
in (let _169_129 = (let _169_128 = (let _169_127 = (let _169_126 = (FStar_Format.text name)
in (_169_126)::[])
in (args)::_169_127)
in (FStar_Format.reduce1 _169_128))
in (FStar_Format.hbox _169_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _75_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _169_134 = (let _169_133 = (let _169_132 = (let _169_131 = (let _169_130 = (FStar_Format.text " -> ")
in (_169_130)::(d2)::[])
in (d1)::_169_131)
in (FStar_Format.reduce1 _169_132))
in (FStar_Format.hbox _169_133))
in (maybe_paren outer t_prio_fun _169_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _169_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _169_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _169_161 = (let _169_160 = (let _169_159 = (FStar_Format.text "Prims.checked_cast")
in (_169_159)::(doc)::[])
in (FStar_Format.reduce _169_160))
in (FStar_Format.parens _169_161))
end else begin
(let _169_166 = (let _169_165 = (let _169_164 = (FStar_Format.text "Obj.magic ")
in (let _169_163 = (let _169_162 = (FStar_Format.parens doc)
in (_169_162)::[])
in (_169_164)::_169_163))
in (FStar_Format.reduce _169_165))
in (FStar_Format.parens _169_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (let _169_170 = (let _169_169 = (let _169_168 = (FStar_Format.text ";")
in (_169_168)::(FStar_Format.hardline)::[])
in (d)::_169_169)
in (FStar_Format.reduce _169_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _169_171 = (string_of_mlconstant c)
in (FStar_Format.text _169_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _75_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _169_172 = (ptsym currentModule path)
in (FStar_Format.text _169_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _75_269 -> (match (_75_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _169_179 = (let _169_178 = (let _169_175 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _169_175))
in (let _169_177 = (let _169_176 = (FStar_Format.text "=")
in (_169_176)::(doc)::[])
in (_169_178)::_169_177))
in (FStar_Format.reduce1 _169_179)))
end))
in (let _169_182 = (let _169_181 = (FStar_Format.text "; ")
in (let _169_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _169_181 _169_180)))
in (FStar_Format.cbrackets _169_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _169_184 = (let _169_183 = (as_standard_constructor ctor)
in (FStar_Option.get _169_183))
in (Prims.snd _169_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _169_186 = (let _169_185 = (as_standard_constructor ctor)
in (FStar_Option.get _169_185))
in (Prims.snd _169_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(let _169_190 = (let _169_189 = (FStar_Format.parens x)
in (let _169_188 = (let _169_187 = (FStar_Format.text "::")
in (_169_187)::(xs)::[])
in (_169_189)::_169_188))
in (FStar_Format.reduce _169_190))
end
| (_75_288, _75_290) -> begin
(let _169_196 = (let _169_195 = (FStar_Format.text name)
in (let _169_194 = (let _169_193 = (let _169_192 = (let _169_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _169_191 args))
in (FStar_Format.parens _169_192))
in (_169_193)::[])
in (_169_195)::_169_194))
in (FStar_Format.reduce1 _169_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (let _169_198 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _169_198))) es)
in (

let docs = (let _169_200 = (let _169_199 = (FStar_Format.text ", ")
in (FStar_Format.combine _169_199 docs))
in (FStar_Format.parens _169_200))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _169_203 = (let _169_202 = (let _169_201 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_169_201)::[])
in (FStar_Format.hardline)::_169_202)
in (FStar_Format.reduce _169_203))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _169_210 = (let _169_209 = (let _169_208 = (let _169_207 = (let _169_206 = (let _169_205 = (let _169_204 = (FStar_Format.text "in")
in (_169_204)::(body)::[])
in (FStar_Format.reduce1 _169_205))
in (_169_206)::[])
in (doc)::_169_207)
in (pre)::_169_208)
in (FStar_Format.combine FStar_Format.hardline _169_209))
in (FStar_Format.parens _169_210)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((_75_331)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _75_329; FStar_Extraction_ML_Syntax.loc = _75_327})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, _75_319))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _75_316; FStar_Extraction_ML_Syntax.loc = _75_314})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _75_346; FStar_Extraction_ML_Syntax.loc = _75_344}, branches); FStar_Extraction_ML_Syntax.mlty = _75_342; FStar_Extraction_ML_Syntax.loc = _75_340} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _75_365; FStar_Extraction_ML_Syntax.loc = _75_363}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _75_385; FStar_Extraction_ML_Syntax.loc = _75_383}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _75_397 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (let _169_211 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _169_211))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _169_216 = (let _169_215 = (let _169_214 = (FStar_Format.text ".")
in (let _169_213 = (let _169_212 = (FStar_Format.text (Prims.snd f))
in (_169_212)::[])
in (_169_214)::_169_213))
in (e)::_169_215)
in (FStar_Format.reduce _169_216))
end else begin
(let _169_222 = (let _169_221 = (let _169_220 = (FStar_Format.text ".")
in (let _169_219 = (let _169_218 = (let _169_217 = (ptsym currentModule f)
in (FStar_Format.text _169_217))
in (_169_218)::[])
in (_169_220)::_169_219))
in (e)::_169_221)
in (FStar_Format.reduce _169_222))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _169_238 = (let _169_237 = (FStar_Format.text "(")
in (let _169_236 = (let _169_235 = (FStar_Format.text x)
in (let _169_234 = (let _169_233 = (match (xt) with
| Some (xxt) -> begin
(let _169_230 = (let _169_229 = (FStar_Format.text " : ")
in (let _169_228 = (let _169_227 = (doc_of_mltype currentModule outer xxt)
in (_169_227)::[])
in (_169_229)::_169_228))
in (FStar_Format.reduce1 _169_230))
end
| _75_416 -> begin
(FStar_Format.text "")
end)
in (let _169_232 = (let _169_231 = (FStar_Format.text ")")
in (_169_231)::[])
in (_169_233)::_169_232))
in (_169_235)::_169_234))
in (_169_237)::_169_236))
in (FStar_Format.reduce1 _169_238))
end else begin
(FStar_Format.text x)
end)
in (

let ids = (FStar_List.map (fun _75_422 -> (match (_75_422) with
| ((x, _75_419), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (let _169_245 = (let _169_244 = (FStar_Format.text "fun")
in (let _169_243 = (let _169_242 = (FStar_Format.reduce1 ids)
in (let _169_241 = (let _169_240 = (FStar_Format.text "->")
in (_169_240)::(body)::[])
in (_169_242)::_169_241))
in (_169_244)::_169_243))
in (FStar_Format.reduce1 _169_245))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _169_258 = (let _169_257 = (let _169_252 = (let _169_251 = (FStar_Format.text "if")
in (let _169_250 = (let _169_249 = (let _169_248 = (FStar_Format.text "then")
in (let _169_247 = (let _169_246 = (FStar_Format.text "begin")
in (_169_246)::[])
in (_169_248)::_169_247))
in (cond)::_169_249)
in (_169_251)::_169_250))
in (FStar_Format.reduce1 _169_252))
in (let _169_256 = (let _169_255 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _169_254 = (let _169_253 = (FStar_Format.text "end")
in (_169_253)::[])
in (_169_255)::_169_254))
in (_169_257)::_169_256))
in (FStar_Format.combine FStar_Format.hardline _169_258))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _169_281 = (let _169_280 = (let _169_265 = (let _169_264 = (FStar_Format.text "if")
in (let _169_263 = (let _169_262 = (let _169_261 = (FStar_Format.text "then")
in (let _169_260 = (let _169_259 = (FStar_Format.text "begin")
in (_169_259)::[])
in (_169_261)::_169_260))
in (cond)::_169_262)
in (_169_264)::_169_263))
in (FStar_Format.reduce1 _169_265))
in (let _169_279 = (let _169_278 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _169_277 = (let _169_276 = (let _169_271 = (let _169_270 = (FStar_Format.text "end")
in (let _169_269 = (let _169_268 = (FStar_Format.text "else")
in (let _169_267 = (let _169_266 = (FStar_Format.text "begin")
in (_169_266)::[])
in (_169_268)::_169_267))
in (_169_270)::_169_269))
in (FStar_Format.reduce1 _169_271))
in (let _169_275 = (let _169_274 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (let _169_273 = (let _169_272 = (FStar_Format.text "end")
in (_169_272)::[])
in (_169_274)::_169_273))
in (_169_276)::_169_275))
in (_169_278)::_169_277))
in (_169_280)::_169_279))
in (FStar_Format.combine FStar_Format.hardline _169_281))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _169_288 = (let _169_287 = (let _169_286 = (FStar_Format.text "match")
in (let _169_285 = (let _169_284 = (FStar_Format.parens cond)
in (let _169_283 = (let _169_282 = (FStar_Format.text "with")
in (_169_282)::[])
in (_169_284)::_169_283))
in (_169_286)::_169_285))
in (FStar_Format.reduce1 _169_287))
in (_169_288)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _169_293 = (let _169_292 = (FStar_Format.text "raise")
in (let _169_291 = (let _169_290 = (let _169_289 = (ptctor currentModule exn)
in (FStar_Format.text _169_289))
in (_169_290)::[])
in (_169_292)::_169_291))
in (FStar_Format.reduce1 _169_293))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _169_302 = (let _169_301 = (FStar_Format.text "raise")
in (let _169_300 = (let _169_299 = (let _169_294 = (ptctor currentModule exn)
in (FStar_Format.text _169_294))
in (let _169_298 = (let _169_297 = (let _169_296 = (let _169_295 = (FStar_Format.text ", ")
in (FStar_Format.combine _169_295 args))
in (FStar_Format.parens _169_296))
in (_169_297)::[])
in (_169_299)::_169_298))
in (_169_301)::_169_300))
in (FStar_Format.reduce1 _169_302)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _169_311 = (let _169_310 = (FStar_Format.text "try")
in (let _169_309 = (let _169_308 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _169_307 = (let _169_306 = (FStar_Format.text "with")
in (let _169_305 = (let _169_304 = (let _169_303 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _169_303))
in (_169_304)::[])
in (_169_306)::_169_305))
in (_169_308)::_169_307))
in (_169_310)::_169_309))
in (FStar_Format.combine FStar_Format.hardline _169_311))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _75_470 = (let _169_316 = (as_bin_op p)
in (FStar_Option.get _169_316))
in (match (_75_470) with
| (_75_467, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (let _169_319 = (let _169_318 = (let _169_317 = (FStar_Format.text txt)
in (_169_317)::(e2)::[])
in (e1)::_169_318)
in (FStar_Format.reduce1 _169_319))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _75_480 = (let _169_323 = (as_uni_op p)
in (FStar_Option.get _169_323))
in (match (_75_480) with
| (_75_478, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc = (let _169_327 = (let _169_326 = (FStar_Format.text txt)
in (let _169_325 = (let _169_324 = (FStar_Format.parens e1)
in (_169_324)::[])
in (_169_326)::_169_325))
in (FStar_Format.reduce1 _169_327))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _169_330 = (string_of_mlconstant c)
in (FStar_Format.text _169_330))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _75_497 -> (match (_75_497) with
| (name, p) -> begin
(let _169_339 = (let _169_338 = (let _169_333 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _169_333))
in (let _169_337 = (let _169_336 = (FStar_Format.text "=")
in (let _169_335 = (let _169_334 = (doc_of_pattern currentModule p)
in (_169_334)::[])
in (_169_336)::_169_335))
in (_169_338)::_169_337))
in (FStar_Format.reduce1 _169_339))
end))
in (let _169_342 = (let _169_341 = (FStar_Format.text "; ")
in (let _169_340 = (FStar_List.map for1 fields)
in (FStar_Format.combine _169_341 _169_340)))
in (FStar_Format.cbrackets _169_342)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _169_344 = (let _169_343 = (as_standard_constructor ctor)
in (FStar_Option.get _169_343))
in (Prims.snd _169_344))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _169_346 = (let _169_345 = (as_standard_constructor ctor)
in (FStar_Option.get _169_345))
in (Prims.snd _169_346))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _169_353 = (let _169_352 = (let _169_347 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _169_347))
in (let _169_351 = (let _169_350 = (FStar_Format.text "::")
in (let _169_349 = (let _169_348 = (doc_of_pattern currentModule xs)
in (_169_348)::[])
in (_169_350)::_169_349))
in (_169_352)::_169_351))
in (FStar_Format.reduce _169_353))
end
| (_75_514, (FStar_Extraction_ML_Syntax.MLP_Tuple (_75_516))::[]) -> begin
(let _169_358 = (let _169_357 = (FStar_Format.text name)
in (let _169_356 = (let _169_355 = (let _169_354 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _169_354))
in (_169_355)::[])
in (_169_357)::_169_356))
in (FStar_Format.reduce1 _169_358))
end
| _75_521 -> begin
(let _169_365 = (let _169_364 = (FStar_Format.text name)
in (let _169_363 = (let _169_362 = (let _169_361 = (let _169_360 = (FStar_Format.text ", ")
in (let _169_359 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _169_360 _169_359)))
in (FStar_Format.parens _169_361))
in (_169_362)::[])
in (_169_364)::_169_363))
in (FStar_Format.reduce1 _169_365))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _169_367 = (let _169_366 = (FStar_Format.text ", ")
in (FStar_Format.combine _169_366 ps))
in (FStar_Format.parens _169_367)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _169_368 = (FStar_Format.text " | ")
in (FStar_Format.combine _169_368 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _75_534 -> (match (_75_534) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _169_374 = (let _169_373 = (FStar_Format.text "|")
in (let _169_372 = (let _169_371 = (doc_of_pattern currentModule p)
in (_169_371)::[])
in (_169_373)::_169_372))
in (FStar_Format.reduce1 _169_374))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _169_380 = (let _169_379 = (FStar_Format.text "|")
in (let _169_378 = (let _169_377 = (doc_of_pattern currentModule p)
in (let _169_376 = (let _169_375 = (FStar_Format.text "when")
in (_169_375)::(c)::[])
in (_169_377)::_169_376))
in (_169_379)::_169_378))
in (FStar_Format.reduce1 _169_380)))
end)
in (let _169_391 = (let _169_390 = (let _169_385 = (let _169_384 = (let _169_383 = (FStar_Format.text "->")
in (let _169_382 = (let _169_381 = (FStar_Format.text "begin")
in (_169_381)::[])
in (_169_383)::_169_382))
in (case)::_169_384)
in (FStar_Format.reduce1 _169_385))
in (let _169_389 = (let _169_388 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _169_387 = (let _169_386 = (FStar_Format.text "end")
in (_169_386)::[])
in (_169_388)::_169_387))
in (_169_390)::_169_389))
in (FStar_Format.combine FStar_Format.hardline _169_391)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _75_544 -> (match (_75_544) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun _75_552 -> (match (_75_552) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _75_549; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun _75_558 -> (match (_75_558) with
| (x, _75_557) -> begin
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
in (let _169_398 = (let _169_397 = (FStar_Format.text ":")
in (_169_397)::(ty)::[])
in (FStar_Format.reduce1 _169_398)))
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
in (let _169_400 = (let _169_399 = (FStar_Format.text ":")
in (_169_399)::(ty)::[])
in (FStar_Format.reduce1 _169_400)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _169_407 = (let _169_406 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _169_405 = (let _169_404 = (FStar_Format.reduce1 ids)
in (let _169_403 = (let _169_402 = (let _169_401 = (FStar_Format.text "=")
in (_169_401)::(e)::[])
in (ty_annot)::_169_402)
in (_169_404)::_169_403))
in (_169_406)::_169_405))
in (FStar_Format.reduce1 _169_407))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(let _169_411 = (let _169_410 = (FStar_Format.text "let")
in (let _169_409 = (let _169_408 = (FStar_Format.text "rec")
in (_169_408)::[])
in (_169_410)::_169_409))
in (FStar_Format.reduce1 _169_411))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _169_415 = (let _169_414 = if (i = (Prims.parse_int "0")) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_169_414)::(doc)::[])
in (FStar_Format.reduce1 _169_415))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _75_598 -> (match (_75_598) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _169_422 = (let _169_421 = (FStar_Format.text "#")
in (let _169_420 = (let _169_419 = (FStar_Format.num lineno)
in (let _169_418 = (let _169_417 = (FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\"")))
in (_169_417)::[])
in (_169_419)::_169_418))
in (_169_421)::_169_420))
in (FStar_Format.reduce1 _169_422)))
end
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun _75_606 -> (match (_75_606) with
| (x, tparams, body) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| (x)::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _75_611 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _169_431 = (let _169_430 = (FStar_Format.text ", ")
in (FStar_Format.combine _169_430 doc))
in (FStar_Format.parens _169_431)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun _75_624 -> (match (_75_624) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _169_438 = (let _169_437 = (let _169_436 = (FStar_Format.text ":")
in (_169_436)::(ty)::[])
in (name)::_169_437)
in (FStar_Format.reduce1 _169_438))))
end))
in (let _169_441 = (let _169_440 = (FStar_Format.text "; ")
in (let _169_439 = (FStar_List.map forfield fields)
in (FStar_Format.combine _169_440 _169_439)))
in (FStar_Format.cbrackets _169_441)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun _75_632 -> (match (_75_632) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _75_635 -> begin
(

let tys = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let tys = (let _169_444 = (FStar_Format.text " * ")
in (FStar_Format.combine _169_444 tys))
in (let _169_448 = (let _169_447 = (FStar_Format.text name)
in (let _169_446 = (let _169_445 = (FStar_Format.text "of")
in (_169_445)::(tys)::[])
in (_169_447)::_169_446))
in (FStar_Format.reduce1 _169_448))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _169_451 = (let _169_450 = (FStar_Format.text "|")
in (_169_450)::(d)::[])
in (FStar_Format.reduce1 _169_451))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _169_455 = (let _169_454 = (let _169_453 = (let _169_452 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _169_452))
in (_169_453)::[])
in (tparams)::_169_454)
in (FStar_Format.reduce1 _169_455))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _169_460 = (let _169_459 = (let _169_458 = (let _169_457 = (let _169_456 = (FStar_Format.text "=")
in (_169_456)::[])
in (doc)::_169_457)
in (FStar_Format.reduce1 _169_458))
in (_169_459)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _169_460)))
end))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > (Prims.parse_int "0")) then begin
(let _169_465 = (let _169_464 = (FStar_Format.text "type")
in (let _169_463 = (let _169_462 = (let _169_461 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _169_461 doc))
in (_169_462)::[])
in (_169_464)::_169_463))
in (FStar_Format.reduce1 _169_465))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _169_485 = (let _169_484 = (let _169_477 = (let _169_476 = (FStar_Format.text "module")
in (let _169_475 = (let _169_474 = (FStar_Format.text x)
in (let _169_473 = (let _169_472 = (FStar_Format.text "=")
in (_169_472)::[])
in (_169_474)::_169_473))
in (_169_476)::_169_475))
in (FStar_Format.reduce1 _169_477))
in (let _169_483 = (let _169_482 = (doc_of_sig currentModule subsig)
in (let _169_481 = (let _169_480 = (let _169_479 = (let _169_478 = (FStar_Format.text "end")
in (_169_478)::[])
in (FStar_Format.reduce1 _169_479))
in (_169_480)::[])
in (_169_482)::_169_481))
in (_169_484)::_169_483))
in (FStar_Format.combine FStar_Format.hardline _169_485))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _169_489 = (let _169_488 = (FStar_Format.text "exception")
in (let _169_487 = (let _169_486 = (FStar_Format.text x)
in (_169_486)::[])
in (_169_488)::_169_487))
in (FStar_Format.reduce1 _169_489))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _169_491 = (let _169_490 = (FStar_Format.text " * ")
in (FStar_Format.combine _169_490 args))
in (FStar_Format.parens _169_491))
in (let _169_497 = (let _169_496 = (FStar_Format.text "exception")
in (let _169_495 = (let _169_494 = (FStar_Format.text x)
in (let _169_493 = (let _169_492 = (FStar_Format.text "of")
in (_169_492)::(args)::[])
in (_169_494)::_169_493))
in (_169_496)::_169_495))
in (FStar_Format.reduce1 _169_497))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_75_666, ty)) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _169_503 = (let _169_502 = (FStar_Format.text "val")
in (let _169_501 = (let _169_500 = (FStar_Format.text x)
in (let _169_499 = (let _169_498 = (FStar_Format.text ": ")
in (_169_498)::(ty)::[])
in (_169_500)::_169_499))
in (_169_502)::_169_501))
in (FStar_Format.reduce1 _169_503)))
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
(let _169_514 = (let _169_513 = (FStar_Format.text "exception")
in (let _169_512 = (let _169_511 = (FStar_Format.text x)
in (_169_511)::[])
in (_169_513)::_169_512))
in (FStar_Format.reduce1 _169_514))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _169_516 = (let _169_515 = (FStar_Format.text " * ")
in (FStar_Format.combine _169_515 args))
in (FStar_Format.parens _169_516))
in (let _169_522 = (let _169_521 = (FStar_Format.text "exception")
in (let _169_520 = (let _169_519 = (FStar_Format.text x)
in (let _169_518 = (let _169_517 = (FStar_Format.text "of")
in (_169_517)::(args)::[])
in (_169_519)::_169_518))
in (_169_521)::_169_520))
in (FStar_Format.reduce1 _169_522))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _169_530 = (let _169_529 = (FStar_Format.text "let")
in (let _169_528 = (let _169_527 = (FStar_Format.text "_")
in (let _169_526 = (let _169_525 = (FStar_Format.text "=")
in (let _169_524 = (let _169_523 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_169_523)::[])
in (_169_525)::_169_524))
in (_169_527)::_169_526))
in (_169_529)::_169_528))
in (FStar_Format.reduce1 _169_530))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_75_706) -> begin
FStar_Format.empty
end
| _75_709 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _75_712 -> (match (_75_712) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun _75_719 -> (match (_75_719) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _169_549 = (let _169_548 = (FStar_Format.text "module")
in (let _169_547 = (let _169_546 = (FStar_Format.text x)
in (let _169_545 = (let _169_544 = (FStar_Format.text ":")
in (let _169_543 = (let _169_542 = (FStar_Format.text "sig")
in (_169_542)::[])
in (_169_544)::_169_543))
in (_169_546)::_169_545))
in (_169_548)::_169_547))
in (FStar_Format.reduce1 _169_549))
in (

let tail = (let _169_551 = (let _169_550 = (FStar_Format.text "end")
in (_169_550)::[])
in (FStar_Format.reduce1 _169_551))
in (

let doc = (FStar_Option.map (fun _75_726 -> (match (_75_726) with
| (s, _75_725) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _169_561 = (let _169_560 = (FStar_Format.cat head FStar_Format.hardline)
in (let _169_559 = (let _169_558 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _169_557 = (let _169_556 = (FStar_Format.reduce sub)
in (let _169_555 = (let _169_554 = (FStar_Format.cat tail FStar_Format.hardline)
in (_169_554)::[])
in (_169_556)::_169_555))
in (_169_558)::_169_557))
in (_169_560)::_169_559))
in (FStar_Format.reduce _169_561))))))))
end))
and for1_mod = (fun istop _75_739 -> (match (_75_739) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _169_574 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _169_566 = (FStar_Format.text "module")
in (let _169_565 = (let _169_564 = (FStar_Format.text x)
in (_169_564)::[])
in (_169_566)::_169_565))
end else begin
if (not (istop)) then begin
(let _169_573 = (FStar_Format.text "module")
in (let _169_572 = (let _169_571 = (FStar_Format.text x)
in (let _169_570 = (let _169_569 = (FStar_Format.text "=")
in (let _169_568 = (let _169_567 = (FStar_Format.text "struct")
in (_169_567)::[])
in (_169_569)::_169_568))
in (_169_571)::_169_570))
in (_169_573)::_169_572))
end else begin
[]
end
end
in (FStar_Format.reduce1 _169_574))
in (

let tail = if (not (istop)) then begin
(let _169_576 = (let _169_575 = (FStar_Format.text "end")
in (_169_575)::[])
in (FStar_Format.reduce1 _169_576))
end else begin
(FStar_Format.reduce1 [])
end
in (

let doc = (FStar_Option.map (fun _75_746 -> (match (_75_746) with
| (_75_744, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _169_580 = (let _169_579 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _169_579 FStar_Format.hardline))
in (_169_580)::[])
end else begin
[]
end
in (let _169_592 = (let _169_591 = (let _169_590 = (let _169_589 = (let _169_588 = (FStar_Format.text "open Prims")
in (let _169_587 = (let _169_586 = (let _169_585 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _169_584 = (let _169_583 = (FStar_Format.reduce sub)
in (let _169_582 = (let _169_581 = (FStar_Format.cat tail FStar_Format.hardline)
in (_169_581)::[])
in (_169_583)::_169_582))
in (_169_585)::_169_584))
in (FStar_Format.hardline)::_169_586)
in (_169_588)::_169_587))
in (FStar_Format.hardline)::_169_589)
in (head)::_169_590)
in (FStar_List.append prefix _169_591))
in (FStar_All.pipe_left FStar_Format.reduce _169_592)))))))))
end))
in (

let docs = (FStar_List.map (fun _75_758 -> (match (_75_758) with
| (x, s, m) -> begin
(let _169_595 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _169_594 = (for1_mod true ((x), (s), (m)))
in ((_169_595), (_169_594))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _169_602 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _169_602 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _169_607 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _169_607 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





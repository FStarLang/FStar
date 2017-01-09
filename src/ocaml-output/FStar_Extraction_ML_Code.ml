
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

let doc = (let _177_119 = (let _177_118 = (FStar_Format.combine (FStar_Format.text " * ") doc)
in (FStar_Format.hbox _177_118))
in (FStar_Format.parens _177_119))
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
in (let _177_121 = (let _177_120 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.hbox _177_120))
in (FStar_Format.parens _177_121)))
end)
in (

let name = if (is_standard_type name) then begin
(let _177_123 = (let _177_122 = (as_standard_type name)
in (FStar_Option.get _177_122))
in (Prims.snd _177_123))
end else begin
(ptsym currentModule name)
end
in (let _177_124 = (FStar_Format.reduce1 ((args)::((FStar_Format.text name))::[]))
in (FStar_Format.hbox _177_124))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _78_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _177_126 = (let _177_125 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox _177_125))
in (maybe_paren outer t_prio_fun _177_126))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _177_130 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _177_130)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _177_151 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc)::[]))
in (FStar_Format.parens _177_151))
end else begin
(let _177_152 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc))::[]))
in (FStar_Format.parens _177_152))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _177_154 = (string_of_mlconstant c)
in (FStar_Format.text _177_154))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _78_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _177_155 = (ptsym currentModule path)
in (FStar_Format.text _177_155))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _78_269 -> (match (_78_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _177_160 = (let _177_159 = (let _177_158 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _177_158))
in (_177_159)::((FStar_Format.text "="))::(doc)::[])
in (FStar_Format.reduce1 _177_160)))
end))
in (let _177_162 = (let _177_161 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _177_161))
in (FStar_Format.cbrackets _177_162)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _177_164 = (let _177_163 = (as_standard_constructor ctor)
in (FStar_Option.get _177_163))
in (Prims.snd _177_164))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _177_166 = (let _177_165 = (as_standard_constructor ctor)
in (FStar_Option.get _177_165))
in (Prims.snd _177_166))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (_78_288, _78_290) -> begin
(let _177_170 = (let _177_169 = (let _177_168 = (let _177_167 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens _177_167))
in (_177_168)::[])
in ((FStar_Format.text name))::_177_169)
in (FStar_Format.reduce1 _177_170))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (let _177_172 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _177_172))) es)
in (

let docs = (let _177_173 = (FStar_Format.combine (FStar_Format.text ", ") docs)
in (FStar_Format.parens _177_173))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, _78_300, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _177_176 = (let _177_175 = (let _177_174 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_177_174)::[])
in (FStar_Format.hardline)::_177_175)
in (FStar_Format.reduce _177_176))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _177_181 = (let _177_180 = (let _177_179 = (let _177_178 = (let _177_177 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body)::[]))
in (_177_177)::[])
in (doc)::_177_178)
in (pre)::_177_179)
in (FStar_Format.combine FStar_Format.hardline _177_180))
in (FStar_Format.parens _177_181)))))
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
in (let _177_182 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _177_182))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.reduce ((e)::((FStar_Format.text "."))::((FStar_Format.text (Prims.snd f)))::[]))
end else begin
(let _177_187 = (let _177_186 = (let _177_185 = (let _177_184 = (let _177_183 = (ptsym currentModule f)
in (FStar_Format.text _177_183))
in (_177_184)::[])
in ((FStar_Format.text "."))::_177_185)
in (e)::_177_186)
in (FStar_Format.reduce _177_187))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _177_198 = (let _177_197 = (let _177_196 = (let _177_195 = (match (xt) with
| Some (xxt) -> begin
(let _177_194 = (let _177_193 = (let _177_192 = (doc_of_mltype currentModule outer xxt)
in (_177_192)::[])
in ((FStar_Format.text " : "))::_177_193)
in (FStar_Format.reduce1 _177_194))
end
| _78_418 -> begin
(FStar_Format.text "")
end)
in (_177_195)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::_177_196)
in ((FStar_Format.text "("))::_177_197)
in (FStar_Format.reduce1 _177_198))
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

let doc = (let _177_202 = (let _177_201 = (let _177_200 = (FStar_Format.reduce1 ids)
in (_177_200)::((FStar_Format.text "->"))::(body)::[])
in ((FStar_Format.text "fun"))::_177_201)
in (FStar_Format.reduce1 _177_202))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _177_206 = (let _177_205 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _177_204 = (let _177_203 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (_177_203)::((FStar_Format.text "end"))::[])
in (_177_205)::_177_204))
in (FStar_Format.combine FStar_Format.hardline _177_206))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _177_214 = (let _177_213 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _177_212 = (let _177_211 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _177_210 = (let _177_209 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (let _177_208 = (let _177_207 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (_177_207)::((FStar_Format.text "end"))::[])
in (_177_209)::_177_208))
in (_177_211)::_177_210))
in (_177_213)::_177_212))
in (FStar_Format.combine FStar_Format.hardline _177_214))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _177_215 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond))::((FStar_Format.text "with"))::[]))
in (_177_215)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _177_219 = (let _177_218 = (let _177_217 = (let _177_216 = (ptctor currentModule exn)
in (FStar_Format.text _177_216))
in (_177_217)::[])
in ((FStar_Format.text "raise"))::_177_218)
in (FStar_Format.reduce1 _177_219))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _177_226 = (let _177_225 = (let _177_224 = (let _177_220 = (ptctor currentModule exn)
in (FStar_Format.text _177_220))
in (let _177_223 = (let _177_222 = (let _177_221 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens _177_221))
in (_177_222)::[])
in (_177_224)::_177_223))
in ((FStar_Format.text "raise"))::_177_225)
in (FStar_Format.reduce1 _177_226)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _177_233 = (let _177_232 = (let _177_231 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _177_230 = (let _177_229 = (let _177_228 = (let _177_227 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _177_227))
in (_177_228)::[])
in ((FStar_Format.text "with"))::_177_229)
in (_177_231)::_177_230))
in ((FStar_Format.text "try"))::_177_232)
in (FStar_Format.combine FStar_Format.hardline _177_233))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _78_472 = (let _177_238 = (as_bin_op p)
in (FStar_Option.get _177_238))
in (match (_78_472) with
| (_78_469, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (FStar_Format.reduce1 ((e1)::((FStar_Format.text txt))::(e2)::[]))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _78_482 = (let _177_242 = (as_uni_op p)
in (FStar_Option.get _177_242))
in (match (_78_482) with
| (_78_480, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc = (FStar_Format.reduce1 (((FStar_Format.text txt))::((FStar_Format.parens e1))::[]))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _177_245 = (string_of_mlconstant c)
in (FStar_Format.text _177_245))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _78_499 -> (match (_78_499) with
| (name, p) -> begin
(let _177_253 = (let _177_252 = (let _177_248 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _177_248))
in (let _177_251 = (let _177_250 = (let _177_249 = (doc_of_pattern currentModule p)
in (_177_249)::[])
in ((FStar_Format.text "="))::_177_250)
in (_177_252)::_177_251))
in (FStar_Format.reduce1 _177_253))
end))
in (let _177_255 = (let _177_254 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _177_254))
in (FStar_Format.cbrackets _177_255)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _177_257 = (let _177_256 = (as_standard_constructor ctor)
in (FStar_Option.get _177_256))
in (Prims.snd _177_257))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _177_259 = (let _177_258 = (as_standard_constructor ctor)
in (FStar_Option.get _177_258))
in (Prims.snd _177_259))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _177_265 = (let _177_264 = (let _177_260 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _177_260))
in (let _177_263 = (let _177_262 = (let _177_261 = (doc_of_pattern currentModule xs)
in (_177_261)::[])
in ((FStar_Format.text "::"))::_177_262)
in (_177_264)::_177_263))
in (FStar_Format.reduce _177_265))
end
| (_78_516, (FStar_Extraction_ML_Syntax.MLP_Tuple (_78_518))::[]) -> begin
(let _177_269 = (let _177_268 = (let _177_267 = (let _177_266 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _177_266))
in (_177_267)::[])
in ((FStar_Format.text name))::_177_268)
in (FStar_Format.reduce1 _177_269))
end
| _78_523 -> begin
(let _177_274 = (let _177_273 = (let _177_272 = (let _177_271 = (let _177_270 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") _177_270))
in (FStar_Format.parens _177_271))
in (_177_272)::[])
in ((FStar_Format.text name))::_177_273)
in (FStar_Format.reduce1 _177_274))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _177_275 = (FStar_Format.combine (FStar_Format.text ", ") ps)
in (FStar_Format.parens _177_275)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (FStar_Format.combine (FStar_Format.text " | ") ps)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _78_536 -> (match (_78_536) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _177_280 = (let _177_279 = (let _177_278 = (doc_of_pattern currentModule p)
in (_177_278)::[])
in ((FStar_Format.text "|"))::_177_279)
in (FStar_Format.reduce1 _177_280))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _177_283 = (let _177_282 = (let _177_281 = (doc_of_pattern currentModule p)
in (_177_281)::((FStar_Format.text "when"))::(c)::[])
in ((FStar_Format.text "|"))::_177_282)
in (FStar_Format.reduce1 _177_283)))
end)
in (let _177_287 = (let _177_286 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (let _177_285 = (let _177_284 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_177_284)::((FStar_Format.text "end"))::[])
in (_177_286)::_177_285))
in (FStar_Format.combine FStar_Format.hardline _177_287)))
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
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty)::[])))
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
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty)::[])))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _177_295 = (let _177_294 = (let _177_293 = (FStar_Format.reduce1 ids)
in (_177_293)::(ty_annot)::((FStar_Format.text "="))::(e)::[])
in ((FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name)))::_177_294)
in (FStar_Format.reduce1 _177_295))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (FStar_Format.reduce1 ((if (i = (Prims.parse_int "0")) then begin
letdoc
end else begin
(FStar_Format.text "and")
end)::(doc)::[]))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _78_600 -> (match (_78_600) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))))::[])))
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
in (let _177_306 = (FStar_Format.combine (FStar_Format.text ", ") doc)
in (FStar_Format.parens _177_306)))
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
in (FStar_Format.reduce1 ((name)::((FStar_Format.text ":"))::(ty)::[]))))
end))
in (let _177_312 = (let _177_311 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") _177_311))
in (FStar_Format.cbrackets _177_312)))
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

let tys = (FStar_Format.combine (FStar_Format.text " * ") tys)
in (FStar_Format.reduce1 (((FStar_Format.text name))::((FStar_Format.text "of"))::(tys)::[]))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (FStar_Format.reduce1 (((FStar_Format.text "|"))::(d)::[]))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _177_319 = (let _177_318 = (let _177_317 = (let _177_316 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _177_316))
in (_177_317)::[])
in (tparams)::_177_318)
in (FStar_Format.reduce1 _177_319))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _177_321 = (let _177_320 = (FStar_Format.reduce1 ((doc)::((FStar_Format.text "="))::[]))
in (_177_320)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _177_321)))
end)))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > (Prims.parse_int "0")) then begin
(let _177_324 = (let _177_323 = (let _177_322 = (FStar_Format.combine (FStar_Format.text " \n and ") doc)
in (_177_322)::[])
in ((FStar_Format.text "type"))::_177_323)
in (FStar_Format.reduce1 _177_324))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _177_336 = (let _177_335 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (let _177_334 = (let _177_333 = (doc_of_sig currentModule subsig)
in (let _177_332 = (let _177_331 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (_177_331)::[])
in (_177_333)::_177_332))
in (_177_335)::_177_334))
in (FStar_Format.combine FStar_Format.hardline _177_336))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _177_337 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens _177_337))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_78_675, ty)) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text "val"))::((FStar_Format.text x))::((FStar_Format.text ": "))::(ty)::[])))
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
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _177_345 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens _177_345))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, _78_704, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _177_350 = (let _177_349 = (let _177_348 = (let _177_347 = (let _177_346 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_177_346)::[])
in ((FStar_Format.text "="))::_177_347)
in ((FStar_Format.text "_"))::_177_348)
in ((FStar_Format.text "let"))::_177_349)
in (FStar_Format.reduce1 _177_350))
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

let head = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc = (FStar_Option.map (fun _78_737 -> (match (_78_737) with
| (s, _78_736) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _177_367 = (let _177_366 = (let _177_365 = (let _177_364 = (FStar_Format.reduce sub)
in (_177_364)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_177_365)
in ((FStar_Format.cat head FStar_Format.hardline))::_177_366)
in (FStar_Format.reduce _177_367))))))))
end))
and for1_mod = (fun istop _78_750 -> (match (_78_750) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _177_370 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
((FStar_Format.text "module"))::((FStar_Format.text x))::[]
end else begin
if (not (istop)) then begin
((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end else begin
[]
end
end
in (FStar_Format.reduce1 _177_370))
in (

let tail = if (not (istop)) then begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
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
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end else begin
[]
end
in (let _177_380 = (let _177_379 = (let _177_378 = (let _177_377 = (let _177_376 = (let _177_375 = (let _177_374 = (let _177_373 = (FStar_Format.reduce sub)
in (_177_373)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_177_374)
in (FStar_Format.hardline)::_177_375)
in ((FStar_Format.text "open Prims"))::_177_376)
in (FStar_Format.hardline)::_177_377)
in (head)::_177_378)
in (FStar_List.append prefix _177_379))
in (FStar_All.pipe_left FStar_Format.reduce _177_380)))))))))
end))
in (

let docs = (FStar_List.map (fun _78_769 -> (match (_78_769) with
| (x, s, m) -> begin
(let _177_383 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _177_382 = (for1_mod true ((x), (s), (m)))
in ((_177_383), (_177_382))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _177_390 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _177_390 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _177_395 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _177_395 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





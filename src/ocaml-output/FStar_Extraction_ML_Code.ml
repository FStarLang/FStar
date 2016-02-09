
open Prims
# 30 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

# 30 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

type fixity =
| Prefix
| Postfix
| Infix of assoc

# 31 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let ___Infix____0 : fixity  ->  assoc = (fun projectee -> (match (projectee) with
| Infix (_77_3) -> begin
_77_3
end))

# 32 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

type opprec =
(Prims.int * fixity)

# 33 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

type level =
(opprec * assoc)

# 35 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

# 36 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

# 37 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let t_prio_name : (Prims.int * fixity) = (30, Postfix)

# 39 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_lambda : (Prims.int * fixity) = (5, Prefix)

# 40 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_if : (Prims.int * fixity) = (15, Prefix)

# 41 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_letin : (Prims.int * fixity) = (19, Prefix)

# 42 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_or : (Prims.int * fixity) = (20, Infix (Left))

# 43 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_and : (Prims.int * fixity) = (25, Infix (Left))

# 44 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_eq : (Prims.int * fixity) = (27, Infix (NonAssoc))

# 45 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_order : (Prims.int * fixity) = (29, Infix (NonAssoc))

# 46 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_op1 : (Prims.int * fixity) = (30, Infix (Left))

# 47 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_op2 : (Prims.int * fixity) = (40, Infix (Left))

# 48 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_op3 : (Prims.int * fixity) = (50, Infix (Left))

# 49 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_op4 : (Prims.int * fixity) = (60, Infix (Left))

# 50 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_comb : (Prims.int * fixity) = (70, Infix (Left))

# 51 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_bin_prio_seq : (Prims.int * fixity) = (100, Infix (Left))

# 52 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let e_app_prio : (Prims.int * fixity) = (10000, Infix (Left))

# 54 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

# 55 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

# 61 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 67 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 85 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 93 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _179_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _179_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

# 98 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 106 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 112 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

# 130 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

# 137 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let prim_types = []

# 140 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

# 148 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 152 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 159 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 163 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 170 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 174 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 181 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 185 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 192 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 196 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 215 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let ocaml_u8_codepoint : Prims.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

# 219 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 240 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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

# 264 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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
in (let doc = (let _179_106 = (let _179_105 = (FSharp_Format.combine (FSharp_Format.text " * ") doc)
in (FSharp_Format.hbox _179_105))
in (FSharp_Format.parens _179_106))
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
in (let _179_108 = (let _179_107 = (FSharp_Format.combine (FSharp_Format.text ", ") args)
in (FSharp_Format.hbox _179_107))
in (FSharp_Format.parens _179_108)))
end)
in (let name = if (is_standard_type name) then begin
(let _179_110 = (let _179_109 = (as_standard_type name)
in (FStar_Option.get _179_109))
in (Prims.snd _179_110))
end else begin
(ptsym currentModule name)
end
in (let _179_111 = (FSharp_Format.reduce1 ((args)::((FSharp_Format.text name))::[]))
in (FSharp_Format.hbox _179_111))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _77_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _179_113 = (let _179_112 = (FSharp_Format.reduce1 ((d1)::((FSharp_Format.text " -> "))::(d2)::[]))
in (FSharp_Format.hbox _179_112))
in (maybe_paren outer t_prio_fun _179_113))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FSharp_Format.text "obj")
end else begin
(FSharp_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FSharp_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

# 312 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _179_136 = (FSharp_Format.reduce (((FSharp_Format.text "Prims.checked_cast"))::(doc)::[]))
in (FSharp_Format.parens _179_136))
end else begin
(let _179_137 = (FSharp_Format.reduce (((FSharp_Format.text "Obj.magic "))::((FSharp_Format.parens doc))::[]))
in (FSharp_Format.parens _179_137))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (FSharp_Format.reduce ((d)::((FSharp_Format.text ";"))::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _179_139 = (string_of_mlconstant c)
in (FSharp_Format.text _179_139))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _77_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _179_140 = (ptsym currentModule path)
in (FSharp_Format.text _179_140))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _77_244 -> (match (_77_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _179_145 = (let _179_144 = (let _179_143 = (ptsym currentModule (path, name))
in (FSharp_Format.text _179_143))
in (_179_144)::((FSharp_Format.text "="))::(doc)::[])
in (FSharp_Format.reduce1 _179_145)))
end))
in (let _179_147 = (let _179_146 = (FStar_List.map for1 fields)
in (FSharp_Format.combine (FSharp_Format.text "; ") _179_146))
in (FSharp_Format.cbrackets _179_147)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _179_149 = (let _179_148 = (as_standard_constructor ctor)
in (FStar_Option.get _179_148))
in (Prims.snd _179_149))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _179_151 = (let _179_150 = (as_standard_constructor ctor)
in (FStar_Option.get _179_150))
in (Prims.snd _179_151))
end else begin
(ptctor currentModule ctor)
end
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(FSharp_Format.reduce (((FSharp_Format.parens x))::((FSharp_Format.text "::"))::(xs)::[]))
end
| (_77_263, _77_265) -> begin
(let _179_155 = (let _179_154 = (let _179_153 = (let _179_152 = (FSharp_Format.combine (FSharp_Format.text ", ") args)
in (FSharp_Format.parens _179_152))
in (_179_153)::[])
in ((FSharp_Format.text name))::_179_154)
in (FSharp_Format.reduce1 _179_155))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _179_156 = (FSharp_Format.combine (FSharp_Format.text ", ") docs)
in (FSharp_Format.parens _179_156))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _179_160 = (let _179_159 = (let _179_158 = (let _179_157 = (FSharp_Format.reduce1 (((FSharp_Format.text "in"))::(body)::[]))
in (_179_157)::[])
in (doc)::_179_158)
in (FSharp_Format.combine FSharp_Format.hardline _179_159))
in (FSharp_Format.parens _179_160))))
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
in (let _179_161 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _179_161))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FSharp_Format.reduce ((e)::((FSharp_Format.text "."))::((FSharp_Format.text (Prims.snd f)))::[]))
end else begin
(let _179_166 = (let _179_165 = (let _179_164 = (let _179_163 = (let _179_162 = (ptsym currentModule f)
in (FSharp_Format.text _179_162))
in (_179_163)::[])
in ((FSharp_Format.text "."))::_179_164)
in (e)::_179_165)
in (FSharp_Format.reduce _179_166))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _179_177 = (let _179_176 = (let _179_175 = (let _179_174 = (match (xt) with
| Some (xxt) -> begin
(let _179_173 = (let _179_172 = (let _179_171 = (doc_of_mltype currentModule outer xxt)
in (_179_171)::[])
in ((FSharp_Format.text " : "))::_179_172)
in (FSharp_Format.reduce1 _179_173))
end
| _77_340 -> begin
(FSharp_Format.text "")
end)
in (_179_174)::((FSharp_Format.text ")"))::[])
in ((FSharp_Format.text x))::_179_175)
in ((FSharp_Format.text "("))::_179_176)
in (FSharp_Format.reduce1 _179_177))
end else begin
(FSharp_Format.text x)
end)
in (let ids = (FStar_List.map (fun _77_346 -> (match (_77_346) with
| ((x, _77_343), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _179_181 = (let _179_180 = (let _179_179 = (FSharp_Format.reduce1 ids)
in (_179_179)::((FSharp_Format.text "->"))::(body)::[])
in ((FSharp_Format.text "fun"))::_179_180)
in (FSharp_Format.reduce1 _179_181))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _179_185 = (let _179_184 = (FSharp_Format.reduce1 (((FSharp_Format.text "if"))::(cond)::((FSharp_Format.text "then"))::((FSharp_Format.text "begin"))::[]))
in (let _179_183 = (let _179_182 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (_179_182)::((FSharp_Format.text "end"))::[])
in (_179_184)::_179_183))
in (FSharp_Format.combine FSharp_Format.hardline _179_185))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _179_193 = (let _179_192 = (FSharp_Format.reduce1 (((FSharp_Format.text "if"))::(cond)::((FSharp_Format.text "then"))::((FSharp_Format.text "begin"))::[]))
in (let _179_191 = (let _179_190 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _179_189 = (let _179_188 = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::((FSharp_Format.text "else"))::((FSharp_Format.text "begin"))::[]))
in (let _179_187 = (let _179_186 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (_179_186)::((FSharp_Format.text "end"))::[])
in (_179_188)::_179_187))
in (_179_190)::_179_189))
in (_179_192)::_179_191))
in (FSharp_Format.combine FSharp_Format.hardline _179_193))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _179_194 = (FSharp_Format.reduce1 (((FSharp_Format.text "match"))::((FSharp_Format.parens cond))::((FSharp_Format.text "with"))::[]))
in (_179_194)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _179_198 = (let _179_197 = (let _179_196 = (let _179_195 = (ptctor currentModule exn)
in (FSharp_Format.text _179_195))
in (_179_196)::[])
in ((FSharp_Format.text "raise"))::_179_197)
in (FSharp_Format.reduce1 _179_198))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _179_205 = (let _179_204 = (let _179_203 = (let _179_199 = (ptctor currentModule exn)
in (FSharp_Format.text _179_199))
in (let _179_202 = (let _179_201 = (let _179_200 = (FSharp_Format.combine (FSharp_Format.text ", ") args)
in (FSharp_Format.parens _179_200))
in (_179_201)::[])
in (_179_203)::_179_202))
in ((FSharp_Format.text "raise"))::_179_204)
in (FSharp_Format.reduce1 _179_205)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _179_214 = (let _179_213 = (FSharp_Format.reduce1 (((FSharp_Format.text "try"))::((FSharp_Format.text "begin"))::[]))
in (let _179_212 = (let _179_211 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _179_210 = (let _179_209 = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::((FSharp_Format.text "with"))::[]))
in (let _179_208 = (let _179_207 = (let _179_206 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _179_206))
in (_179_207)::[])
in (_179_209)::_179_208))
in (_179_211)::_179_210))
in (_179_213)::_179_212))
in (FSharp_Format.combine FSharp_Format.hardline _179_214))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule p e1 e2 -> (let _77_394 = (let _179_219 = (as_bin_op p)
in (FStar_Option.get _179_219))
in (match (_77_394) with
| (_77_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (FSharp_Format.reduce1 ((e1)::((FSharp_Format.text txt))::(e2)::[]))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule p e1 -> (let _77_404 = (let _179_223 = (as_uni_op p)
in (FStar_Option.get _179_223))
in (match (_77_404) with
| (_77_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (FSharp_Format.reduce1 (((FSharp_Format.text txt))::((FSharp_Format.parens e1))::[]))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FSharp_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_226 = (string_of_mlconstant c)
in (FSharp_Format.text _179_226))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _77_421 -> (match (_77_421) with
| (name, p) -> begin
(let _179_234 = (let _179_233 = (let _179_229 = (ptsym currentModule (path, name))
in (FSharp_Format.text _179_229))
in (let _179_232 = (let _179_231 = (let _179_230 = (doc_of_pattern currentModule p)
in (_179_230)::[])
in ((FSharp_Format.text "="))::_179_231)
in (_179_233)::_179_232))
in (FSharp_Format.reduce1 _179_234))
end))
in (let _179_236 = (let _179_235 = (FStar_List.map for1 fields)
in (FSharp_Format.combine (FSharp_Format.text "; ") _179_235))
in (FSharp_Format.cbrackets _179_236)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _179_238 = (let _179_237 = (as_standard_constructor ctor)
in (FStar_Option.get _179_237))
in (Prims.snd _179_238))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _179_240 = (let _179_239 = (as_standard_constructor ctor)
in (FStar_Option.get _179_239))
in (Prims.snd _179_240))
end else begin
(ptctor currentModule ctor)
end
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _179_245 = (let _179_244 = (doc_of_pattern currentModule x)
in (let _179_243 = (let _179_242 = (let _179_241 = (doc_of_pattern currentModule xs)
in (_179_241)::[])
in ((FSharp_Format.text "::"))::_179_242)
in (_179_244)::_179_243))
in (FSharp_Format.reduce _179_245))
end
| (_77_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_77_440)::[]) -> begin
(let _179_249 = (let _179_248 = (let _179_247 = (let _179_246 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _179_246))
in (_179_247)::[])
in ((FSharp_Format.text name))::_179_248)
in (FSharp_Format.reduce1 _179_249))
end
| _77_445 -> begin
(let _179_254 = (let _179_253 = (let _179_252 = (let _179_251 = (let _179_250 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine (FSharp_Format.text ", ") _179_250))
in (FSharp_Format.parens _179_251))
in (_179_252)::[])
in ((FSharp_Format.text name))::_179_253)
in (FSharp_Format.reduce1 _179_254))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _179_255 = (FSharp_Format.combine (FSharp_Format.text ", ") ps)
in (FSharp_Format.parens _179_255)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (FSharp_Format.combine (FSharp_Format.text " | ") ps)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FSharp_Format.doc = (fun currentModule _77_458 -> (match (_77_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _179_260 = (let _179_259 = (let _179_258 = (doc_of_pattern currentModule p)
in (_179_258)::[])
in ((FSharp_Format.text "|"))::_179_259)
in (FSharp_Format.reduce1 _179_260))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _179_263 = (let _179_262 = (let _179_261 = (doc_of_pattern currentModule p)
in (_179_261)::((FSharp_Format.text "when"))::(c)::[])
in ((FSharp_Format.text "|"))::_179_262)
in (FSharp_Format.reduce1 _179_263)))
end)
in (let _179_267 = (let _179_266 = (FSharp_Format.reduce1 ((case)::((FSharp_Format.text "->"))::((FSharp_Format.text "begin"))::[]))
in (let _179_265 = (let _179_264 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_179_264)::((FSharp_Format.text "end"))::[])
in (_179_266)::_179_265))
in (FSharp_Format.combine FSharp_Format.hardline _179_267)))
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
in (FSharp_Format.reduce1 (((FSharp_Format.text ":"))::(ty)::[])))
end)
end else begin
if top_level then begin
(match (tys) with
| (_77_498::_77_496, _77_501) -> begin
(FSharp_Format.text "")
end
| ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) (Prims.snd tys))
in (FSharp_Format.reduce1 (((FSharp_Format.text ":"))::(ty)::[])))
end)
end else begin
(FSharp_Format.text "")
end
end
in (let _179_275 = (let _179_274 = (let _179_273 = (FSharp_Format.reduce1 ids)
in (_179_273)::(ty_annot)::((FSharp_Format.text "="))::(e)::[])
in ((FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name)))::_179_274)
in (FSharp_Format.reduce1 _179_275))))))
end))
in (let letdoc = if rec_ then begin
(FSharp_Format.reduce1 (((FSharp_Format.text "let"))::((FSharp_Format.text "rec"))::[]))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (FSharp_Format.reduce1 ((if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end)::(doc)::[]))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

# 567 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

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
in (let _179_285 = (FSharp_Format.combine (FSharp_Format.text ", ") doc)
in (FSharp_Format.parens _179_285)))
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
in (FSharp_Format.reduce1 ((name)::((FSharp_Format.text ":"))::(ty)::[]))))
end))
in (let _179_291 = (let _179_290 = (FStar_List.map forfield fields)
in (FSharp_Format.combine (FSharp_Format.text "; ") _179_290))
in (FSharp_Format.cbrackets _179_291)))
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
in (let tys = (FSharp_Format.combine (FSharp_Format.text " * ") tys)
in (FSharp_Format.reduce1 (((FSharp_Format.text name))::((FSharp_Format.text "of"))::(tys)::[]))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (FSharp_Format.reduce1 (((FSharp_Format.text "|"))::(d)::[]))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _179_298 = (let _179_297 = (let _179_296 = (let _179_295 = (ptsym currentModule ([], x))
in (FSharp_Format.text _179_295))
in (_179_296)::[])
in (tparams)::_179_297)
in (FSharp_Format.reduce1 _179_298))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _179_300 = (let _179_299 = (FSharp_Format.reduce1 ((doc)::((FSharp_Format.text "="))::[]))
in (_179_299)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _179_300)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = if ((FStar_List.length doc) > 0) then begin
(let _179_303 = (let _179_302 = (let _179_301 = (FSharp_Format.combine (FSharp_Format.text " \n and ") doc)
in (_179_301)::[])
in ((FSharp_Format.text "type"))::_179_302)
in (FSharp_Format.reduce1 _179_303))
end else begin
(FSharp_Format.text "")
end
in doc))))

# 622 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FSharp_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _179_315 = (let _179_314 = (FSharp_Format.reduce1 (((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text "="))::[]))
in (let _179_313 = (let _179_312 = (doc_of_sig currentModule subsig)
in (let _179_311 = (let _179_310 = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[]))
in (_179_310)::[])
in (_179_312)::_179_311))
in (_179_314)::_179_313))
in (FSharp_Format.combine FSharp_Format.hardline _179_315))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _179_316 = (FSharp_Format.combine (FSharp_Format.text " * ") args)
in (FSharp_Format.parens _179_316))
in (FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::((FSharp_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_77_579, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (FSharp_Format.reduce1 (((FSharp_Format.text "val"))::((FSharp_Format.text x))::((FSharp_Format.text ": "))::(ty)::[])))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FSharp_Format.doc = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

# 652 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let doc_of_loc : Prims.int  ->  Prims.string  ->  FSharp_Format.doc = (fun lineno file -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
FSharp_Format.empty
end else begin
(FSharp_Format.reduce1 (((FSharp_Format.text "#"))::((FSharp_Format.num lineno))::((FSharp_Format.text (Prims.strcat (Prims.strcat "\"" (FStar_Util.replace_string file "\\" "\\\\")) "\"")))::[]))
end)

# 659 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FSharp_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _179_328 = (FSharp_Format.combine (FSharp_Format.text " * ") args)
in (FSharp_Format.parens _179_328))
in (FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::((FSharp_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _179_333 = (let _179_332 = (let _179_331 = (let _179_330 = (let _179_329 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_179_329)::[])
in ((FSharp_Format.text "="))::_179_330)
in ((FSharp_Format.text "_"))::_179_331)
in ((FSharp_Format.text "let"))::_179_332)
in (FSharp_Format.reduce1 _179_333))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (lineno, file) -> begin
(doc_of_loc lineno file)
end))

# 685 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FSharp_Format.doc = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

# 691 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FSharp_Format.doc) Prims.list = (fun _77_624 -> (match (_77_624) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _77_631 -> (match (_77_631) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (FSharp_Format.reduce1 (((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text ":"))::((FSharp_Format.text "sig"))::[]))
in (let tail = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[]))
in (let doc = (FStar_Option.map (fun _77_637 -> (match (_77_637) with
| (s, _77_636) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _179_350 = (let _179_349 = (let _179_348 = (let _179_347 = (FSharp_Format.reduce sub)
in (_179_347)::((FSharp_Format.cat tail FSharp_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end))::_179_348)
in ((FSharp_Format.cat head FSharp_Format.hardline))::_179_349)
in (FSharp_Format.reduce _179_350)))))))
end))
and for1_mod = (fun istop _77_650 -> (match (_77_650) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _179_353 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
((FSharp_Format.text "module"))::((FSharp_Format.text x))::[]
end else begin
if (not (istop)) then begin
((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text "="))::((FSharp_Format.text "struct"))::[]
end else begin
[]
end
end
in (FSharp_Format.reduce1 _179_353))
in (let tail = if (not (istop)) then begin
(FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[]))
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
((FSharp_Format.cat (FSharp_Format.text "#light \"off\"") FSharp_Format.hardline))::[]
end else begin
[]
end
in (let _179_363 = (let _179_362 = (let _179_361 = (let _179_360 = (let _179_359 = (let _179_358 = (let _179_357 = (let _179_356 = (FSharp_Format.reduce sub)
in (_179_356)::((FSharp_Format.cat tail FSharp_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end))::_179_357)
in (FSharp_Format.hardline)::_179_358)
in ((FSharp_Format.text "open Prims"))::_179_359)
in (FSharp_Format.hardline)::_179_360)
in (head)::_179_361)
in (FStar_List.append prefix _179_362))
in (FStar_All.pipe_left FSharp_Format.reduce _179_363))))))))
end))
in (let docs = (FStar_List.map (fun _77_668 -> (match (_77_668) with
| (x, s, m) -> begin
(let _179_365 = (for1_mod true (x, s, m))
in (x, _179_365))
end)) mllib)
in docs))
end))

# 739 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FSharp_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 743 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let string_of_mlexpr : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun env e -> (let doc = (let _179_372 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _179_372 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

# 747 "D:\\workspace\\universes\\FStar\\src\\extraction\\codegen.fs"

let string_of_mlty : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun env e -> (let doc = (let _179_377 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _179_377 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





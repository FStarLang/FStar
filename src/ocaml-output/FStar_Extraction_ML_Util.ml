
open Prims
open FStar_Pervasives

let codegen_fsharp : unit  ->  Prims.bool = (fun uu____6 -> (

let uu____7 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____7 (FStar_Pervasives_Native.Some (FStar_Options.FSharp)))))


let pruneNones : 'a . 'a FStar_Pervasives_Native.option Prims.list  ->  'a Prims.list = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| FStar_Pervasives_Native.Some (xs) -> begin
(xs)::ll
end
| FStar_Pervasives_Native.None -> begin
ll
end)) l []))


let mk_range_mle : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("mk_range")))))


let dummy_range_mle : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("FStar")::("Range")::[]), ("dummyRange")))))


let mlconst_of_const' : FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun sctt -> (match (sctt) with
| FStar_Const.Const_effect -> begin
(failwith "Unsupported constant")
end
| FStar_Const.Const_range (uu____76) -> begin
FStar_Extraction_ML_Syntax.MLC_Unit
end
| FStar_Const.Const_unit -> begin
FStar_Extraction_ML_Syntax.MLC_Unit
end
| FStar_Const.Const_char (c) -> begin
FStar_Extraction_ML_Syntax.MLC_Char (c)
end
| FStar_Const.Const_int (s, i) -> begin
FStar_Extraction_ML_Syntax.MLC_Int (((s), (i)))
end
| FStar_Const.Const_bool (b) -> begin
FStar_Extraction_ML_Syntax.MLC_Bool (b)
end
| FStar_Const.Const_float (d) -> begin
FStar_Extraction_ML_Syntax.MLC_Float (d)
end
| FStar_Const.Const_bytearray (bytes, uu____106) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (s, uu____112) -> begin
FStar_Extraction_ML_Syntax.MLC_String (s)
end
| FStar_Const.Const_range_of -> begin
(failwith "Unhandled constant: range_of/set_range_of")
end
| FStar_Const.Const_set_range_of -> begin
(failwith "Unhandled constant: range_of/set_range_of")
end
| FStar_Const.Const_reify -> begin
(failwith "Unhandled constant: reify/reflect")
end
| FStar_Const.Const_reflect (uu____118) -> begin
(failwith "Unhandled constant: reify/reflect")
end))


let mlconst_of_const : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> (FStar_All.try_with (fun uu___282_132 -> (match (()) with
| () -> begin
(mlconst_of_const' c)
end)) (fun uu___281_135 -> (

let uu____136 = (

let uu____138 = (FStar_Range.string_of_range p)
in (

let uu____140 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " uu____138 uu____140)))
in (failwith uu____136)))))


let mlexpr_of_range : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun r -> (

let cint = (fun i -> (

let uu____157 = (

let uu____158 = (

let uu____159 = (

let uu____171 = (FStar_Util.string_of_int i)
in ((uu____171), (FStar_Pervasives_Native.None)))
in FStar_Extraction_ML_Syntax.MLC_Int (uu____159))
in (FStar_All.pipe_right uu____158 (fun _0_1 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_1))))
in (FStar_All.pipe_right uu____157 (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty))))
in (

let cstr = (fun s -> (

let uu____192 = (FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String (s)) (fun _0_2 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_2)))
in (FStar_All.pipe_right uu____192 (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty))))
in (

let uu____193 = (

let uu____200 = (

let uu____203 = (

let uu____204 = (FStar_Range.file_of_range r)
in (FStar_All.pipe_right uu____204 cstr))
in (

let uu____207 = (

let uu____210 = (

let uu____211 = (

let uu____213 = (FStar_Range.start_of_range r)
in (FStar_All.pipe_right uu____213 FStar_Range.line_of_pos))
in (FStar_All.pipe_right uu____211 cint))
in (

let uu____216 = (

let uu____219 = (

let uu____220 = (

let uu____222 = (FStar_Range.start_of_range r)
in (FStar_All.pipe_right uu____222 FStar_Range.col_of_pos))
in (FStar_All.pipe_right uu____220 cint))
in (

let uu____225 = (

let uu____228 = (

let uu____229 = (

let uu____231 = (FStar_Range.end_of_range r)
in (FStar_All.pipe_right uu____231 FStar_Range.line_of_pos))
in (FStar_All.pipe_right uu____229 cint))
in (

let uu____234 = (

let uu____237 = (

let uu____238 = (

let uu____240 = (FStar_Range.end_of_range r)
in (FStar_All.pipe_right uu____240 FStar_Range.col_of_pos))
in (FStar_All.pipe_right uu____238 cint))
in (uu____237)::[])
in (uu____228)::uu____234))
in (uu____219)::uu____225))
in (uu____210)::uu____216))
in (uu____203)::uu____207))
in ((mk_range_mle), (uu____200)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____193)))))


let mlexpr_of_const : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun p c -> (match (c) with
| FStar_Const.Const_range (r) -> begin
(mlexpr_of_range r)
end
| uu____257 -> begin
(

let uu____258 = (mlconst_of_const p c)
in FStar_Extraction_ML_Syntax.MLE_Const (uu____258))
end))


let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst1 t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let uu____286 = (FStar_Util.find_opt (fun uu____302 -> (match (uu____302) with
| (y, uu____310) -> begin
(Prims.op_Equality y x)
end)) subst1)
in (match (uu____286) with
| FStar_Pervasives_Native.Some (ts) -> begin
(FStar_Pervasives_Native.snd ts)
end
| FStar_Pervasives_Native.None -> begin
t
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____334 = (

let uu____341 = (subst_aux subst1 t1)
in (

let uu____342 = (subst_aux subst1 t2)
in ((uu____341), (f), (uu____342))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____334))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(

let uu____349 = (

let uu____356 = (FStar_List.map (subst_aux subst1) args)
in ((uu____356), (path)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____349))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____364 = (FStar_List.map (subst_aux subst1) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____364))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
t
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
t
end))


let try_subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option = (fun uu____380 args -> (match (uu____380) with
| (formals, t) -> begin
(match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____392 -> begin
(

let uu____394 = (

let uu____395 = (FStar_List.zip formals args)
in (subst_aux uu____395 t))
in FStar_Pervasives_Native.Some (uu____394))
end)
end))


let subst : (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty)  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun ts args -> (

let uu____427 = (try_subst ts args)
in (match (uu____427) with
| FStar_Pervasives_Native.None -> begin
(failwith "Substitution must be fully applied (see GitHub issue #490)")
end
| FStar_Pervasives_Native.Some (t) -> begin
t
end)))


let udelta_unfold : FStar_Extraction_ML_UEnv.uenv  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option = (fun g uu___274_444 -> (match (uu___274_444) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n1) -> begin
(

let uu____453 = (FStar_Extraction_ML_UEnv.lookup_ty_const g n1)
in (match (uu____453) with
| FStar_Pervasives_Native.Some (ts) -> begin
(

let uu____459 = (try_subst ts args)
in (match (uu____459) with
| FStar_Pervasives_Native.None -> begin
(

let uu____464 = (

let uu____466 = (FStar_Extraction_ML_Syntax.string_of_mlpath n1)
in (

let uu____468 = (FStar_Util.string_of_int (FStar_List.length args))
in (

let uu____470 = (FStar_Util.string_of_int (FStar_List.length (FStar_Pervasives_Native.fst ts)))
in (FStar_Util.format3 "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)" uu____466 uu____468 uu____470))))
in (failwith uu____464))
end
| FStar_Pervasives_Native.Some (r) -> begin
FStar_Pervasives_Native.Some (r)
end))
end
| uu____477 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____480 -> begin
FStar_Pervasives_Native.None
end))


let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_PURE, uu____494) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| uu____498 -> begin
false
end))


let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun uu___275_510 -> (match (uu___275_510) with
| FStar_Extraction_ML_Syntax.E_PURE -> begin
"Pure"
end
| FStar_Extraction_ML_Syntax.E_GHOST -> begin
"Ghost"
end
| FStar_Extraction_ML_Syntax.E_IMPURE -> begin
"Impure"
end))


let join : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_PURE) -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_PURE) -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| (FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.E_PURE) -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____531 -> begin
(

let uu____536 = (

let uu____538 = (FStar_Range.string_of_range r)
in (

let uu____540 = (eff_to_string f)
in (

let uu____542 = (eff_to_string f')
in (FStar_Util.format3 "Impossible (%s): Inconsistent effects %s and %s" uu____538 uu____540 uu____542))))
in (failwith uu____536))
end))


let join_l : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r fs -> (FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs))


let mk_ty_fun : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (FStar_List.fold_right (fun uu____585 t -> (match (uu____585) with
| (uu____592, t0) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((t0), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end)))


type unfold_t =
FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option


let rec type_leq_c : unfold_t  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) = (fun unfold_ty e t t' -> (match (((t), (t'))) with
| (FStar_Extraction_ML_Syntax.MLTY_Var (x), FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
(match ((Prims.op_Equality x y)) with
| true -> begin
((true), (e))
end
| uu____678 -> begin
((false), (FStar_Pervasives_Native.None))
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(

let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| uu____720 -> begin
(

let e1 = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body1) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((FStar_List.append xs ys)), (body1)))
end
| uu____757 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((xs), (body)))
end)
in (

let uu____765 = (mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____765 e1)))
end))
in (match (e) with
| FStar_Pervasives_Native.Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((x)::xs, body); FStar_Extraction_ML_Syntax.mlty = uu____776; FStar_Extraction_ML_Syntax.loc = uu____777}) -> begin
(

let uu____802 = ((type_leq unfold_ty t1' t1) && (eff_leq f f'))
in (match (uu____802) with
| true -> begin
(match (((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_PURE) && (Prims.op_Equality f' FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
(

let uu____823 = (type_leq unfold_ty t2 t2')
in (match (uu____823) with
| true -> begin
(

let body1 = (

let uu____837 = (type_leq unfold_ty t2 FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____837) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____843 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t2')))))
end))
in (

let uu____845 = (

let uu____848 = (

let uu____849 = (

let uu____854 = (mk_ty_fun ((x)::[]) body1.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____854))
in (FStar_All.pipe_left uu____849 (FStar_Extraction_ML_Syntax.MLE_Fun ((((x)::[]), (body1))))))
in FStar_Pervasives_Native.Some (uu____848))
in ((true), (uu____845))))
end
| uu____886 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____892 -> begin
(

let uu____894 = (

let uu____902 = (

let uu____905 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) uu____905))
in (type_leq_c unfold_ty uu____902 t2 t2'))
in (match (uu____894) with
| (ok, body1) -> begin
(

let res = (match (body1) with
| FStar_Pervasives_Native.Some (body2) -> begin
(

let uu____932 = (mk_fun ((x)::[]) body2)
in FStar_Pervasives_Native.Some (uu____932))
end
| uu____943 -> begin
FStar_Pervasives_Native.None
end)
in ((ok), (res)))
end))
end)
end
| uu____949 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____955 -> begin
(

let uu____958 = (((type_leq unfold_ty t1' t1) && (eff_leq f f')) && (type_leq unfold_ty t2 t2'))
in (match (uu____958) with
| true -> begin
((true), (e))
end
| uu____978 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
(match ((Prims.op_Equality path path')) with
| true -> begin
(

let uu____1004 = (FStar_List.forall2 (type_leq unfold_ty) args args')
in (match (uu____1004) with
| true -> begin
((true), (e))
end
| uu____1021 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____1027 -> begin
(

let uu____1029 = (unfold_ty t)
in (match (uu____1029) with
| FStar_Pervasives_Native.Some (t1) -> begin
(type_leq_c unfold_ty e t1 t')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1044 = (unfold_ty t')
in (match (uu____1044) with
| FStar_Pervasives_Native.None -> begin
((false), (FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.Some (t'1) -> begin
(type_leq_c unfold_ty e t t'1)
end))
end))
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Tuple (ts), FStar_Extraction_ML_Syntax.MLTY_Tuple (ts')) -> begin
(

let uu____1069 = (FStar_List.forall2 (type_leq unfold_ty) ts ts')
in (match (uu____1069) with
| true -> begin
((true), (e))
end
| uu____1086 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((true), (e))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (uu____1096), uu____1097) -> begin
(

let uu____1104 = (unfold_ty t)
in (match (uu____1104) with
| FStar_Pervasives_Native.Some (t1) -> begin
(type_leq_c unfold_ty e t1 t')
end
| uu____1119 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (uu____1126, FStar_Extraction_ML_Syntax.MLTY_Named (uu____1127)) -> begin
(

let uu____1134 = (unfold_ty t')
in (match (uu____1134) with
| FStar_Pervasives_Native.Some (t'1) -> begin
(type_leq_c unfold_ty e t t'1)
end
| uu____1149 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Erased, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((true), (e))
end
| uu____1160 -> begin
((false), (FStar_Pervasives_Native.None))
end))
and type_leq : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (

let uu____1175 = (type_leq_c g FStar_Pervasives_Native.None t1 t2)
in (FStar_All.pipe_right uu____1175 FStar_Pervasives_Native.fst)))


let rec erase_effect_annotations : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____1206 = (

let uu____1213 = (erase_effect_annotations t1)
in (

let uu____1214 = (erase_effect_annotations t2)
in ((uu____1213), (FStar_Extraction_ML_Syntax.E_PURE), (uu____1214))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____1206))
end
| uu____1215 -> begin
t
end))


let is_type_abstraction : 'a 'b 'c . (('a, 'b) FStar_Util.either * 'c) Prims.list  ->  Prims.bool = (fun uu___276_1243 -> (match (uu___276_1243) with
| ((FStar_Util.Inl (uu____1255), uu____1256))::uu____1257 -> begin
true
end
| uu____1281 -> begin
false
end))


let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.bool = (fun uu____1307 -> (match (uu____1307) with
| (ns, n1) -> begin
(

let uu____1327 = (FStar_Util.concat_l "." (FStar_List.append ns ((n1)::[])))
in (FStar_Parser_Const.is_tuple_datacon_string uu____1327))
end))


let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(

let uu____1345 = (is_xtuple mlp)
in (match (uu____1345) with
| true -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| uu____1348 -> begin
e
end))
end
| uu____1350 -> begin
e
end))


let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun uu___277_1361 -> (match (uu___277_1361) with
| (f)::uu____1368 -> begin
(

let uu____1371 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (uu____1371) with
| (ns, uu____1382) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id1 -> id1.FStar_Ident.idText)))
end))
end
| uu____1395 -> begin
(failwith "impos")
end))


let record_fields : 'a . FStar_Ident.lident Prims.list  ->  'a Prims.list  ->  (Prims.string * 'a) Prims.list = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.ident.FStar_Ident.idText), (e))) fs vs))


let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.bool = (fun uu____1459 -> (match (uu____1459) with
| (ns, n1) -> begin
(

let uu____1479 = (FStar_Util.concat_l "." (FStar_List.append ns ((n1)::[])))
in (FStar_Parser_Const.is_tuple_constructor_string uu____1479))
end))


let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(

let uu____1497 = (is_xtuple_ty mlp)
in (match (uu____1497) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| uu____1500 -> begin
t
end))
end
| uu____1502 -> begin
t
end))


let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> (

let uu____1516 = (codegen_fsharp ())
in (match (uu____1516) with
| true -> begin
(FStar_String.concat "." ns)
end
| uu____1521 -> begin
(FStar_String.concat "_" ns)
end)))


let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun uu____1538 -> (match (uu____1538) with
| (ns, n1) -> begin
(

let uu____1558 = (codegen_fsharp ())
in (match (uu____1558) with
| true -> begin
(FStar_String.concat "." (FStar_List.append ns ((n1)::[])))
end
| uu____1566 -> begin
(FStar_String.concat "_" (FStar_List.append ns ((n1)::[])))
end))
end))


let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (

let uu____1586 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in ((uu____1586), (l.FStar_Ident.ident.FStar_Ident.idText))))


let rec erasableType : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun unfold_ty t -> (

let uu____1620 = (FStar_Extraction_ML_UEnv.erasableTypeNoDelta t)
in (match (uu____1620) with
| true -> begin
true
end
| uu____1625 -> begin
(

let uu____1627 = (unfold_ty t)
in (match (uu____1627) with
| FStar_Pervasives_Native.Some (t1) -> begin
(erasableType unfold_ty t1)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end)))


let rec eraseTypeDeep : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun unfold_ty t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
(match ((Prims.op_Equality etag FStar_Extraction_ML_Syntax.E_PURE)) with
| true -> begin
(

let uu____1657 = (

let uu____1664 = (eraseTypeDeep unfold_ty tyd)
in (

let uu____1668 = (eraseTypeDeep unfold_ty tycd)
in ((uu____1664), (etag), (uu____1668))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____1657))
end
| uu____1672 -> begin
t
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
(

let uu____1680 = (erasableType unfold_ty t)
in (match (uu____1680) with
| true -> begin
FStar_Extraction_ML_UEnv.erasedContent
end
| uu____1686 -> begin
(

let uu____1688 = (

let uu____1695 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in ((uu____1695), (mlp)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____1688))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(

let uu____1706 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____1706))
end
| uu____1712 -> begin
t
end))


let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_Equality")))))


let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (

let uu____1723 = (

let uu____1728 = (mk_ty_fun (((("x"), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::((("y"), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty uu____1728))
in (FStar_All.pipe_left uu____1723 (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_AmpAmp"))))))


let conjoin : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e1 e2 -> (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_App (((prims_op_amp_amp), ((e1)::(e2)::[]))))))


let conjoin_opt : FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option = (fun e1 e2 -> (match (((e1), (e2))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some (x)
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (x)) -> begin
FStar_Pervasives_Native.Some (x)
end
| (FStar_Pervasives_Native.Some (x), FStar_Pervasives_Native.Some (y)) -> begin
(

let uu____1816 = (conjoin x y)
in FStar_Pervasives_Native.Some (uu____1816))
end))


let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (

let pos = (FStar_Range.start_of_range r)
in (

let line = (FStar_Range.line_of_pos pos)
in (

let uu____1832 = (FStar_Range.file_of_range r)
in ((line), (uu____1832))))))


let rec doms_and_cod : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1855, b) -> begin
(

let uu____1857 = (doms_and_cod b)
in (match (uu____1857) with
| (ds, c) -> begin
(((a)::ds), (c))
end))
end
| uu____1878 -> begin
(([]), (t))
end))


let argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (

let uu____1891 = (doms_and_cod t)
in (FStar_Pervasives_Native.fst uu____1891)))


let rec uncurry_mlty_fun : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1919, b) -> begin
(

let uu____1921 = (uncurry_mlty_fun b)
in (match (uu____1921) with
| (args, res) -> begin
(((a)::args), (res))
end))
end
| uu____1942 -> begin
(([]), (t))
end))

exception NoTacticEmbedding of (Prims.string)


let uu___is_NoTacticEmbedding : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoTacticEmbedding (uu____1958) -> begin
true
end
| uu____1961 -> begin
false
end))


let __proj__NoTacticEmbedding__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| NoTacticEmbedding (uu____1972) -> begin
uu____1972
end))


let not_implemented_warning : FStar_Range.range  ->  Prims.string  ->  Prims.string  ->  unit = (fun r t msg -> (

let uu____1994 = (

let uu____2000 = (FStar_Util.format2 "Plugin %s will not run natively because %s.\n" t msg)
in ((FStar_Errors.Warning_CallNotImplementedAsWarning), (uu____2000)))
in (FStar_Errors.log_issue r uu____1994)))

type emb_loc =
| Syntax_term
| Refl_emb
| NBE_t
| NBERefl_emb


let uu___is_Syntax_term : emb_loc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Syntax_term -> begin
true
end
| uu____2013 -> begin
false
end))


let uu___is_Refl_emb : emb_loc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Refl_emb -> begin
true
end
| uu____2024 -> begin
false
end))


let uu___is_NBE_t : emb_loc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NBE_t -> begin
true
end
| uu____2035 -> begin
false
end))


let uu___is_NBERefl_emb : emb_loc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NBERefl_emb -> begin
true
end
| uu____2046 -> begin
false
end))


type wrapped_term =
(FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlexpr * Prims.int * Prims.bool)


let interpret_plugin_as_term_fun : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  Prims.int FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlexpr'  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlexpr * Prims.int * Prims.bool) FStar_Pervasives_Native.option = (fun tcenv fv t arity_opt ml_fv -> (

let fv_lid1 = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) tcenv t)
in (

let w = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
in (

let lid_to_name = (fun l -> (

let uu____2117 = (

let uu____2118 = (FStar_Extraction_ML_Syntax.mlpath_of_lident l)
in FStar_Extraction_ML_Syntax.MLE_Name (uu____2118))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____2117)))
in (

let lid_to_top_name = (fun l -> (

let uu____2125 = (

let uu____2126 = (FStar_Extraction_ML_Syntax.mlpath_of_lident l)
in FStar_Extraction_ML_Syntax.MLE_Name (uu____2126))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____2125)))
in (

let str_to_name = (fun s -> (

let uu____2135 = (FStar_Ident.lid_of_str s)
in (lid_to_name uu____2135)))
in (

let str_to_top_name = (fun s -> (

let uu____2144 = (FStar_Ident.lid_of_str s)
in (lid_to_top_name uu____2144)))
in (

let fstar_tc_nbe_prefix = (fun s -> (str_to_name (Prims.strcat "FStar_TypeChecker_NBETerm." s)))
in (

let fstar_syn_emb_prefix = (fun s -> (str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)))
in (

let fstar_refl_emb_prefix = (fun s -> (str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s)))
in (

let fstar_refl_nbeemb_prefix = (fun s -> (str_to_name (Prims.strcat "FStar_Reflection_NBEEmbeddings." s)))
in (

let fv_lid_embedded = (

let uu____2182 = (

let uu____2183 = (

let uu____2190 = (str_to_name "FStar_Ident.lid_of_str")
in (

let uu____2192 = (

let uu____2195 = (

let uu____2196 = (

let uu____2197 = (

let uu____2198 = (FStar_Ident.string_of_lid fv_lid1)
in FStar_Extraction_ML_Syntax.MLC_String (uu____2198))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____2197))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____2196))
in (uu____2195)::[])
in ((uu____2190), (uu____2192))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2183))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____2182))
in (

let emb_prefix = (fun uu___278_2213 -> (match (uu___278_2213) with
| Syntax_term -> begin
fstar_syn_emb_prefix
end
| Refl_emb -> begin
fstar_refl_emb_prefix
end
| NBE_t -> begin
fstar_tc_nbe_prefix
end
| NBERefl_emb -> begin
fstar_refl_nbeemb_prefix
end))
in (

let mk_tactic_interpretation = (fun l -> (match (l) with
| Syntax_term -> begin
"FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
end
| uu____2227 -> begin
"FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
end))
in (

let mk_from_tactic = (fun l -> (match (l) with
| Syntax_term -> begin
"FStar_Tactics_Native.from_tactic_"
end
| uu____2238 -> begin
"FStar_Tactics_Native.from_nbe_tactic_"
end))
in (

let mk_basic_embedding = (fun l s -> (emb_prefix l (Prims.strcat "e_" s)))
in (

let mk_arrow_as_prim_step = (fun l arity -> (

let uu____2267 = (

let uu____2269 = (FStar_Util.string_of_int arity)
in (Prims.strcat "arrow_as_prim_step_" uu____2269))
in (emb_prefix l uu____2267)))
in (

let mk_any_embedding = (fun l s -> (

let uu____2285 = (

let uu____2286 = (

let uu____2293 = (emb_prefix l "mk_any_emb")
in (

let uu____2295 = (

let uu____2298 = (str_to_name s)
in (uu____2298)::[])
in ((uu____2293), (uu____2295))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2286))
in (FStar_All.pipe_left w uu____2285)))
in (

let mk_lam = (fun nm e -> (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_Fun ((((((nm), (FStar_Extraction_ML_Syntax.MLTY_Top)))::[]), (e))))))
in (

let emb_arrow = (fun l e1 e2 -> (

let uu____2348 = (

let uu____2349 = (

let uu____2356 = (emb_prefix l "e_arrow")
in ((uu____2356), ((e1)::(e2)::[])))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2349))
in (FStar_All.pipe_left w uu____2348)))
in (

let known_type_constructors = (

let term_cs = (

let uu____2394 = (

let uu____2409 = (

let uu____2424 = (

let uu____2439 = (

let uu____2454 = (

let uu____2469 = (

let uu____2484 = (

let uu____2499 = (

let uu____2512 = (

let uu____2521 = (FStar_Parser_Const.mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange)
in ((uu____2521), ((Prims.parse_int "2")), ("tuple2")))
in ((uu____2512), (Syntax_term)))
in (

let uu____2535 = (

let uu____2550 = (

let uu____2563 = (

let uu____2572 = (FStar_Reflection_Data.fstar_refl_types_lid "term")
in ((uu____2572), ((Prims.parse_int "0")), ("term")))
in ((uu____2563), (Refl_emb)))
in (

let uu____2586 = (

let uu____2601 = (

let uu____2614 = (

let uu____2623 = (FStar_Reflection_Data.fstar_refl_types_lid "fv")
in ((uu____2623), ((Prims.parse_int "0")), ("fv")))
in ((uu____2614), (Refl_emb)))
in (

let uu____2637 = (

let uu____2652 = (

let uu____2665 = (

let uu____2674 = (FStar_Reflection_Data.fstar_refl_types_lid "binder")
in ((uu____2674), ((Prims.parse_int "0")), ("binder")))
in ((uu____2665), (Refl_emb)))
in (

let uu____2688 = (

let uu____2703 = (

let uu____2716 = (

let uu____2725 = (FStar_Reflection_Data.fstar_refl_syntax_lid "binders")
in ((uu____2725), ((Prims.parse_int "0")), ("binders")))
in ((uu____2716), (Refl_emb)))
in (

let uu____2739 = (

let uu____2754 = (

let uu____2767 = (

let uu____2776 = (FStar_Reflection_Data.fstar_refl_data_lid "exp")
in ((uu____2776), ((Prims.parse_int "0")), ("exp")))
in ((uu____2767), (Refl_emb)))
in (uu____2754)::[])
in (uu____2703)::uu____2739))
in (uu____2652)::uu____2688))
in (uu____2601)::uu____2637))
in (uu____2550)::uu____2586))
in (uu____2499)::uu____2535))
in (((((FStar_Parser_Const.option_lid), ((Prims.parse_int "1")), ("option"))), (Syntax_term)))::uu____2484)
in (((((FStar_Parser_Const.list_lid), ((Prims.parse_int "1")), ("list"))), (Syntax_term)))::uu____2469)
in (((((FStar_Parser_Const.norm_step_lid), ((Prims.parse_int "0")), ("norm_step"))), (Syntax_term)))::uu____2454)
in (((((FStar_Parser_Const.string_lid), ((Prims.parse_int "0")), ("string"))), (Syntax_term)))::uu____2439)
in (((((FStar_Parser_Const.unit_lid), ((Prims.parse_int "0")), ("unit"))), (Syntax_term)))::uu____2424)
in (((((FStar_Parser_Const.bool_lid), ((Prims.parse_int "0")), ("bool"))), (Syntax_term)))::uu____2409)
in (((((FStar_Parser_Const.int_lid), ((Prims.parse_int "0")), ("int"))), (Syntax_term)))::uu____2394)
in (

let nbe_cs = (FStar_List.map (fun uu___279_3083 -> (match (uu___279_3083) with
| (x, Syntax_term) -> begin
((x), (NBE_t))
end
| (x, Refl_emb) -> begin
((x), (NBERefl_emb))
end
| uu____3158 -> begin
(failwith "Impossible")
end)) term_cs)
in (fun uu___280_3184 -> (match (uu___280_3184) with
| Syntax_term -> begin
term_cs
end
| Refl_emb -> begin
term_cs
end
| uu____3199 -> begin
nbe_cs
end))))
in (

let is_known_type_constructor = (fun l fv1 n1 -> (FStar_Util.for_some (fun uu____3236 -> (match (uu____3236) with
| ((x, args, uu____3252), uu____3253) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (Prims.op_Equality n1 args))
end)) (known_type_constructors l)))
in (

let find_env_entry = (fun bv uu____3283 -> (match (uu____3283) with
| (bv', uu____3291) -> begin
(FStar_Syntax_Syntax.bv_eq bv bv')
end))
in (

let rec mk_embedding = (fun l env t2 -> (

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf tcenv t2)
in (

let uu____3325 = (

let uu____3326 = (FStar_Syntax_Subst.compress t3)
in uu____3326.FStar_Syntax_Syntax.n)
in (match (uu____3325) with
| FStar_Syntax_Syntax.Tm_name (bv) when (FStar_Util.for_some (find_env_entry bv) env) -> begin
(

let uu____3335 = (

let uu____3337 = (

let uu____3343 = (FStar_Util.find_opt (find_env_entry bv) env)
in (FStar_Util.must uu____3343))
in (FStar_Pervasives_Native.snd uu____3337))
in (FStar_All.pipe_left (mk_any_embedding l) uu____3335))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____3364) -> begin
(mk_embedding l env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t4, uu____3370, uu____3371) -> begin
(mk_embedding l env t4)
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::[], c) when (FStar_Syntax_Util.is_pure_comp c) -> begin
(

let uu____3444 = (FStar_Syntax_Subst.open_comp ((b)::[]) c)
in (match (uu____3444) with
| (bs, c1) -> begin
(

let t0 = (

let uu____3466 = (

let uu____3467 = (FStar_List.hd bs)
in (FStar_Pervasives_Native.fst uu____3467))
in uu____3466.FStar_Syntax_Syntax.sort)
in (

let t11 = (FStar_Syntax_Util.comp_result c1)
in (

let uu____3485 = (mk_embedding l env t0)
in (

let uu____3486 = (mk_embedding l env t11)
in (emb_arrow l uu____3485 uu____3486)))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow ((b)::(more)::bs, c) -> begin
(

let tail1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((more)::bs), (c)))) FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos)
in (

let t4 = (

let uu____3557 = (

let uu____3564 = (

let uu____3565 = (

let uu____3580 = (FStar_Syntax_Syntax.mk_Total tail1)
in (((b)::[]), (uu____3580)))
in FStar_Syntax_Syntax.Tm_arrow (uu____3565))
in (FStar_Syntax_Syntax.mk uu____3564))
in (uu____3557 FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos))
in (mk_embedding l env t4)))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3608) -> begin
(

let uu____3609 = (FStar_Syntax_Util.head_and_args t3)
in (match (uu____3609) with
| (head1, args) -> begin
(

let n_args = (FStar_List.length args)
in (

let uu____3661 = (

let uu____3662 = (FStar_Syntax_Util.un_uinst head1)
in uu____3662.FStar_Syntax_Syntax.n)
in (match (uu____3661) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (is_known_type_constructor l fv1 n_args) -> begin
(

let arg_embeddings = (FStar_All.pipe_right args (FStar_List.map (fun uu____3692 -> (match (uu____3692) with
| (t4, uu____3700) -> begin
(mk_embedding l env t4)
end))))
in (

let nm = fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (

let uu____3707 = (

let uu____3720 = (FStar_Util.find_opt (fun uu____3752 -> (match (uu____3752) with
| ((x, uu____3767, uu____3768), uu____3769) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv1 x)
end)) (known_type_constructors l))
in (FStar_All.pipe_right uu____3720 FStar_Util.must))
in (match (uu____3707) with
| ((uu____3820, t_arity, _trepr_head), loc_embedding) -> begin
(

let head2 = (mk_basic_embedding loc_embedding nm)
in (match (t_arity) with
| _0_4 when (_0_4 = (Prims.parse_int "0")) -> begin
head2
end
| n1 -> begin
(FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((head2), (arg_embeddings)))))
end))
end))))
end
| uu____3841 -> begin
(

let uu____3842 = (

let uu____3843 = (

let uu____3845 = (FStar_Syntax_Print.term_to_string t3)
in (Prims.strcat "Embedding not defined for type " uu____3845))
in NoTacticEmbedding (uu____3843))
in (FStar_Exn.raise uu____3842))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____3848) -> begin
(

let uu____3855 = (FStar_Syntax_Util.head_and_args t3)
in (match (uu____3855) with
| (head1, args) -> begin
(

let n_args = (FStar_List.length args)
in (

let uu____3907 = (

let uu____3908 = (FStar_Syntax_Util.un_uinst head1)
in uu____3908.FStar_Syntax_Syntax.n)
in (match (uu____3907) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (is_known_type_constructor l fv1 n_args) -> begin
(

let arg_embeddings = (FStar_All.pipe_right args (FStar_List.map (fun uu____3938 -> (match (uu____3938) with
| (t4, uu____3946) -> begin
(mk_embedding l env t4)
end))))
in (

let nm = fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (

let uu____3953 = (

let uu____3966 = (FStar_Util.find_opt (fun uu____3998 -> (match (uu____3998) with
| ((x, uu____4013, uu____4014), uu____4015) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv1 x)
end)) (known_type_constructors l))
in (FStar_All.pipe_right uu____3966 FStar_Util.must))
in (match (uu____3953) with
| ((uu____4066, t_arity, _trepr_head), loc_embedding) -> begin
(

let head2 = (mk_basic_embedding loc_embedding nm)
in (match (t_arity) with
| _0_5 when (_0_5 = (Prims.parse_int "0")) -> begin
head2
end
| n1 -> begin
(FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((head2), (arg_embeddings)))))
end))
end))))
end
| uu____4087 -> begin
(

let uu____4088 = (

let uu____4089 = (

let uu____4091 = (FStar_Syntax_Print.term_to_string t3)
in (Prims.strcat "Embedding not defined for type " uu____4091))
in NoTacticEmbedding (uu____4089))
in (FStar_Exn.raise uu____4088))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app (uu____4094) -> begin
(

let uu____4111 = (FStar_Syntax_Util.head_and_args t3)
in (match (uu____4111) with
| (head1, args) -> begin
(

let n_args = (FStar_List.length args)
in (

let uu____4163 = (

let uu____4164 = (FStar_Syntax_Util.un_uinst head1)
in uu____4164.FStar_Syntax_Syntax.n)
in (match (uu____4163) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (is_known_type_constructor l fv1 n_args) -> begin
(

let arg_embeddings = (FStar_All.pipe_right args (FStar_List.map (fun uu____4194 -> (match (uu____4194) with
| (t4, uu____4202) -> begin
(mk_embedding l env t4)
end))))
in (

let nm = fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (

let uu____4209 = (

let uu____4222 = (FStar_Util.find_opt (fun uu____4254 -> (match (uu____4254) with
| ((x, uu____4269, uu____4270), uu____4271) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv1 x)
end)) (known_type_constructors l))
in (FStar_All.pipe_right uu____4222 FStar_Util.must))
in (match (uu____4209) with
| ((uu____4322, t_arity, _trepr_head), loc_embedding) -> begin
(

let head2 = (mk_basic_embedding loc_embedding nm)
in (match (t_arity) with
| _0_6 when (_0_6 = (Prims.parse_int "0")) -> begin
head2
end
| n1 -> begin
(FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((head2), (arg_embeddings)))))
end))
end))))
end
| uu____4343 -> begin
(

let uu____4344 = (

let uu____4345 = (

let uu____4347 = (FStar_Syntax_Print.term_to_string t3)
in (Prims.strcat "Embedding not defined for type " uu____4347))
in NoTacticEmbedding (uu____4345))
in (FStar_Exn.raise uu____4344))
end)))
end))
end
| uu____4350 -> begin
(

let uu____4351 = (

let uu____4352 = (

let uu____4354 = (FStar_Syntax_Print.term_to_string t3)
in (Prims.strcat "Embedding not defined for type " uu____4354))
in NoTacticEmbedding (uu____4352))
in (FStar_Exn.raise uu____4351))
end))))
in (

let abstract_tvars = (fun tvar_names body -> (match (tvar_names) with
| [] -> begin
(

let body1 = (

let uu____4376 = (

let uu____4377 = (

let uu____4384 = (str_to_name "FStar_Syntax_Embeddings.debug_wrap")
in (

let uu____4386 = (

let uu____4389 = (

let uu____4390 = (

let uu____4391 = (

let uu____4392 = (FStar_Ident.string_of_lid fv_lid1)
in FStar_Extraction_ML_Syntax.MLC_String (uu____4392))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____4391))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____4390))
in (

let uu____4394 = (

let uu____4397 = (

let uu____4398 = (

let uu____4399 = (

let uu____4400 = (

let uu____4407 = (

let uu____4410 = (str_to_name "args")
in (uu____4410)::[])
in ((body), (uu____4407)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4400))
in (FStar_All.pipe_left w uu____4399))
in (mk_lam "_" uu____4398))
in (uu____4397)::[])
in (uu____4389)::uu____4394))
in ((uu____4384), (uu____4386))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4377))
in (FStar_All.pipe_left w uu____4376))
in (mk_lam "args" body1))
end
| uu____4418 -> begin
(

let args_tail = FStar_Extraction_ML_Syntax.MLP_Var ("args_tail")
in (

let mk_cons = (fun hd_pat tail_pat -> FStar_Extraction_ML_Syntax.MLP_CTor (((((("Prims")::[]), ("Cons"))), ((hd_pat)::(tail_pat)::[]))))
in (

let fst_pat = (fun v1 -> FStar_Extraction_ML_Syntax.MLP_Tuple ((FStar_Extraction_ML_Syntax.MLP_Var (v1))::(FStar_Extraction_ML_Syntax.MLP_Wild)::[]))
in (

let pattern = (FStar_List.fold_right (fun hd_var -> (mk_cons (fst_pat hd_var))) tvar_names args_tail)
in (

let branch1 = (

let uu____4467 = (

let uu____4468 = (

let uu____4469 = (

let uu____4476 = (

let uu____4479 = (str_to_name "args")
in (uu____4479)::[])
in ((body), (uu____4476)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4469))
in (FStar_All.pipe_left w uu____4468))
in ((pattern), (FStar_Pervasives_Native.None), (uu____4467)))
in (

let default_branch = (

let uu____4494 = (

let uu____4495 = (

let uu____4496 = (

let uu____4503 = (str_to_name "failwith")
in (

let uu____4505 = (

let uu____4508 = (

let uu____4509 = (mlexpr_of_const FStar_Range.dummyRange (FStar_Const.Const_string ((("arity mismatch"), (FStar_Range.dummyRange)))))
in (FStar_All.pipe_left w uu____4509))
in (uu____4508)::[])
in ((uu____4503), (uu____4505))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4496))
in (FStar_All.pipe_left w uu____4495))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____4494)))
in (

let body1 = (

let uu____4517 = (

let uu____4518 = (

let uu____4533 = (str_to_name "args")
in ((uu____4533), ((branch1)::(default_branch)::[])))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____4518))
in (FStar_All.pipe_left w uu____4517))
in (

let body2 = (

let uu____4570 = (

let uu____4571 = (

let uu____4578 = (str_to_name "FStar_Syntax_Embeddings.debug_wrap")
in (

let uu____4580 = (

let uu____4583 = (

let uu____4584 = (

let uu____4585 = (

let uu____4586 = (FStar_Ident.string_of_lid fv_lid1)
in FStar_Extraction_ML_Syntax.MLC_String (uu____4586))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____4585))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____4584))
in (

let uu____4588 = (

let uu____4591 = (mk_lam "_" body1)
in (uu____4591)::[])
in (uu____4583)::uu____4588))
in ((uu____4578), (uu____4580))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____4571))
in (FStar_All.pipe_left w uu____4570))
in (mk_lam "args" body2)))))))))
end))
in (

let uu____4596 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____4596) with
| (bs, c) -> begin
(

let uu____4629 = (match (arity_opt) with
| FStar_Pervasives_Native.None -> begin
((bs), (c))
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let n_bs = (FStar_List.length bs)
in (match ((Prims.op_Equality n1 n_bs)) with
| true -> begin
((bs), (c))
end
| uu____4709 -> begin
(match ((n1 < n_bs)) with
| true -> begin
(

let uu____4730 = (FStar_Util.first_N n1 bs)
in (match (uu____4730) with
| (bs1, rest) -> begin
(

let c1 = (

let uu____4808 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____4808))
in ((bs1), (c1)))
end))
end
| uu____4821 -> begin
(

let msg = (

let uu____4825 = (FStar_Ident.string_of_lid fv_lid1)
in (

let uu____4827 = (FStar_Util.string_of_int n1)
in (

let uu____4829 = (FStar_Util.string_of_int n_bs)
in (FStar_Util.format3 "Embedding not defined for %s; expected arity at least %s; got %s" uu____4825 uu____4827 uu____4829))))
in (FStar_Exn.raise (NoTacticEmbedding (msg))))
end)
end))
end)
in (match (uu____4629) with
| (bs1, c1) -> begin
(

let result_typ = (FStar_Syntax_Util.comp_result c1)
in (

let arity = (FStar_List.length bs1)
in (

let uu____4886 = (

let uu____4907 = (FStar_Util.prefix_until (fun uu____4949 -> (match (uu____4949) with
| (b, uu____4958) -> begin
(

let uu____4963 = (

let uu____4964 = (FStar_Syntax_Subst.compress b.FStar_Syntax_Syntax.sort)
in uu____4964.FStar_Syntax_Syntax.n)
in (match (uu____4963) with
| FStar_Syntax_Syntax.Tm_type (uu____4968) -> begin
false
end
| uu____4970 -> begin
true
end))
end)) bs1)
in (match (uu____4907) with
| FStar_Pervasives_Native.None -> begin
((bs1), ([]))
end
| FStar_Pervasives_Native.Some (tvars, x, rest) -> begin
((tvars), ((x)::rest))
end))
in (match (uu____4886) with
| (type_vars, bs2) -> begin
(

let tvar_arity = (FStar_List.length type_vars)
in (

let non_tvar_arity = (FStar_List.length bs2)
in (

let tvar_names = (FStar_List.mapi (fun i tv -> (

let uu____5212 = (FStar_Util.string_of_int i)
in (Prims.strcat "tv_" uu____5212))) type_vars)
in (

let tvar_context = (FStar_List.map2 (fun b nm -> (((FStar_Pervasives_Native.fst b)), (nm))) type_vars tvar_names)
in (

let rec aux = (fun loc accum_embeddings bs3 -> (match (bs3) with
| [] -> begin
(

let arg_unembeddings = (FStar_List.rev accum_embeddings)
in (

let res_embedding = (mk_embedding loc tvar_context result_typ)
in (

let fv_lid2 = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5312 = (FStar_Syntax_Util.is_pure_comp c1)
in (match (uu____5312) with
| true -> begin
(

let cb = (str_to_name "cb")
in (

let embed_fun_N = (mk_arrow_as_prim_step loc non_tvar_arity)
in (

let args = (

let uu____5333 = (

let uu____5336 = (

let uu____5339 = (lid_to_top_name fv_lid2)
in (

let uu____5340 = (

let uu____5343 = (

let uu____5344 = (

let uu____5345 = (

let uu____5346 = (

let uu____5358 = (FStar_Util.string_of_int tvar_arity)
in ((uu____5358), (FStar_Pervasives_Native.None)))
in FStar_Extraction_ML_Syntax.MLC_Int (uu____5346))
in FStar_Extraction_ML_Syntax.MLE_Const (uu____5345))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____5344))
in (uu____5343)::(fv_lid_embedded)::(cb)::[])
in (uu____5339)::uu____5340))
in (res_embedding)::uu____5336)
in (FStar_List.append arg_unembeddings uu____5333))
in (

let fun_embedding = (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((embed_fun_N), (args)))))
in (

let tabs = (abstract_tvars tvar_names fun_embedding)
in (

let cb_tabs = (mk_lam "cb" tabs)
in (

let uu____5383 = (match ((Prims.op_Equality loc NBE_t)) with
| true -> begin
cb_tabs
end
| uu____5385 -> begin
(mk_lam "_psc" cb_tabs)
end)
in ((uu____5383), (arity), (true)))))))))
end
| uu____5395 -> begin
(

let uu____5397 = (

let uu____5399 = (FStar_TypeChecker_Env.norm_eff_name tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (FStar_Ident.lid_equals uu____5399 FStar_Parser_Const.effect_TAC_lid))
in (match (uu____5397) with
| true -> begin
(

let h = (

let uu____5410 = (

let uu____5412 = (FStar_Util.string_of_int non_tvar_arity)
in (Prims.strcat (mk_tactic_interpretation loc) uu____5412))
in (str_to_top_name uu____5410))
in (

let tac_fun = (

let uu____5421 = (

let uu____5422 = (

let uu____5429 = (

let uu____5430 = (

let uu____5432 = (FStar_Util.string_of_int non_tvar_arity)
in (Prims.strcat (mk_from_tactic loc) uu____5432))
in (str_to_top_name uu____5430))
in (

let uu____5440 = (

let uu____5443 = (lid_to_top_name fv_lid2)
in (uu____5443)::[])
in ((uu____5429), (uu____5440))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____5422))
in (FStar_All.pipe_left w uu____5421))
in (

let psc = (str_to_name "psc")
in (

let ncb = (str_to_name "ncb")
in (

let all_args = (str_to_name "args")
in (

let args = (FStar_List.append ((tac_fun)::[]) (FStar_List.append arg_unembeddings ((res_embedding)::(psc)::(ncb)::[])))
in (

let tabs = (match (tvar_names) with
| [] -> begin
(

let uu____5457 = (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((h), ((FStar_List.append args ((all_args)::[])))))))
in (mk_lam "args" uu____5457))
end
| uu____5461 -> begin
(

let uu____5465 = (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((h), (args)))))
in (abstract_tvars tvar_names uu____5465))
end)
in (

let uu____5468 = (

let uu____5469 = (mk_lam "ncb" tabs)
in (mk_lam "psc" uu____5469))
in ((uu____5468), ((arity + (Prims.parse_int "1"))), (false))))))))))
end
| uu____5482 -> begin
(

let uu____5484 = (

let uu____5485 = (

let uu____5487 = (FStar_Syntax_Print.term_to_string t1)
in (Prims.strcat "Plugins not defined for type " uu____5487))
in NoTacticEmbedding (uu____5485))
in (FStar_Exn.raise uu____5484))
end))
end)))))
end
| ((b, uu____5499))::bs4 -> begin
(

let uu____5519 = (

let uu____5522 = (mk_embedding loc tvar_context b.FStar_Syntax_Syntax.sort)
in (uu____5522)::accum_embeddings)
in (aux loc uu____5519 bs4))
end))
in (FStar_All.try_with (fun uu___284_5544 -> (match (()) with
| () -> begin
(

let uu____5557 = (aux Syntax_term [] bs2)
in (match (uu____5557) with
| (w1, a, b) -> begin
(

let uu____5585 = (aux NBE_t [] bs2)
in (match (uu____5585) with
| (w', uu____5607, uu____5608) -> begin
FStar_Pervasives_Native.Some (((w1), (w'), (a), (b)))
end))
end))
end)) (fun uu___283_5628 -> (match (uu___283_5628) with
| NoTacticEmbedding (msg) -> begin
((

let uu____5644 = (FStar_Syntax_Print.fv_to_string fv)
in (not_implemented_warning t1.FStar_Syntax_Syntax.pos uu____5644 msg));
FStar_Pervasives_Native.None;
)
end))))))))
end))))
end))
end))))))))))))))))))))))))))))





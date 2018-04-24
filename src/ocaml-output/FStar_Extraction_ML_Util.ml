
open Prims
open FStar_Pervasives

let codegen_fsharp : unit  ->  Prims.bool = (fun uu____5 -> (

let uu____6 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____6 (FStar_Pervasives_Native.Some (FStar_Options.FSharp)))))


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
| FStar_Const.Const_range (uu____56) -> begin
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
| FStar_Const.Const_bytearray (bytes, uu____81) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (s, uu____87) -> begin
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
| FStar_Const.Const_reflect (uu____88) -> begin
(failwith "Unhandled constant: reify/reflect")
end))


let mlconst_of_const : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> (FStar_All.try_with (fun uu___69_100 -> (match (()) with
| () -> begin
(mlconst_of_const' c)
end)) (fun uu___68_104 -> (match (uu___68_104) with
| uu____105 -> begin
(

let uu____106 = (

let uu____107 = (FStar_Range.string_of_range p)
in (

let uu____108 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " uu____107 uu____108)))
in (failwith uu____106))
end))))


let mlexpr_of_range : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun r -> (

let cint = (fun i -> (

let uu____120 = (

let uu____121 = (

let uu____122 = (

let uu____133 = (FStar_Util.string_of_int i)
in ((uu____133), (FStar_Pervasives_Native.None)))
in FStar_Extraction_ML_Syntax.MLC_Int (uu____122))
in (FStar_All.pipe_right uu____121 (fun _0_18 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_18))))
in (FStar_All.pipe_right uu____120 (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty))))
in (

let cstr = (fun s -> (

let uu____150 = (FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String (s)) (fun _0_19 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_19)))
in (FStar_All.pipe_right uu____150 (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty))))
in (

let uu____151 = (

let uu____158 = (

let uu____161 = (

let uu____162 = (FStar_Range.file_of_range r)
in (FStar_All.pipe_right uu____162 cstr))
in (

let uu____163 = (

let uu____166 = (

let uu____167 = (

let uu____168 = (FStar_Range.start_of_range r)
in (FStar_All.pipe_right uu____168 FStar_Range.line_of_pos))
in (FStar_All.pipe_right uu____167 cint))
in (

let uu____169 = (

let uu____172 = (

let uu____173 = (

let uu____174 = (FStar_Range.start_of_range r)
in (FStar_All.pipe_right uu____174 FStar_Range.col_of_pos))
in (FStar_All.pipe_right uu____173 cint))
in (

let uu____175 = (

let uu____178 = (

let uu____179 = (

let uu____180 = (FStar_Range.end_of_range r)
in (FStar_All.pipe_right uu____180 FStar_Range.line_of_pos))
in (FStar_All.pipe_right uu____179 cint))
in (

let uu____181 = (

let uu____184 = (

let uu____185 = (

let uu____186 = (FStar_Range.end_of_range r)
in (FStar_All.pipe_right uu____186 FStar_Range.col_of_pos))
in (FStar_All.pipe_right uu____185 cint))
in (uu____184)::[])
in (uu____178)::uu____181))
in (uu____172)::uu____175))
in (uu____166)::uu____169))
in (uu____161)::uu____163))
in ((mk_range_mle), (uu____158)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____151)))))


let mlexpr_of_const : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun p c -> (match (c) with
| FStar_Const.Const_range (r) -> begin
(mlexpr_of_range r)
end
| uu____200 -> begin
(

let uu____201 = (mlconst_of_const p c)
in FStar_Extraction_ML_Syntax.MLE_Const (uu____201))
end))


let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst1 t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let uu____225 = (FStar_Util.find_opt (fun uu____239 -> (match (uu____239) with
| (y, uu____245) -> begin
(Prims.op_Equality y x)
end)) subst1)
in (match (uu____225) with
| FStar_Pervasives_Native.Some (ts) -> begin
(FStar_Pervasives_Native.snd ts)
end
| FStar_Pervasives_Native.None -> begin
t
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____262 = (

let uu____269 = (subst_aux subst1 t1)
in (

let uu____270 = (subst_aux subst1 t2)
in ((uu____269), (f), (uu____270))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____262))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(

let uu____277 = (

let uu____284 = (FStar_List.map (subst_aux subst1) args)
in ((uu____284), (path)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____277))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____292 = (FStar_List.map (subst_aux subst1) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____292))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
t
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
t
end))


let try_subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option = (fun uu____307 args -> (match (uu____307) with
| (formals, t) -> begin
(match ((Prims.op_disEquality (FStar_List.length formals) (FStar_List.length args))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____317 -> begin
(

let uu____318 = (

let uu____319 = (FStar_List.zip formals args)
in (subst_aux uu____319 t))
in FStar_Pervasives_Native.Some (uu____318))
end)
end))


let subst : (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty)  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun ts args -> (

let uu____348 = (try_subst ts args)
in (match (uu____348) with
| FStar_Pervasives_Native.None -> begin
(failwith "Substitution must be fully applied (see GitHub issue #490)")
end
| FStar_Pervasives_Native.Some (t) -> begin
t
end)))


let udelta_unfold : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option = (fun g uu___64_363 -> (match (uu___64_363) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n1) -> begin
(

let uu____372 = (FStar_Extraction_ML_UEnv.lookup_ty_const g n1)
in (match (uu____372) with
| FStar_Pervasives_Native.Some (ts) -> begin
(

let uu____378 = (try_subst ts args)
in (match (uu____378) with
| FStar_Pervasives_Native.None -> begin
(

let uu____383 = (

let uu____384 = (FStar_Extraction_ML_Syntax.string_of_mlpath n1)
in (

let uu____385 = (FStar_Util.string_of_int (FStar_List.length args))
in (

let uu____386 = (FStar_Util.string_of_int (FStar_List.length (FStar_Pervasives_Native.fst ts)))
in (FStar_Util.format3 "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)" uu____384 uu____385 uu____386))))
in (failwith uu____383))
end
| FStar_Pervasives_Native.Some (r) -> begin
FStar_Pervasives_Native.Some (r)
end))
end
| uu____390 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____393 -> begin
FStar_Pervasives_Native.None
end))


let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_PURE, uu____404) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| uu____405 -> begin
false
end))


let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun uu___65_414 -> (match (uu___65_414) with
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
| uu____430 -> begin
(

let uu____435 = (

let uu____436 = (FStar_Range.string_of_range r)
in (

let uu____437 = (eff_to_string f)
in (

let uu____438 = (eff_to_string f')
in (FStar_Util.format3 "Impossible (%s): Inconsistent effects %s and %s" uu____436 uu____437 uu____438))))
in (failwith uu____435))
end))


let join_l : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r fs -> (FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs))


let mk_ty_fun : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (FStar_List.fold_right (fun uu____475 t -> (match (uu____475) with
| (uu____481, t0) -> begin
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
| uu____554 -> begin
((false), (FStar_Pervasives_Native.None))
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(

let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| uu____590 -> begin
(

let e1 = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body1) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((FStar_List.append xs ys)), (body1)))
end
| uu____622 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((xs), (body)))
end)
in (

let uu____629 = (mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____629 e1)))
end))
in (match (e) with
| FStar_Pervasives_Native.Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((x)::xs, body); FStar_Extraction_ML_Syntax.mlty = uu____639; FStar_Extraction_ML_Syntax.loc = uu____640}) -> begin
(

let uu____661 = ((type_leq unfold_ty t1' t1) && (eff_leq f f'))
in (match (uu____661) with
| true -> begin
(match (((Prims.op_Equality f FStar_Extraction_ML_Syntax.E_PURE) && (Prims.op_Equality f' FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
(

let uu____677 = (type_leq unfold_ty t2 t2')
in (match (uu____677) with
| true -> begin
(

let body1 = (

let uu____688 = (type_leq unfold_ty t2 FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____688) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____692 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t2')))))
end))
in (

let uu____693 = (

let uu____696 = (

let uu____697 = (

let uu____702 = (mk_ty_fun ((x)::[]) body1.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____702))
in (FStar_All.pipe_left uu____697 (FStar_Extraction_ML_Syntax.MLE_Fun ((((x)::[]), (body1))))))
in FStar_Pervasives_Native.Some (uu____696))
in ((true), (uu____693))))
end
| uu____727 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____730 -> begin
(

let uu____731 = (

let uu____738 = (

let uu____741 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) uu____741))
in (type_leq_c unfold_ty uu____738 t2 t2'))
in (match (uu____731) with
| (ok, body1) -> begin
(

let res = (match (body1) with
| FStar_Pervasives_Native.Some (body2) -> begin
(

let uu____765 = (mk_fun ((x)::[]) body2)
in FStar_Pervasives_Native.Some (uu____765))
end
| uu____774 -> begin
FStar_Pervasives_Native.None
end)
in ((ok), (res)))
end))
end)
end
| uu____779 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____782 -> begin
(

let uu____785 = (((type_leq unfold_ty t1' t1) && (eff_leq f f')) && (type_leq unfold_ty t2 t2'))
in (match (uu____785) with
| true -> begin
((true), (e))
end
| uu____800 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
(match ((Prims.op_Equality path path')) with
| true -> begin
(

let uu____821 = (FStar_List.forall2 (type_leq unfold_ty) args args')
in (match (uu____821) with
| true -> begin
((true), (e))
end
| uu____833 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____836 -> begin
(

let uu____837 = (unfold_ty t)
in (match (uu____837) with
| FStar_Pervasives_Native.Some (t1) -> begin
(type_leq_c unfold_ty e t1 t')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____851 = (unfold_ty t')
in (match (uu____851) with
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

let uu____873 = (FStar_List.forall2 (type_leq unfold_ty) ts ts')
in (match (uu____873) with
| true -> begin
((true), (e))
end
| uu____885 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((true), (e))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (uu____890), uu____891) -> begin
(

let uu____898 = (unfold_ty t)
in (match (uu____898) with
| FStar_Pervasives_Native.Some (t1) -> begin
(type_leq_c unfold_ty e t1 t')
end
| uu____912 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (uu____917, FStar_Extraction_ML_Syntax.MLTY_Named (uu____918)) -> begin
(

let uu____925 = (unfold_ty t')
in (match (uu____925) with
| FStar_Pervasives_Native.Some (t'1) -> begin
(type_leq_c unfold_ty e t t'1)
end
| uu____939 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Erased, FStar_Extraction_ML_Syntax.MLTY_Erased) -> begin
((true), (e))
end
| uu____946 -> begin
((false), (FStar_Pervasives_Native.None))
end))
and type_leq : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (

let uu____958 = (type_leq_c g FStar_Pervasives_Native.None t1 t2)
in (FStar_All.pipe_right uu____958 FStar_Pervasives_Native.fst)))


let is_type_abstraction : 'a 'b 'c . (('a, 'b) FStar_Util.either * 'c) Prims.list  ->  Prims.bool = (fun uu___66_1001 -> (match (uu___66_1001) with
| ((FStar_Util.Inl (uu____1012), uu____1013))::uu____1014 -> begin
true
end
| uu____1037 -> begin
false
end))


let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int FStar_Pervasives_Native.option = (fun uu____1060 -> (match (uu____1060) with
| (ns, n1) -> begin
(

let uu____1075 = (

let uu____1076 = (FStar_Util.concat_l "." (FStar_List.append ns ((n1)::[])))
in (FStar_Parser_Const.is_tuple_datacon_string uu____1076))
in (match (uu____1075) with
| true -> begin
(

let uu____1079 = (

let uu____1080 = (FStar_Util.char_at n1 (Prims.parse_int "7"))
in (FStar_Util.int_of_char uu____1080))
in FStar_Pervasives_Native.Some (uu____1079))
end
| uu____1081 -> begin
FStar_Pervasives_Native.None
end))
end))


let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(

let uu____1093 = (is_xtuple mlp)
in (match (uu____1093) with
| FStar_Pervasives_Native.Some (n1) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| uu____1097 -> begin
e
end))
end
| uu____1100 -> begin
e
end))


let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun uu___67_1109 -> (match (uu___67_1109) with
| (f)::uu____1115 -> begin
(

let uu____1118 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (uu____1118) with
| (ns, uu____1128) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id1 -> id1.FStar_Ident.idText)))
end))
end
| uu____1139 -> begin
(failwith "impos")
end))


let record_fields : 'a . FStar_Ident.lident Prims.list  ->  'a Prims.list  ->  (Prims.string * 'a) Prims.list = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.ident.FStar_Ident.idText), (e))) fs vs))


let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int FStar_Pervasives_Native.option = (fun uu____1195 -> (match (uu____1195) with
| (ns, n1) -> begin
(

let uu____1210 = (

let uu____1211 = (FStar_Util.concat_l "." (FStar_List.append ns ((n1)::[])))
in (FStar_Parser_Const.is_tuple_constructor_string uu____1211))
in (match (uu____1210) with
| true -> begin
(

let uu____1214 = (

let uu____1215 = (FStar_Util.char_at n1 (Prims.parse_int "5"))
in (FStar_Util.int_of_char uu____1215))
in FStar_Pervasives_Native.Some (uu____1214))
end
| uu____1216 -> begin
FStar_Pervasives_Native.None
end))
end))


let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(

let uu____1228 = (is_xtuple_ty mlp)
in (match (uu____1228) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| uu____1232 -> begin
t
end))
end
| uu____1235 -> begin
t
end))


let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> (

let uu____1245 = (codegen_fsharp ())
in (match (uu____1245) with
| true -> begin
(FStar_String.concat "." ns)
end
| uu____1246 -> begin
(FStar_String.concat "_" ns)
end)))


let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun uu____1257 -> (match (uu____1257) with
| (ns, n1) -> begin
(

let uu____1270 = (codegen_fsharp ())
in (match (uu____1270) with
| true -> begin
(FStar_String.concat "." (FStar_List.append ns ((n1)::[])))
end
| uu____1271 -> begin
(FStar_String.concat "_" (FStar_List.append ns ((n1)::[])))
end))
end))


let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (

let uu____1283 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in ((uu____1283), (l.FStar_Ident.ident.FStar_Ident.idText))))


let rec erasableType : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun unfold_ty t -> (

let uu____1309 = (FStar_Extraction_ML_UEnv.erasableTypeNoDelta t)
in (match (uu____1309) with
| true -> begin
true
end
| uu____1310 -> begin
(

let uu____1311 = (unfold_ty t)
in (match (uu____1311) with
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

let uu____1337 = (

let uu____1344 = (eraseTypeDeep unfold_ty tyd)
in (

let uu____1348 = (eraseTypeDeep unfold_ty tycd)
in ((uu____1344), (etag), (uu____1348))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____1337))
end
| uu____1352 -> begin
t
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
(

let uu____1359 = (erasableType unfold_ty t)
in (match (uu____1359) with
| true -> begin
FStar_Extraction_ML_UEnv.erasedContent
end
| uu____1363 -> begin
(

let uu____1364 = (

let uu____1371 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in ((uu____1371), (mlp)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____1364))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(

let uu____1382 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____1382))
end
| uu____1388 -> begin
t
end))


let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_Equality")))))


let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (

let uu____1391 = (

let uu____1396 = (mk_ty_fun (((("x"), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::((("y"), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty uu____1396))
in (FStar_All.pipe_left uu____1391 (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_AmpAmp"))))))


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

let uu____1469 = (conjoin x y)
in FStar_Pervasives_Native.Some (uu____1469))
end))


let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (

let pos = (FStar_Range.start_of_range r)
in (

let line = (FStar_Range.line_of_pos pos)
in (

let uu____1481 = (FStar_Range.file_of_range r)
in ((line), (uu____1481))))))


let rec doms_and_cod : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1500, b) -> begin
(

let uu____1502 = (doms_and_cod b)
in (match (uu____1502) with
| (ds, c) -> begin
(((a)::ds), (c))
end))
end
| uu____1523 -> begin
(([]), (t))
end))


let argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (

let uu____1535 = (doms_and_cod t)
in (FStar_Pervasives_Native.fst uu____1535)))


let rec uncurry_mlty_fun : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1562, b) -> begin
(

let uu____1564 = (uncurry_mlty_fun b)
in (match (uu____1564) with
| (args, res) -> begin
(((a)::args), (res))
end))
end
| uu____1585 -> begin
(([]), (t))
end))

exception NoTacticEmbedding of (Prims.string)


let uu___is_NoTacticEmbedding : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoTacticEmbedding (uu____1597) -> begin
true
end
| uu____1598 -> begin
false
end))


let __proj__NoTacticEmbedding__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| NoTacticEmbedding (uu____1605) -> begin
uu____1605
end))


let not_implemented_warning : FStar_Range.range  ->  Prims.string  ->  Prims.string  ->  unit = (fun r t msg -> (

let uu____1621 = (

let uu____1626 = (FStar_Util.format2 "Plugin %s will not run natively because %s.\n" t msg)
in ((FStar_Errors.Warning_CallNotImplementedAsWarning), (uu____1626)))
in (FStar_Errors.log_issue r uu____1621)))

type emb_loc =
| S
| R


let uu___is_S : emb_loc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| S -> begin
true
end
| uu____1632 -> begin
false
end))


let uu___is_R : emb_loc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| R -> begin
true
end
| uu____1638 -> begin
false
end))


let interpret_plugin_as_term_fun : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mlexpr'  ->  (FStar_Extraction_ML_Syntax.mlexpr * Prims.int * Prims.bool) FStar_Pervasives_Native.option = (fun tcenv fv t ml_fv -> (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) tcenv t)
in (

let w = (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
in (

let lid_to_name = (fun l -> (

let uu____1679 = (

let uu____1680 = (FStar_Extraction_ML_Syntax.mlpath_of_lident l)
in FStar_Extraction_ML_Syntax.MLE_Name (uu____1680))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1679)))
in (

let lid_to_top_name = (fun l -> (

let uu____1687 = (

let uu____1688 = (FStar_Extraction_ML_Syntax.mlpath_of_lident l)
in FStar_Extraction_ML_Syntax.MLE_Name (uu____1688))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1687)))
in (

let str_to_name = (fun s -> (

let uu____1695 = (FStar_Ident.lid_of_str s)
in (lid_to_name uu____1695)))
in (

let str_to_top_name = (fun s -> (

let uu____1702 = (FStar_Ident.lid_of_str s)
in (lid_to_top_name uu____1702)))
in (

let fstar_syn_emb_prefix = (fun s -> (str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)))
in (

let fstar_refl_emb_prefix = (fun s -> (str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s)))
in (

let mk_basic_embedding = (fun l s -> (

let emb_prefix = (match (l) with
| S -> begin
fstar_syn_emb_prefix
end
| R -> begin
fstar_refl_emb_prefix
end)
in (emb_prefix (Prims.strcat "e_" s))))
in (

let mk_arrow_embedding = (fun arity -> (

let uu____1740 = (

let uu____1741 = (FStar_Util.string_of_int arity)
in (Prims.strcat "embed_arrow_" uu____1741))
in (fstar_syn_emb_prefix uu____1740)))
in (

let mk_any_embedding = (fun s -> (

let uu____1748 = (

let uu____1749 = (

let uu____1756 = (fstar_syn_emb_prefix "mk_any_emb")
in (

let uu____1757 = (

let uu____1760 = (str_to_name s)
in (uu____1760)::[])
in ((uu____1756), (uu____1757))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1749))
in (FStar_All.pipe_left w uu____1748)))
in (

let mk_lam = (fun nm e -> (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_Fun ((((((nm), (FStar_Extraction_ML_Syntax.MLTY_Top)))::[]), (e))))))
in (

let known_type_constructors = (

let uu____1799 = (

let uu____1810 = (

let uu____1821 = (

let uu____1832 = (

let uu____1843 = (

let uu____1852 = (FStar_Reflection_Data.fstar_refl_types_lid "term")
in ((uu____1852), ((Prims.parse_int "0")), ("term"), (R)))
in (

let uu____1853 = (

let uu____1864 = (

let uu____1873 = (FStar_Reflection_Data.fstar_refl_types_lid "fv")
in ((uu____1873), ((Prims.parse_int "0")), ("fv"), (R)))
in (

let uu____1874 = (

let uu____1885 = (

let uu____1894 = (FStar_Reflection_Data.fstar_refl_types_lid "binder")
in ((uu____1894), ((Prims.parse_int "0")), ("binder"), (R)))
in (

let uu____1895 = (

let uu____1906 = (

let uu____1915 = (FStar_Reflection_Data.fstar_refl_syntax_lid "binders")
in ((uu____1915), ((Prims.parse_int "0")), ("binders"), (R)))
in (

let uu____1916 = (

let uu____1927 = (

let uu____1938 = (

let uu____1949 = (

let uu____1960 = (

let uu____1969 = (FStar_Parser_Const.mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange)
in ((uu____1969), ((Prims.parse_int "2")), ("tuple2"), (S)))
in (

let uu____1970 = (

let uu____1981 = (

let uu____1990 = (FStar_Reflection_Data.fstar_refl_data_lid "exp")
in ((uu____1990), ((Prims.parse_int "0")), ("exp"), (R)))
in (uu____1981)::[])
in (uu____1960)::uu____1970))
in (((FStar_Parser_Const.option_lid), ((Prims.parse_int "1")), ("option"), (S)))::uu____1949)
in (((FStar_Parser_Const.list_lid), ((Prims.parse_int "1")), ("list"), (S)))::uu____1938)
in (((FStar_Parser_Const.norm_step_lid), ((Prims.parse_int "0")), ("norm_step"), (S)))::uu____1927)
in (uu____1906)::uu____1916))
in (uu____1885)::uu____1895))
in (uu____1864)::uu____1874))
in (uu____1843)::uu____1853))
in (((FStar_Parser_Const.string_lid), ((Prims.parse_int "0")), ("string"), (S)))::uu____1832)
in (((FStar_Parser_Const.unit_lid), ((Prims.parse_int "0")), ("unit"), (S)))::uu____1821)
in (((FStar_Parser_Const.bool_lid), ((Prims.parse_int "0")), ("bool"), (S)))::uu____1810)
in (((FStar_Parser_Const.int_lid), ((Prims.parse_int "0")), ("int"), (S)))::uu____1799)
in (

let is_known_type_constructor = (fun fv1 n1 -> (FStar_Util.for_some (fun uu____2127 -> (match (uu____2127) with
| (x, args, uu____2138, uu____2139) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (Prims.op_Equality n1 args))
end)) known_type_constructors))
in (

let find_env_entry = (fun bv uu____2154 -> (match (uu____2154) with
| (bv', uu____2160) -> begin
(FStar_Syntax_Syntax.bv_eq bv bv')
end))
in (

let rec mk_embedding = (fun env t2 -> (

let uu____2184 = (

let uu____2185 = (FStar_Syntax_Subst.compress t2)
in uu____2185.FStar_Syntax_Syntax.n)
in (match (uu____2184) with
| FStar_Syntax_Syntax.Tm_name (bv) when (FStar_Util.for_some (find_env_entry bv) env) -> begin
(

let uu____2193 = (

let uu____2194 = (

let uu____2199 = (FStar_Util.find_opt (find_env_entry bv) env)
in (FStar_Util.must uu____2199))
in (FStar_Pervasives_Native.snd uu____2194))
in (FStar_All.pipe_left mk_any_embedding uu____2193))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____2215) -> begin
(mk_embedding env x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t3, uu____2221, uu____2222) -> begin
(mk_embedding env t3)
end
| uu____2263 -> begin
(

let t3 = (FStar_TypeChecker_Normalize.unfold_whnf tcenv t2)
in (

let uu____2265 = (FStar_Syntax_Util.head_and_args t3)
in (match (uu____2265) with
| (head1, args) -> begin
(

let n_args = (FStar_List.length args)
in (

let uu____2309 = (

let uu____2310 = (FStar_Syntax_Util.un_uinst head1)
in uu____2310.FStar_Syntax_Syntax.n)
in (match (uu____2309) with
| FStar_Syntax_Syntax.Tm_refine (b, uu____2314) -> begin
(mk_embedding env b.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_fvar (fv1) when (is_known_type_constructor fv1 n_args) -> begin
(

let arg_embeddings = (FStar_List.map (fun uu____2334 -> (match (uu____2334) with
| (t4, uu____2340) -> begin
(mk_embedding env t4)
end)) args)
in (

let nm = fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (

let uu____2342 = (

let uu____2351 = (FStar_Util.find_opt (fun uu____2375 -> (match (uu____2375) with
| (x, uu____2385, uu____2386, uu____2387) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv1 x)
end)) known_type_constructors)
in (FStar_All.pipe_right uu____2351 FStar_Util.must))
in (match (uu____2342) with
| (uu____2414, t_arity, trepr_head, loc_embedding) -> begin
(

let head2 = (mk_basic_embedding loc_embedding nm)
in (match (t_arity) with
| _0_21 when (_0_21 = (Prims.parse_int "0")) -> begin
head2
end
| n1 -> begin
(FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((head2), (arg_embeddings)))))
end))
end))))
end
| uu____2422 -> begin
(

let uu____2423 = (

let uu____2424 = (

let uu____2425 = (FStar_Syntax_Print.term_to_string t3)
in (Prims.strcat "Embedding not defined for type " uu____2425))
in NoTacticEmbedding (uu____2424))
in (FStar_Exn.raise uu____2423))
end)))
end)))
end)))
in (

let abstract_tvars = (fun tvar_names body -> (match (tvar_names) with
| [] -> begin
body
end
| uu____2441 -> begin
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

let uu____2484 = (

let uu____2485 = (

let uu____2486 = (

let uu____2493 = (

let uu____2496 = (str_to_name "args_tail")
in (uu____2496)::[])
in ((body), (uu____2493)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2486))
in (FStar_All.pipe_left w uu____2485))
in ((pattern), (FStar_Pervasives_Native.None), (uu____2484)))
in (

let default_branch = (

let uu____2510 = (

let uu____2511 = (

let uu____2512 = (

let uu____2519 = (str_to_name "failwith")
in (

let uu____2520 = (

let uu____2523 = (

let uu____2524 = (mlexpr_of_const FStar_Range.dummyRange (FStar_Const.Const_string ((("arity mismatch"), (FStar_Range.dummyRange)))))
in (FStar_All.pipe_left w uu____2524))
in (uu____2523)::[])
in ((uu____2519), (uu____2520))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2512))
in (FStar_All.pipe_left w uu____2511))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (uu____2510)))
in (

let body1 = (

let uu____2530 = (

let uu____2531 = (

let uu____2546 = (str_to_name "args")
in ((uu____2546), ((branch1)::(default_branch)::[])))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____2531))
in (FStar_All.pipe_left w uu____2530))
in (mk_lam "args" body1))))))))
end))
in (

let uu____2581 = (FStar_Syntax_Util.arrow_formals_comp t1)
in (match (uu____2581) with
| (bs, c) -> begin
(

let result_typ = (FStar_Syntax_Util.comp_result c)
in (

let arity = (FStar_List.length bs)
in (

let uu____2622 = (

let uu____2639 = (FStar_Util.prefix_until (fun uu____2673 -> (match (uu____2673) with
| (b, uu____2679) -> begin
(

let uu____2680 = (

let uu____2681 = (FStar_Syntax_Subst.compress b.FStar_Syntax_Syntax.sort)
in uu____2681.FStar_Syntax_Syntax.n)
in (match (uu____2680) with
| FStar_Syntax_Syntax.Tm_type (uu____2684) -> begin
false
end
| uu____2685 -> begin
true
end))
end)) bs)
in (match (uu____2639) with
| FStar_Pervasives_Native.None -> begin
((bs), ([]))
end
| FStar_Pervasives_Native.Some (tvars, x, rest) -> begin
((tvars), ((x)::rest))
end))
in (match (uu____2622) with
| (type_vars, bs1) -> begin
(

let non_tvar_arity = (FStar_List.length bs1)
in (

let tvar_names = (FStar_List.mapi (fun i tv -> (

let uu____2868 = (FStar_Util.string_of_int i)
in (Prims.strcat "tv_" uu____2868))) type_vars)
in (

let tvar_context = (FStar_List.map2 (fun b nm -> (((FStar_Pervasives_Native.fst b)), (nm))) type_vars tvar_names)
in (

let rec aux = (fun accum_embeddings env bs2 -> (match (bs2) with
| [] -> begin
(

let arg_unembeddings = (FStar_List.rev accum_embeddings)
in (

let res_embedding = (mk_embedding env result_typ)
in (

let uu____2960 = (FStar_Syntax_Util.is_pure_comp c)
in (match (uu____2960) with
| true -> begin
(

let embed_fun_N = (mk_arrow_embedding non_tvar_arity)
in (

let args = (

let uu____2979 = (

let uu____2982 = (

let uu____2985 = (lid_to_top_name fv)
in (uu____2985)::[])
in (res_embedding)::uu____2982)
in (FStar_List.append arg_unembeddings uu____2979))
in (

let fun_embedding = (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((embed_fun_N), (args)))))
in (

let tabs = (abstract_tvars tvar_names fun_embedding)
in (

let uu____2990 = (

let uu____2997 = (mk_lam "_psc" tabs)
in ((uu____2997), (arity), (true)))
in FStar_Pervasives_Native.Some (uu____2990))))))
end
| uu____3008 -> begin
(

let uu____3009 = (

let uu____3010 = (FStar_TypeChecker_Env.norm_eff_name tcenv (FStar_Syntax_Util.comp_effect_name c))
in (FStar_Ident.lid_equals uu____3010 FStar_Parser_Const.effect_TAC_lid))
in (match (uu____3009) with
| true -> begin
(

let h = (

let uu____3020 = (

let uu____3021 = (FStar_Util.string_of_int non_tvar_arity)
in (Prims.strcat "FStar_Tactics_Interpreter.mk_tactic_interpretation_" uu____3021))
in (str_to_top_name uu____3020))
in (

let tac_fun = (

let uu____3029 = (

let uu____3030 = (

let uu____3037 = (

let uu____3038 = (

let uu____3039 = (FStar_Util.string_of_int non_tvar_arity)
in (Prims.strcat "FStar_Tactics_Native.from_tactic_" uu____3039))
in (str_to_top_name uu____3038))
in (

let uu____3046 = (

let uu____3049 = (lid_to_top_name fv)
in (uu____3049)::[])
in ((uu____3037), (uu____3046))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3030))
in (FStar_All.pipe_left w uu____3029))
in (

let tac_lid_app = (

let uu____3053 = (

let uu____3054 = (

let uu____3061 = (str_to_top_name "FStar_Ident.lid_of_str")
in ((uu____3061), (((w ml_fv))::[])))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3054))
in (FStar_All.pipe_left w uu____3053))
in (

let psc = (str_to_name "psc")
in (

let all_args = (str_to_name "args")
in (

let args = (

let uu____3069 = (

let uu____3072 = (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in (uu____3072)::(tac_fun)::[])
in (FStar_List.append uu____3069 (FStar_List.append arg_unembeddings ((res_embedding)::(tac_lid_app)::(psc)::[]))))
in (

let tabs = (match (tvar_names) with
| [] -> begin
(

let uu____3074 = (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((h), ((FStar_List.append args ((all_args)::[])))))))
in (mk_lam "args" uu____3074))
end
| uu____3077 -> begin
(

let uu____3080 = (FStar_All.pipe_left w (FStar_Extraction_ML_Syntax.MLE_App (((h), (args)))))
in (abstract_tvars tvar_names uu____3080))
end)
in (

let uu____3083 = (

let uu____3090 = (mk_lam "psc" tabs)
in ((uu____3090), ((arity + (Prims.parse_int "1"))), (false)))
in FStar_Pervasives_Native.Some (uu____3083)))))))))
end
| uu____3103 -> begin
(

let uu____3104 = (

let uu____3105 = (

let uu____3106 = (FStar_Syntax_Print.term_to_string t1)
in (Prims.strcat "Plugins not defined for type " uu____3106))
in NoTacticEmbedding (uu____3105))
in (FStar_Exn.raise uu____3104))
end))
end))))
end
| ((b, uu____3116))::bs3 -> begin
(

let uu____3128 = (

let uu____3131 = (mk_embedding env b.FStar_Syntax_Syntax.sort)
in (uu____3131)::accum_embeddings)
in (aux uu____3128 env bs3))
end))
in (FStar_All.try_with (fun uu___71_3141 -> (match (()) with
| () -> begin
(aux [] tvar_context bs1)
end)) (fun uu___70_3153 -> (match (uu___70_3153) with
| NoTacticEmbedding (msg) -> begin
((

let uu____3164 = (FStar_Ident.string_of_lid fv)
in (not_implemented_warning t1.FStar_Syntax_Syntax.pos uu____3164 msg));
FStar_Pervasives_Native.None;
)
end)))))))
end))))
end))))))))))))))))))))





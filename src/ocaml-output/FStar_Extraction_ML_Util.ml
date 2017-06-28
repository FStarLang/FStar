
open Prims
open FStar_Pervasives

let pruneNones = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| FStar_Pervasives_Native.Some (xs) -> begin
(xs)::ll
end
| FStar_Pervasives_Native.None -> begin
ll
end)) l []))


let mlconst_of_const : FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun sctt -> (match (sctt) with
| FStar_Const.Const_range (uu____30) -> begin
(failwith "Unsupported constant")
end
| FStar_Const.Const_effect -> begin
(failwith "Unsupported constant")
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
| FStar_Const.Const_bytearray (bytes, uu____46) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (bytes, uu____50) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end
| FStar_Const.Const_reify -> begin
(failwith "Unhandled constant: reify/reflect")
end
| FStar_Const.Const_reflect (uu____53) -> begin
(failwith "Unhandled constant: reify/reflect")
end))


let mlconst_of_const' : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> try
(match (()) with
| () -> begin
(mlconst_of_const c)
end)
with
| uu____68 -> begin
(

let uu____69 = (

let uu____70 = (FStar_Range.string_of_range p)
in (

let uu____71 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " uu____70 uu____71)))
in (failwith uu____69))
end)


let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst1 t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let uu____87 = (FStar_Util.find_opt (fun uu____96 -> (match (uu____96) with
| (y, uu____100) -> begin
(y = x)
end)) subst1)
in (match (uu____87) with
| FStar_Pervasives_Native.Some (ts) -> begin
(FStar_Pervasives_Native.snd ts)
end
| FStar_Pervasives_Native.None -> begin
t
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____111 = (

let uu____115 = (subst_aux subst1 t1)
in (

let uu____116 = (subst_aux subst1 t2)
in ((uu____115), (f), (uu____116))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____111))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(

let uu____121 = (

let uu____125 = (FStar_List.map (subst_aux subst1) args)
in ((uu____125), (path)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____121))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____130 = (FStar_List.map (subst_aux subst1) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____130))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun uu____139 args -> (match (uu____139) with
| (formals, t) -> begin
(match (((FStar_List.length formals) <> (FStar_List.length args))) with
| true -> begin
(failwith "Substitution must be fully applied (see GitHub issue #490)")
end
| uu____152 -> begin
(

let uu____153 = (FStar_List.zip formals args)
in (subst_aux uu____153 t))
end)
end))


let udelta_unfold : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option = (fun g uu___112_165 -> (match (uu___112_165) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n1) -> begin
(

let uu____171 = (FStar_Extraction_ML_UEnv.lookup_ty_const g n1)
in (match (uu____171) with
| FStar_Pervasives_Native.Some (ts) -> begin
(

let uu____175 = (subst ts args)
in FStar_Pervasives_Native.Some (uu____175))
end
| uu____176 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____178 -> begin
FStar_Pervasives_Native.None
end))


let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_PURE, uu____187) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| uu____188 -> begin
false
end))


let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun uu___113_194 -> (match (uu___113_194) with
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
| uu____207 -> begin
(

let uu____210 = (

let uu____211 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "Impossible (%s): Inconsistent effects %s and %s" uu____211 (eff_to_string f) (eff_to_string f')))
in (failwith uu____210))
end))


let join_l : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r fs -> (FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs))


let mk_ty_fun = (fun uu____236 -> (FStar_List.fold_right (fun uu____243 t -> (match (uu____243) with
| (uu____247, t0) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((t0), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end))))


type unfold_t =
FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option


let rec type_leq_c : unfold_t  ->  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option) = (fun unfold_ty e t t' -> (match (((t), (t'))) with
| (FStar_Extraction_ML_Syntax.MLTY_Var (x), FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
(match (((FStar_Pervasives_Native.fst x) = (FStar_Pervasives_Native.fst y))) with
| true -> begin
((true), (e))
end
| uu____289 -> begin
((false), (FStar_Pervasives_Native.None))
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(

let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| uu____312 -> begin
(

let e1 = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body1) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((FStar_List.append xs ys)), (body1)))
end
| uu____330 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((xs), (body)))
end)
in (

let uu____334 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____334 e1)))
end))
in (match (e) with
| FStar_Pervasives_Native.Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((x)::xs, body); FStar_Extraction_ML_Syntax.mlty = uu____341; FStar_Extraction_ML_Syntax.loc = uu____342}) -> begin
(

let uu____353 = ((type_leq unfold_ty t1' t1) && (eff_leq f f'))
in (match (uu____353) with
| true -> begin
(match (((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
(

let uu____363 = (type_leq unfold_ty t2 t2')
in (match (uu____363) with
| true -> begin
(

let body1 = (

let uu____371 = (type_leq unfold_ty t2 FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____371) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____375 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t2')))))
end))
in (

let uu____376 = (

let uu____378 = (

let uu____379 = (

let uu____382 = ((mk_ty_fun ()) ((x)::[]) body1.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____382))
in (FStar_All.pipe_left uu____379 (FStar_Extraction_ML_Syntax.MLE_Fun ((((x)::[]), (body1))))))
in FStar_Pervasives_Native.Some (uu____378))
in ((true), (uu____376))))
end
| uu____395 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____397 -> begin
(

let uu____398 = (

let uu____402 = (

let uu____404 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) uu____404))
in (type_leq_c unfold_ty uu____402 t2 t2'))
in (match (uu____398) with
| (ok, body1) -> begin
(

let res = (match (body1) with
| FStar_Pervasives_Native.Some (body2) -> begin
(

let uu____420 = (mk_fun ((x)::[]) body2)
in FStar_Pervasives_Native.Some (uu____420))
end
| uu____425 -> begin
FStar_Pervasives_Native.None
end)
in ((ok), (res)))
end))
end)
end
| uu____428 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____430 -> begin
(

let uu____432 = (((type_leq unfold_ty t1' t1) && (eff_leq f f')) && (type_leq unfold_ty t2 t2'))
in (match (uu____432) with
| true -> begin
((true), (e))
end
| uu____443 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
(match ((path = path')) with
| true -> begin
(

let uu____456 = (FStar_List.forall2 (type_leq unfold_ty) args args')
in (match (uu____456) with
| true -> begin
((true), (e))
end
| uu____464 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____466 -> begin
(

let uu____467 = (unfold_ty t)
in (match (uu____467) with
| FStar_Pervasives_Native.Some (t1) -> begin
(type_leq_c unfold_ty e t1 t')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____477 = (unfold_ty t')
in (match (uu____477) with
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

let uu____492 = (FStar_List.forall2 (type_leq unfold_ty) ts ts')
in (match (uu____492) with
| true -> begin
((true), (e))
end
| uu____500 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((true), (e))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (uu____503), uu____504) -> begin
(

let uu____508 = (unfold_ty t)
in (match (uu____508) with
| FStar_Pervasives_Native.Some (t1) -> begin
(type_leq_c unfold_ty e t1 t')
end
| uu____518 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (uu____521, FStar_Extraction_ML_Syntax.MLTY_Named (uu____522)) -> begin
(

let uu____526 = (unfold_ty t')
in (match (uu____526) with
| FStar_Pervasives_Native.Some (t'1) -> begin
(type_leq_c unfold_ty e t t'1)
end
| uu____536 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____539 -> begin
((false), (FStar_Pervasives_Native.None))
end))
and type_leq : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (

let uu____547 = (type_leq_c g FStar_Pervasives_Native.None t1 t2)
in (FStar_All.pipe_right uu____547 FStar_Pervasives_Native.fst)))


let is_type_abstraction = (fun uu___114_577 -> (match (uu___114_577) with
| ((FStar_Util.Inl (uu____583), uu____584))::uu____585 -> begin
true
end
| uu____597 -> begin
false
end))


let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int FStar_Pervasives_Native.option = (fun uu____610 -> (match (uu____610) with
| (ns, n1) -> begin
(

let uu____619 = (

let uu____620 = (FStar_Util.concat_l "." (FStar_List.append ns ((n1)::[])))
in (FStar_Parser_Const.is_tuple_datacon_string uu____620))
in (match (uu____619) with
| true -> begin
(

let uu____622 = (

let uu____623 = (FStar_Util.char_at n1 (Prims.parse_int "7"))
in (FStar_Util.int_of_char uu____623))
in FStar_Pervasives_Native.Some (uu____622))
end
| uu____624 -> begin
FStar_Pervasives_Native.None
end))
end))


let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(

let uu____633 = (is_xtuple mlp)
in (match (uu____633) with
| FStar_Pervasives_Native.Some (n1) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| uu____636 -> begin
e
end))
end
| uu____638 -> begin
e
end))


let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun uu___115_644 -> (match (uu___115_644) with
| (f)::uu____648 -> begin
(

let uu____650 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (uu____650) with
| (ns, uu____656) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| uu____663 -> begin
(failwith "impos")
end))


let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.ident.FStar_Ident.idText), (e))) fs vs))


let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int FStar_Pervasives_Native.option = (fun uu____701 -> (match (uu____701) with
| (ns, n1) -> begin
(

let uu____710 = (

let uu____711 = (FStar_Util.concat_l "." (FStar_List.append ns ((n1)::[])))
in (FStar_Parser_Const.is_tuple_constructor_string uu____711))
in (match (uu____710) with
| true -> begin
(

let uu____713 = (

let uu____714 = (FStar_Util.char_at n1 (Prims.parse_int "5"))
in (FStar_Util.int_of_char uu____714))
in FStar_Pervasives_Native.Some (uu____713))
end
| uu____715 -> begin
FStar_Pervasives_Native.None
end))
end))


let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(

let uu____724 = (is_xtuple_ty mlp)
in (match (uu____724) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| uu____727 -> begin
t
end))
end
| uu____729 -> begin
t
end))


let codegen_fsharp : Prims.unit  ->  Prims.bool = (fun uu____733 -> (

let uu____734 = (

let uu____735 = (FStar_Options.codegen ())
in (FStar_Option.get uu____735))
in (uu____734 = "FSharp")))


let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> (

let uu____743 = (codegen_fsharp ())
in (match (uu____743) with
| true -> begin
(FStar_String.concat "." ns)
end
| uu____744 -> begin
(FStar_String.concat "_" ns)
end)))


let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun uu____751 -> (match (uu____751) with
| (ns, n1) -> begin
(

let uu____759 = (codegen_fsharp ())
in (match (uu____759) with
| true -> begin
(FStar_String.concat "." (FStar_List.append ns ((n1)::[])))
end
| uu____760 -> begin
(FStar_String.concat "_" (FStar_List.append ns ((n1)::[])))
end))
end))


let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (

let uu____768 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in ((uu____768), (l.FStar_Ident.ident.FStar_Ident.idText))))


let rec erasableType : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun unfold_ty t -> (match ((FStar_Extraction_ML_UEnv.erasableTypeNoDelta t)) with
| true -> begin
true
end
| uu____786 -> begin
(

let uu____787 = (unfold_ty t)
in (match (uu____787) with
| FStar_Pervasives_Native.Some (t1) -> begin
(erasableType unfold_ty t1)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end))


let rec eraseTypeDeep : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun unfold_ty t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
(match ((etag = FStar_Extraction_ML_Syntax.E_PURE)) with
| true -> begin
(

let uu____808 = (

let uu____812 = (eraseTypeDeep unfold_ty tyd)
in (

let uu____816 = (eraseTypeDeep unfold_ty tycd)
in ((uu____812), (etag), (uu____816))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____808))
end
| uu____820 -> begin
t
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
(

let uu____825 = (erasableType unfold_ty t)
in (match (uu____825) with
| true -> begin
FStar_Extraction_ML_UEnv.erasedContent
end
| uu____829 -> begin
(

let uu____830 = (

let uu____834 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in ((uu____834), (mlp)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____830))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(

let uu____842 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____842))
end
| uu____847 -> begin
t
end))


let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_Equality")))))


let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (

let uu____849 = (

let uu____852 = ((mk_ty_fun ()) (((((("x"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::((((("y"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty uu____852))
in (FStar_All.pipe_left uu____849 (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_AmpAmp"))))))


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

let uu____909 = (conjoin x y)
in FStar_Pervasives_Native.Some (uu____909))
end))


let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (

let pos = (FStar_Range.start_of_range r)
in (

let line = (FStar_Range.line_of_pos pos)
in (

let uu____918 = (FStar_Range.file_of_range r)
in ((line), (uu____918))))))


let rec argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____926, b) -> begin
(

let uu____928 = (argTypes b)
in (a)::uu____928)
end
| uu____930 -> begin
[]
end))


let rec uncurry_mlty_fun : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____942, b) -> begin
(

let uu____944 = (uncurry_mlty_fun b)
in (match (uu____944) with
| (args, res) -> begin
(((a)::args), (res))
end))
end
| uu____956 -> begin
(([]), (t))
end))

type emb_decl =
| Embed
| Unembed


let uu___is_Embed : emb_decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Embed -> begin
true
end
| uu____962 -> begin
false
end))


let uu___is_Unembed : emb_decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unembed -> begin
true
end
| uu____967 -> begin
false
end))


let lid_to_name : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun l -> (

let uu____972 = (FStar_Extraction_ML_Syntax.mlpath_of_lident l)
in FStar_Extraction_ML_Syntax.MLE_Name (uu____972)))


let lid_to_top_name : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun l -> (

let uu____977 = (

let uu____978 = (FStar_Extraction_ML_Syntax.mlpath_of_lident l)
in FStar_Extraction_ML_Syntax.MLE_Name (uu____978))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____977)))


let str_to_name : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (

let uu____983 = (FStar_Ident.lid_of_str s)
in (lid_to_name uu____983)))


let str_to_top_name : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun s -> (

let uu____988 = (FStar_Ident.lid_of_str s)
in (lid_to_top_name uu____988)))


let fstar_tc_common_prefix : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (str_to_name (Prims.strcat "FStar_TypeChecker_Common." s)))


let fstar_refl_basic_prefix : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (str_to_name (Prims.strcat "FStar_Reflection_Basic." s)))


let fstar_refl_data_prefix : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (str_to_name (Prims.strcat "FStar_Reflection_Data." s)))


let mk_embedding : emb_decl  ->  Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun m s -> (match (m) with
| Embed -> begin
(fstar_refl_basic_prefix (Prims.strcat "embed_" s))
end
| Unembed -> begin
(fstar_refl_basic_prefix (Prims.strcat "unembed_" s))
end))


let rec mk_tac_param_type : FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun t -> (

let uu____1013 = (

let uu____1014 = (FStar_Syntax_Subst.compress t)
in uu____1014.FStar_Syntax_Syntax.n)
in (match (uu____1013) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid) -> begin
(fstar_tc_common_prefix "t_int")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) -> begin
(fstar_tc_common_prefix "t_bool")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(fstar_tc_common_prefix "t_unit")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid) -> begin
(fstar_tc_common_prefix "t_string")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1022 = (FStar_Reflection_Data.fstar_refl_types_lid "binder")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1022)) -> begin
(fstar_refl_data_prefix "t_binder")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1024 = (FStar_Reflection_Data.fstar_refl_types_lid "term")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1024)) -> begin
(fstar_refl_data_prefix "t_term")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1026 = (FStar_Reflection_Data.fstar_refl_types_lid "fv")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1026)) -> begin
(fstar_refl_data_prefix "t_fv")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1028 = (FStar_Reflection_Data.fstar_refl_syntax_lid "binder")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1028)) -> begin
(fstar_refl_data_prefix "t_binders")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1030 = (FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1030)) -> begin
(fstar_refl_data_prefix "t_norm_step")
end
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let uu____1047 = (

let uu____1048 = (FStar_Syntax_Subst.compress h)
in uu____1048.FStar_Syntax_Syntax.n)
in (match (uu____1047) with
| FStar_Syntax_Syntax.Tm_uinst (h', uu____1052) -> begin
(

let uu____1057 = (

let uu____1058 = (FStar_Syntax_Subst.compress h')
in uu____1058.FStar_Syntax_Syntax.n)
in (match (uu____1057) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.list_lid) -> begin
(

let arg_term = (

let uu____1065 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1065))
in (

let uu____1076 = (

let uu____1080 = (

let uu____1081 = (fstar_tc_common_prefix "t_list_of")
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____1081))
in (

let uu____1082 = (

let uu____1084 = (

let uu____1086 = (mk_tac_param_type arg_term)
in (uu____1086)::[])
in (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1084))
in ((uu____1080), (uu____1082))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1076)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.option_lid) -> begin
(

let arg_term = (

let uu____1092 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1092))
in (

let uu____1103 = (

let uu____1107 = (

let uu____1108 = (fstar_tc_common_prefix "t_option_of")
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____1108))
in (

let uu____1109 = (

let uu____1111 = (

let uu____1113 = (mk_tac_param_type arg_term)
in (uu____1113)::[])
in (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1111))
in ((uu____1107), (uu____1109))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1103)))
end
| uu____1115 -> begin
(

let uu____1116 = (

let uu____1117 = (

let uu____1118 = (FStar_Syntax_Subst.compress h')
in (FStar_Syntax_Print.term_to_string uu____1118))
in (Prims.strcat "Type term not defined for higher-order type " uu____1117))
in (failwith uu____1116))
end))
end
| uu____1119 -> begin
(failwith "Impossible")
end))
end
| uu____1120 -> begin
(

let uu____1121 = (

let uu____1122 = (

let uu____1123 = (FStar_Syntax_Subst.compress t)
in (FStar_Syntax_Print.term_to_string uu____1123))
in (Prims.strcat "Type term not defined for " uu____1122))
in (failwith uu____1121))
end)))


let rec mk_tac_embedding_path : emb_decl  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun m t -> (

let uu____1132 = (

let uu____1133 = (FStar_Syntax_Subst.compress t)
in uu____1133.FStar_Syntax_Syntax.n)
in (match (uu____1132) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid) -> begin
(mk_embedding m "int")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) -> begin
(mk_embedding m "bool")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(mk_embedding m "unit")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid) -> begin
(mk_embedding m "string")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1141 = (FStar_Reflection_Data.fstar_refl_types_lid "binder")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1141)) -> begin
(mk_embedding m "binder")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1143 = (FStar_Reflection_Data.fstar_refl_types_lid "term")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1143)) -> begin
(mk_embedding m "term")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1145 = (FStar_Reflection_Data.fstar_refl_types_lid "fv")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1145)) -> begin
(mk_embedding m "fvar")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1147 = (FStar_Reflection_Data.fstar_refl_syntax_lid "binders")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1147)) -> begin
(mk_embedding m "binders")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1149 = (FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1149)) -> begin
(mk_embedding m "norm_step")
end
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let uu____1166 = (

let uu____1167 = (FStar_Syntax_Subst.compress h)
in uu____1167.FStar_Syntax_Syntax.n)
in (match (uu____1166) with
| FStar_Syntax_Syntax.Tm_uinst (h', uu____1171) -> begin
(

let uu____1176 = (

let uu____1181 = (

let uu____1182 = (FStar_Syntax_Subst.compress h')
in uu____1182.FStar_Syntax_Syntax.n)
in (match (uu____1181) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.list_lid) -> begin
(

let arg_term = (

let uu____1193 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1193))
in (

let uu____1204 = (

let uu____1206 = (mk_tac_embedding_path m arg_term)
in (uu____1206)::[])
in (

let uu____1207 = (mk_tac_param_type arg_term)
in (("list"), (uu____1204), (uu____1207)))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.option_lid) -> begin
(

let arg_term = (

let uu____1213 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1213))
in (

let uu____1224 = (

let uu____1226 = (mk_tac_embedding_path m arg_term)
in (uu____1226)::[])
in (

let uu____1227 = (mk_tac_param_type arg_term)
in (("option"), (uu____1224), (uu____1227)))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.tactic_lid) -> begin
(failwith "Embedding for tactics not defined")
end
| uu____1234 -> begin
(

let uu____1235 = (

let uu____1236 = (

let uu____1237 = (FStar_Syntax_Subst.compress h')
in (FStar_Syntax_Print.term_to_string uu____1237))
in (Prims.strcat "Embedding not defined for higher-order type " uu____1236))
in (failwith uu____1235))
end))
in (match (uu____1176) with
| (ht, hargs, type_arg) -> begin
(

let hargs1 = (match (m) with
| Embed -> begin
(FStar_List.append hargs ((type_arg)::[]))
end
| Unembed -> begin
hargs
end)
in (

let uu____1250 = (

let uu____1254 = (

let uu____1255 = (mk_embedding m ht)
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____1255))
in (

let uu____1256 = (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) hargs1)
in ((uu____1254), (uu____1256))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1250)))
end))
end
| uu____1259 -> begin
(failwith "Impossible")
end))
end
| uu____1260 -> begin
(

let uu____1261 = (

let uu____1262 = (

let uu____1263 = (FStar_Syntax_Subst.compress t)
in (FStar_Syntax_Print.term_to_string uu____1263))
in (Prims.strcat "Embedding not defined for type " uu____1262))
in (failwith uu____1261))
end)))


let mk_interpretation_fun = (fun tac_lid assm_lid t bs -> (

let arg_types = (FStar_List.map (fun x -> (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort) bs)
in (

let arity = (FStar_List.length bs)
in (

let h = (

let uu____1315 = (

let uu____1316 = (FStar_Util.string_of_int arity)
in (Prims.strcat "FStar_Tactics_Interpreter.mk_tactic_interpretation_" uu____1316))
in (str_to_top_name uu____1315))
in (

let tac_fun = (

let uu____1324 = (

let uu____1328 = (

let uu____1329 = (

let uu____1330 = (FStar_Util.string_of_int arity)
in (Prims.strcat "FStar_Tactics_Native.from_tactic_" uu____1330))
in (str_to_top_name uu____1329))
in (

let uu____1337 = (

let uu____1339 = (lid_to_top_name tac_lid)
in (uu____1339)::[])
in ((uu____1328), (uu____1337))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1324))
in (

let tac_lid_app = (

let uu____1342 = (

let uu____1346 = (str_to_top_name "FStar_Ident.lid_of_str")
in ((uu____1346), (((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top assm_lid))::[])))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1342))
in (

let args = (

let uu____1350 = (

let uu____1352 = (str_to_name "ps")
in (uu____1352)::(tac_fun)::[])
in (

let uu____1353 = (

let uu____1355 = (FStar_List.map (mk_tac_embedding_path Unembed) arg_types)
in (

let uu____1357 = (

let uu____1359 = (mk_tac_embedding_path Embed t)
in (

let uu____1360 = (

let uu____1362 = (mk_tac_param_type t)
in (

let uu____1363 = (

let uu____1365 = (

let uu____1367 = (str_to_name "args")
in (uu____1367)::[])
in (tac_lid_app)::uu____1365)
in (uu____1362)::uu____1363))
in (uu____1359)::uu____1360))
in (FStar_List.append uu____1355 uu____1357)))
in (FStar_List.append uu____1350 uu____1353)))
in (

let app = (

let uu____1369 = (

let uu____1370 = (

let uu____1374 = (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) args)
in ((h), (uu____1374)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1370))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1369))
in FStar_Extraction_ML_Syntax.MLE_Fun (((((((("ps"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.MLTY_Top)))::((((("args"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.MLTY_Top)))::[]), (app)))))))))))





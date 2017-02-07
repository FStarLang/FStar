
open Prims

let pruneNones = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| Some (xs) -> begin
(xs)::ll
end
| None -> begin
ll
end)) l []))


let mlconst_of_const : FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun sctt -> (match (sctt) with
| (FStar_Const.Const_range (_)) | (FStar_Const.Const_effect) -> begin
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
| FStar_Const.Const_bytearray (bytes, uu____40) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (bytes, uu____44) -> begin
FStar_Extraction_ML_Syntax.MLC_String ((FStar_Util.string_of_unicode bytes))
end
| (FStar_Const.Const_reify) | (FStar_Const.Const_reflect (_)) -> begin
(failwith "Unhandled constant: reify/reflect")
end))


let mlconst_of_const' : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> try
(match (()) with
| () -> begin
(mlconst_of_const c)
end)
with
| uu____56 -> begin
(

let uu____57 = (

let uu____58 = (FStar_Range.string_of_range p)
in (

let uu____59 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " uu____58 uu____59)))
in (failwith uu____57))
end)


let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let uu____73 = (FStar_Util.find_opt (fun uu____79 -> (match (uu____79) with
| (y, uu____83) -> begin
(y = x)
end)) subst)
in (match (uu____73) with
| Some (ts) -> begin
(Prims.snd ts)
end
| None -> begin
t
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____94 = (

let uu____98 = (subst_aux subst t1)
in (

let uu____99 = (subst_aux subst t2)
in ((uu____98), (f), (uu____99))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____94))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(

let uu____104 = (

let uu____108 = (FStar_List.map (subst_aux subst) args)
in ((uu____108), (path)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____104))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____113 = (FStar_List.map (subst_aux subst) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____113))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun uu____120 args -> (match (uu____120) with
| (formals, t) -> begin
(match (((FStar_List.length formals) <> (FStar_List.length args))) with
| true -> begin
(failwith "Substitution must be fully applied (see GitHub issue #490)")
end
| uu____129 -> begin
(

let uu____130 = (FStar_List.zip formals args)
in (subst_aux uu____130 t))
end)
end))


let udelta_unfold : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option = (fun g uu___107_140 -> (match (uu___107_140) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(

let uu____146 = (FStar_Extraction_ML_UEnv.lookup_ty_const g n)
in (match (uu____146) with
| Some (ts) -> begin
(

let uu____150 = (subst ts args)
in Some (uu____150))
end
| uu____151 -> begin
None
end))
end
| uu____153 -> begin
None
end))


let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_PURE, uu____160) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| uu____161 -> begin
false
end))


let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun uu___108_166 -> (match (uu___108_166) with
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
| ((FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_PURE)) | ((FStar_Extraction_ML_Syntax.E_PURE, FStar_Extraction_ML_Syntax.E_IMPURE)) | ((FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE)) -> begin
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
| uu____176 -> begin
(

let uu____179 = (

let uu____180 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "Impossible (%s): Inconsistent effects %s and %s" uu____180 (eff_to_string f) (eff_to_string f')))
in (failwith uu____179))
end))


let join_l : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r fs -> (FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs))


let mk_ty_fun = (fun uu____200 -> (FStar_List.fold_right (fun uu____203 t -> (match (uu____203) with
| (uu____207, t0) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((t0), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end))))


type unfold_t =
FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option


let rec type_leq_c : unfold_t  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun unfold_ty e t t' -> (match (((t), (t'))) with
| (FStar_Extraction_ML_Syntax.MLTY_Var (x), FStar_Extraction_ML_Syntax.MLTY_Var (y)) -> begin
(match (((Prims.fst x) = (Prims.fst y))) with
| true -> begin
((true), (e))
end
| uu____252 -> begin
((false), (None))
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(

let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| uu____275 -> begin
(

let e = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((FStar_List.append xs ys)), (body)))
end
| uu____293 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((xs), (body)))
end)
in (

let uu____297 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____297 e)))
end))
in (match (e) with
| Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((x)::xs, body); FStar_Extraction_ML_Syntax.mlty = uu____304; FStar_Extraction_ML_Syntax.loc = uu____305}) -> begin
(

let uu____316 = ((type_leq unfold_ty t1' t1) && (eff_leq f f'))
in (match (uu____316) with
| true -> begin
(match (((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
(

let uu____326 = (type_leq unfold_ty t2 t2')
in (match (uu____326) with
| true -> begin
(

let body = (

let uu____334 = (type_leq unfold_ty t2 FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____334) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____338 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t2')))))
end))
in (

let uu____339 = (

let uu____341 = (

let uu____342 = (

let uu____345 = ((mk_ty_fun ()) ((x)::[]) body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____345))
in (FStar_All.pipe_left uu____342 (FStar_Extraction_ML_Syntax.MLE_Fun ((((x)::[]), (body))))))
in Some (uu____341))
in ((true), (uu____339))))
end
| uu____358 -> begin
((false), (None))
end))
end
| uu____360 -> begin
(

let uu____361 = (

let uu____365 = (

let uu____367 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____367))
in (type_leq_c unfold_ty uu____365 t2 t2'))
in (match (uu____361) with
| (ok, body) -> begin
(

let res = (match (body) with
| Some (body) -> begin
(

let uu____383 = (mk_fun ((x)::[]) body)
in Some (uu____383))
end
| uu____388 -> begin
None
end)
in ((ok), (res)))
end))
end)
end
| uu____391 -> begin
((false), (None))
end))
end
| uu____393 -> begin
(

let uu____395 = (((type_leq unfold_ty t1' t1) && (eff_leq f f')) && (type_leq unfold_ty t2 t2'))
in (match (uu____395) with
| true -> begin
((true), (e))
end
| uu____406 -> begin
((false), (None))
end))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
(match ((path = path')) with
| true -> begin
(

let uu____419 = (FStar_List.forall2 (type_leq unfold_ty) args args')
in (match (uu____419) with
| true -> begin
((true), (e))
end
| uu____427 -> begin
((false), (None))
end))
end
| uu____429 -> begin
(

let uu____430 = (unfold_ty t)
in (match (uu____430) with
| Some (t) -> begin
(type_leq_c unfold_ty e t t')
end
| None -> begin
(

let uu____440 = (unfold_ty t')
in (match (uu____440) with
| None -> begin
((false), (None))
end
| Some (t') -> begin
(type_leq_c unfold_ty e t t')
end))
end))
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Tuple (ts), FStar_Extraction_ML_Syntax.MLTY_Tuple (ts')) -> begin
(

let uu____455 = (FStar_List.forall2 (type_leq unfold_ty) ts ts')
in (match (uu____455) with
| true -> begin
((true), (e))
end
| uu____463 -> begin
((false), (None))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((true), (e))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (uu____466), uu____467) -> begin
(

let uu____471 = (unfold_ty t)
in (match (uu____471) with
| Some (t) -> begin
(type_leq_c unfold_ty e t t')
end
| uu____481 -> begin
((false), (None))
end))
end
| (uu____484, FStar_Extraction_ML_Syntax.MLTY_Named (uu____485)) -> begin
(

let uu____489 = (unfold_ty t')
in (match (uu____489) with
| Some (t') -> begin
(type_leq_c unfold_ty e t t')
end
| uu____499 -> begin
((false), (None))
end))
end
| uu____502 -> begin
((false), (None))
end))
and type_leq : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (

let uu____510 = (type_leq_c g None t1 t2)
in (FStar_All.pipe_right uu____510 Prims.fst)))


let is_type_abstraction = (fun uu___109_536 -> (match (uu___109_536) with
| ((FStar_Util.Inl (uu____542), uu____543))::uu____544 -> begin
true
end
| uu____556 -> begin
false
end))


let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun uu____568 -> (match (uu____568) with
| (ns, n) -> begin
(match ((ns = ("Prims")::[])) with
| true -> begin
(match (n) with
| "Mktuple2" -> begin
Some ((Prims.parse_int "2"))
end
| "Mktuple3" -> begin
Some ((Prims.parse_int "3"))
end
| "Mktuple4" -> begin
Some ((Prims.parse_int "4"))
end
| "Mktuple5" -> begin
Some ((Prims.parse_int "5"))
end
| "Mktuple6" -> begin
Some ((Prims.parse_int "6"))
end
| "Mktuple7" -> begin
Some ((Prims.parse_int "7"))
end
| "Mktuple8" -> begin
Some ((Prims.parse_int "8"))
end
| uu____580 -> begin
None
end)
end
| uu____581 -> begin
None
end)
end))


let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| uu____590 -> begin
e
end)
end
| uu____592 -> begin
e
end))


let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun uu___110_597 -> (match (uu___110_597) with
| (f)::uu____601 -> begin
(

let uu____603 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (uu____603) with
| (ns, uu____609) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| uu____615 -> begin
(failwith "impos")
end))


let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.ident.FStar_Ident.idText), (e))) fs vs))


let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun uu____647 -> (match (uu____647) with
| (ns, n) -> begin
(match ((ns = ("Prims")::[])) with
| true -> begin
(match (n) with
| "tuple2" -> begin
Some ((Prims.parse_int "2"))
end
| "tuple3" -> begin
Some ((Prims.parse_int "3"))
end
| "tuple4" -> begin
Some ((Prims.parse_int "4"))
end
| "tuple5" -> begin
Some ((Prims.parse_int "5"))
end
| "tuple6" -> begin
Some ((Prims.parse_int "6"))
end
| "tuple7" -> begin
Some ((Prims.parse_int "7"))
end
| "tuple8" -> begin
Some ((Prims.parse_int "8"))
end
| uu____659 -> begin
None
end)
end
| uu____660 -> begin
None
end)
end))


let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(match ((is_xtuple_ty mlp)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| uu____669 -> begin
t
end)
end
| uu____671 -> begin
t
end))


let codegen_fsharp : Prims.unit  ->  Prims.bool = (fun uu____674 -> (

let uu____675 = (

let uu____676 = (FStar_Options.codegen ())
in (FStar_Option.get uu____676))
in (uu____675 = "FSharp")))


let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> (

let uu____683 = (codegen_fsharp ())
in (match (uu____683) with
| true -> begin
(FStar_String.concat "." ns)
end
| uu____684 -> begin
(FStar_String.concat "_" ns)
end)))


let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun uu____690 -> (match (uu____690) with
| (ns, n) -> begin
(

let uu____698 = (codegen_fsharp ())
in (match (uu____698) with
| true -> begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end
| uu____699 -> begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end))
end))


let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (

let uu____706 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in ((uu____706), (l.FStar_Ident.ident.FStar_Ident.idText))))


let rec erasableType : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun unfold_ty t -> (match ((FStar_Extraction_ML_UEnv.erasableTypeNoDelta t)) with
| true -> begin
true
end
| uu____721 -> begin
(

let uu____722 = (unfold_ty t)
in (match (uu____722) with
| Some (t) -> begin
(erasableType unfold_ty t)
end
| None -> begin
false
end))
end))


let rec eraseTypeDeep : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun unfold_ty t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) -> begin
(match ((etag = FStar_Extraction_ML_Syntax.E_PURE)) with
| true -> begin
(

let uu____741 = (

let uu____745 = (eraseTypeDeep unfold_ty tyd)
in (

let uu____749 = (eraseTypeDeep unfold_ty tycd)
in ((uu____745), (etag), (uu____749))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____741))
end
| uu____753 -> begin
t
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
(

let uu____758 = (erasableType unfold_ty t)
in (match (uu____758) with
| true -> begin
FStar_Extraction_ML_UEnv.erasedContent
end
| uu____762 -> begin
(

let uu____763 = (

let uu____767 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in ((uu____767), (mlp)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____763))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(

let uu____775 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____775))
end
| uu____780 -> begin
t
end))


let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_Equality")))))


let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (

let uu____782 = (

let uu____785 = ((mk_ty_fun ()) (((((("x"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::((((("y"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty uu____785))
in (FStar_All.pipe_left uu____782 (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_AmpAmp"))))))


let conjoin : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e1 e2 -> (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_App (((prims_op_amp_amp), ((e1)::(e2)::[]))))))


let conjoin_opt : FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option = (fun e1 e2 -> (match (((e1), (e2))) with
| (None, None) -> begin
None
end
| ((Some (x), None)) | ((None, Some (x))) -> begin
Some (x)
end
| (Some (x), Some (y)) -> begin
(

let uu____837 = (conjoin x y)
in Some (uu____837))
end))


let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (

let pos = (FStar_Range.start_of_range r)
in (

let line = (FStar_Range.line_of_pos pos)
in (

let uu____845 = (FStar_Range.file_of_range r)
in ((line), (uu____845))))))


let rec argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____853, b) -> begin
(

let uu____855 = (argTypes b)
in (a)::uu____855)
end
| uu____857 -> begin
[]
end))


let rec uncurry_mlty_fun : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____868, b) -> begin
(

let uu____870 = (uncurry_mlty_fun b)
in (match (uu____870) with
| (args, res) -> begin
(((a)::args), (res))
end))
end
| uu____882 -> begin
(([]), (t))
end))





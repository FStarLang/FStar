
open Prims
open FStar_Pervasives

let pruneNones : 'a . 'a FStar_Pervasives_Native.option Prims.list  ->  'a Prims.list = (fun l -> (FStar_List.fold_right (fun x ll -> (match (x) with
| FStar_Pervasives_Native.Some (xs) -> begin
(xs)::ll
end
| FStar_Pervasives_Native.None -> begin
ll
end)) l []))


let mlconst_of_const : FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun sctt -> (match (sctt) with
| FStar_Const.Const_range (uu____40) -> begin
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
| FStar_Const.Const_bytearray (bytes, uu____65) -> begin
FStar_Extraction_ML_Syntax.MLC_Bytes (bytes)
end
| FStar_Const.Const_string (s, uu____71) -> begin
FStar_Extraction_ML_Syntax.MLC_String (s)
end
| FStar_Const.Const_reify -> begin
(failwith "Unhandled constant: reify/reflect")
end
| FStar_Const.Const_reflect (uu____72) -> begin
(failwith "Unhandled constant: reify/reflect")
end))


let mlconst_of_const' : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Extraction_ML_Syntax.mlconstant = (fun p c -> try
(match (()) with
| () -> begin
(mlconst_of_const c)
end)
with
| uu____87 -> begin
(

let uu____88 = (

let uu____89 = (FStar_Range.string_of_range p)
in (

let uu____90 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " uu____89 uu____90)))
in (failwith uu____88))
end)


let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst1 t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let uu____112 = (FStar_Util.find_opt (fun uu____126 -> (match (uu____126) with
| (y, uu____132) -> begin
(y = x)
end)) subst1)
in (match (uu____112) with
| FStar_Pervasives_Native.Some (ts) -> begin
(FStar_Pervasives_Native.snd ts)
end
| FStar_Pervasives_Native.None -> begin
t
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(

let uu____149 = (

let uu____156 = (subst_aux subst1 t1)
in (

let uu____157 = (subst_aux subst1 t2)
in ((uu____156), (f), (uu____157))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____149))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(

let uu____164 = (

let uu____171 = (FStar_List.map (subst_aux subst1) args)
in ((uu____171), (path)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____164))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(

let uu____179 = (FStar_List.map (subst_aux subst1) ts)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____179))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let try_subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option = (fun uu____192 args -> (match (uu____192) with
| (formals, t) -> begin
(match (((FStar_List.length formals) <> (FStar_List.length args))) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____202 -> begin
(

let uu____203 = (

let uu____204 = (FStar_List.zip formals args)
in (subst_aux uu____204 t))
in FStar_Pervasives_Native.Some (uu____203))
end)
end))


let subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun ts args -> (

let uu____223 = (try_subst ts args)
in (match (uu____223) with
| FStar_Pervasives_Native.None -> begin
(failwith "Substitution must be fully applied (see GitHub issue #490)")
end
| FStar_Pervasives_Native.Some (t) -> begin
t
end)))


let udelta_unfold : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option = (fun g uu___117_236 -> (match (uu___117_236) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n1) -> begin
(

let uu____245 = (FStar_Extraction_ML_UEnv.lookup_ty_const g n1)
in (match (uu____245) with
| FStar_Pervasives_Native.Some (ts) -> begin
(

let uu____251 = (try_subst ts args)
in (match (uu____251) with
| FStar_Pervasives_Native.None -> begin
(

let uu____256 = (

let uu____257 = (FStar_Extraction_ML_Syntax.string_of_mlpath n1)
in (

let uu____258 = (FStar_Util.string_of_int (FStar_List.length args))
in (

let uu____259 = (FStar_Util.string_of_int (FStar_List.length (FStar_Pervasives_Native.fst ts)))
in (FStar_Util.format3 "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)" uu____257 uu____258 uu____259))))
in (failwith uu____256))
end
| FStar_Pervasives_Native.Some (r) -> begin
FStar_Pervasives_Native.Some (r)
end))
end
| uu____263 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____266 -> begin
FStar_Pervasives_Native.None
end))


let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_PURE, uu____275) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| uu____276 -> begin
false
end))


let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun uu___118_284 -> (match (uu___118_284) with
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
| uu____297 -> begin
(

let uu____302 = (

let uu____303 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "Impossible (%s): Inconsistent effects %s and %s" uu____303 (eff_to_string f) (eff_to_string f')))
in (failwith uu____302))
end))


let join_l : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r fs -> (FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs))


let mk_ty_fun : 'Auu____322 . Prims.unit  ->  ('Auu____322 * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun uu____333 -> (FStar_List.fold_right (fun uu____342 t -> (match (uu____342) with
| (uu____348, t0) -> begin
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
| uu____403 -> begin
((false), (FStar_Pervasives_Native.None))
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(

let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| uu____435 -> begin
(

let e1 = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body1) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((FStar_List.append xs ys)), (body1)))
end
| uu____467 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((xs), (body)))
end)
in (

let uu____474 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____474 e1)))
end))
in (match (e) with
| FStar_Pervasives_Native.Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((x)::xs, body); FStar_Extraction_ML_Syntax.mlty = uu____484; FStar_Extraction_ML_Syntax.loc = uu____485}) -> begin
(

let uu____506 = ((type_leq unfold_ty t1' t1) && (eff_leq f f'))
in (match (uu____506) with
| true -> begin
(match (((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
(

let uu____522 = (type_leq unfold_ty t2 t2')
in (match (uu____522) with
| true -> begin
(

let body1 = (

let uu____533 = (type_leq unfold_ty t2 FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____533) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____537 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t2')))))
end))
in (

let uu____538 = (

let uu____541 = (

let uu____542 = (

let uu____545 = ((mk_ty_fun ()) ((x)::[]) body1.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty uu____545))
in (FStar_All.pipe_left uu____542 (FStar_Extraction_ML_Syntax.MLE_Fun ((((x)::[]), (body1))))))
in FStar_Pervasives_Native.Some (uu____541))
in ((true), (uu____538))))
end
| uu____570 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____573 -> begin
(

let uu____574 = (

let uu____581 = (

let uu____584 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____584))
in (type_leq_c unfold_ty uu____581 t2 t2'))
in (match (uu____574) with
| (ok, body1) -> begin
(

let res = (match (body1) with
| FStar_Pervasives_Native.Some (body2) -> begin
(

let uu____608 = (mk_fun ((x)::[]) body2)
in FStar_Pervasives_Native.Some (uu____608))
end
| uu____617 -> begin
FStar_Pervasives_Native.None
end)
in ((ok), (res)))
end))
end)
end
| uu____622 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____625 -> begin
(

let uu____628 = (((type_leq unfold_ty t1' t1) && (eff_leq f f')) && (type_leq unfold_ty t2 t2'))
in (match (uu____628) with
| true -> begin
((true), (e))
end
| uu____643 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
(match ((path = path')) with
| true -> begin
(

let uu____664 = (FStar_List.forall2 (type_leq unfold_ty) args args')
in (match (uu____664) with
| true -> begin
((true), (e))
end
| uu____676 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____679 -> begin
(

let uu____680 = (unfold_ty t)
in (match (uu____680) with
| FStar_Pervasives_Native.Some (t1) -> begin
(type_leq_c unfold_ty e t1 t')
end
| FStar_Pervasives_Native.None -> begin
(

let uu____694 = (unfold_ty t')
in (match (uu____694) with
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

let uu____716 = (FStar_List.forall2 (type_leq unfold_ty) ts ts')
in (match (uu____716) with
| true -> begin
((true), (e))
end
| uu____728 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((true), (e))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (uu____733), uu____734) -> begin
(

let uu____741 = (unfold_ty t)
in (match (uu____741) with
| FStar_Pervasives_Native.Some (t1) -> begin
(type_leq_c unfold_ty e t1 t')
end
| uu____755 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| (uu____760, FStar_Extraction_ML_Syntax.MLTY_Named (uu____761)) -> begin
(

let uu____768 = (unfold_ty t')
in (match (uu____768) with
| FStar_Pervasives_Native.Some (t'1) -> begin
(type_leq_c unfold_ty e t t'1)
end
| uu____782 -> begin
((false), (FStar_Pervasives_Native.None))
end))
end
| uu____787 -> begin
((false), (FStar_Pervasives_Native.None))
end))
and type_leq : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (

let uu____798 = (type_leq_c g FStar_Pervasives_Native.None t1 t2)
in (FStar_All.pipe_right uu____798 FStar_Pervasives_Native.fst)))


let is_type_abstraction : 'Auu____824 'Auu____825 'Auu____826 . (('Auu____826, 'Auu____825) FStar_Util.either * 'Auu____824) Prims.list  ->  Prims.bool = (fun uu___119_840 -> (match (uu___119_840) with
| ((FStar_Util.Inl (uu____851), uu____852))::uu____853 -> begin
true
end
| uu____876 -> begin
false
end))


let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int FStar_Pervasives_Native.option = (fun uu____898 -> (match (uu____898) with
| (ns, n1) -> begin
(

let uu____913 = (

let uu____914 = (FStar_Util.concat_l "." (FStar_List.append ns ((n1)::[])))
in (FStar_Parser_Const.is_tuple_datacon_string uu____914))
in (match (uu____913) with
| true -> begin
(

let uu____917 = (

let uu____918 = (FStar_Util.char_at n1 (Prims.parse_int "7"))
in (FStar_Util.int_of_char uu____918))
in FStar_Pervasives_Native.Some (uu____917))
end
| uu____919 -> begin
FStar_Pervasives_Native.None
end))
end))


let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(

let uu____930 = (is_xtuple mlp)
in (match (uu____930) with
| FStar_Pervasives_Native.Some (n1) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| uu____934 -> begin
e
end))
end
| uu____937 -> begin
e
end))


let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun uu___120_945 -> (match (uu___120_945) with
| (f)::uu____951 -> begin
(

let uu____954 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (uu____954) with
| (ns, uu____964) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| uu____975 -> begin
(failwith "impos")
end))


let record_fields : 'Auu____986 . FStar_Ident.lident Prims.list  ->  'Auu____986 Prims.list  ->  (Prims.string * 'Auu____986) Prims.list = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.ident.FStar_Ident.idText), (e))) fs vs))


let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int FStar_Pervasives_Native.option = (fun uu____1028 -> (match (uu____1028) with
| (ns, n1) -> begin
(

let uu____1043 = (

let uu____1044 = (FStar_Util.concat_l "." (FStar_List.append ns ((n1)::[])))
in (FStar_Parser_Const.is_tuple_constructor_string uu____1044))
in (match (uu____1043) with
| true -> begin
(

let uu____1047 = (

let uu____1048 = (FStar_Util.char_at n1 (Prims.parse_int "5"))
in (FStar_Util.int_of_char uu____1048))
in FStar_Pervasives_Native.Some (uu____1047))
end
| uu____1049 -> begin
FStar_Pervasives_Native.None
end))
end))


let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(

let uu____1060 = (is_xtuple_ty mlp)
in (match (uu____1060) with
| FStar_Pervasives_Native.Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| uu____1064 -> begin
t
end))
end
| uu____1067 -> begin
t
end))


let codegen_fsharp : Prims.unit  ->  Prims.bool = (fun uu____1071 -> (

let uu____1072 = (

let uu____1073 = (FStar_Options.codegen ())
in (FStar_Option.get uu____1073))
in (uu____1072 = "FSharp")))


let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> (

let uu____1084 = (codegen_fsharp ())
in (match (uu____1084) with
| true -> begin
(FStar_String.concat "." ns)
end
| uu____1085 -> begin
(FStar_String.concat "_" ns)
end)))


let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun uu____1095 -> (match (uu____1095) with
| (ns, n1) -> begin
(

let uu____1108 = (codegen_fsharp ())
in (match (uu____1108) with
| true -> begin
(FStar_String.concat "." (FStar_List.append ns ((n1)::[])))
end
| uu____1109 -> begin
(FStar_String.concat "_" (FStar_List.append ns ((n1)::[])))
end))
end))


let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (

let uu____1120 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in ((uu____1120), (l.FStar_Ident.ident.FStar_Ident.idText))))


let rec erasableType : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun unfold_ty t -> (match ((FStar_Extraction_ML_UEnv.erasableTypeNoDelta t)) with
| true -> begin
true
end
| uu____1142 -> begin
(

let uu____1143 = (unfold_ty t)
in (match (uu____1143) with
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

let uu____1165 = (

let uu____1172 = (eraseTypeDeep unfold_ty tyd)
in (

let uu____1176 = (eraseTypeDeep unfold_ty tycd)
in ((uu____1172), (etag), (uu____1176))))
in FStar_Extraction_ML_Syntax.MLTY_Fun (uu____1165))
end
| uu____1180 -> begin
t
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
(

let uu____1187 = (erasableType unfold_ty t)
in (match (uu____1187) with
| true -> begin
FStar_Extraction_ML_UEnv.erasedContent
end
| uu____1191 -> begin
(

let uu____1192 = (

let uu____1199 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in ((uu____1199), (mlp)))
in FStar_Extraction_ML_Syntax.MLTY_Named (uu____1192))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
(

let uu____1210 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in FStar_Extraction_ML_Syntax.MLTY_Tuple (uu____1210))
end
| uu____1216 -> begin
t
end))


let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_Equality")))))


let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (

let uu____1219 = (

let uu____1222 = ((mk_ty_fun ()) (((((("x"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::((((("y"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty)
in (FStar_Extraction_ML_Syntax.with_ty uu____1222))
in (FStar_All.pipe_left uu____1219 (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_AmpAmp"))))))


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

let uu____1315 = (conjoin x y)
in FStar_Pervasives_Native.Some (uu____1315))
end))


let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (

let pos = (FStar_Range.start_of_range r)
in (

let line = (FStar_Range.line_of_pos pos)
in (

let uu____1326 = (FStar_Range.file_of_range r)
in ((line), (uu____1326))))))


let rec doms_and_cod : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1344, b) -> begin
(

let uu____1346 = (doms_and_cod b)
in (match (uu____1346) with
| (ds, c) -> begin
(((a)::ds), (c))
end))
end
| uu____1367 -> begin
(([]), (t))
end))


let argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (

let uu____1378 = (doms_and_cod t)
in (FStar_Pervasives_Native.fst uu____1378)))


let rec uncurry_mlty_fun : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1404, b) -> begin
(

let uu____1406 = (uncurry_mlty_fun b)
in (match (uu____1406) with
| (args, res) -> begin
(((a)::args), (res))
end))
end
| uu____1427 -> begin
(([]), (t))
end))

type emb_decl =
| Embed
| Unembed


let uu___is_Embed : emb_decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Embed -> begin
true
end
| uu____1434 -> begin
false
end))


let uu___is_Unembed : emb_decl  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unembed -> begin
true
end
| uu____1439 -> begin
false
end))


let lid_to_name : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun l -> (

let uu____1444 = (FStar_Extraction_ML_Syntax.mlpath_of_lident l)
in FStar_Extraction_ML_Syntax.MLE_Name (uu____1444)))


let lid_to_top_name : FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun l -> (

let uu____1449 = (

let uu____1450 = (FStar_Extraction_ML_Syntax.mlpath_of_lident l)
in FStar_Extraction_ML_Syntax.MLE_Name (uu____1450))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1449)))


let str_to_name : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (

let uu____1455 = (FStar_Ident.lid_of_str s)
in (lid_to_name uu____1455)))


let str_to_top_name : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun s -> (

let uu____1460 = (FStar_Ident.lid_of_str s)
in (lid_to_top_name uu____1460)))


let fstar_syn_syn_prefix : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (str_to_name (Prims.strcat "FStar_Syntax_Syntax." s)))


let fstar_tc_common_prefix : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (str_to_name (Prims.strcat "FStar_TypeChecker_Common." s)))


let fstar_refl_basic_prefix : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (str_to_name (Prims.strcat "FStar_Reflection_Basic." s)))


let fstar_refl_data_prefix : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (str_to_name (Prims.strcat "FStar_Reflection_Data." s)))


let fstar_emb_basic_prefix : Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun s -> (str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)))


let mk_basic_embedding : emb_decl  ->  Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun m s -> (match (m) with
| Embed -> begin
(fstar_emb_basic_prefix (Prims.strcat "embed_" s))
end
| Unembed -> begin
(fstar_emb_basic_prefix (Prims.strcat "unembed_" s))
end))


let mk_embedding : emb_decl  ->  Prims.string  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun m s -> (match (m) with
| Embed -> begin
(fstar_refl_basic_prefix (Prims.strcat "embed_" s))
end
| Unembed -> begin
(fstar_refl_basic_prefix (Prims.strcat "unembed_" s))
end))


let mk_tactic_unembedding : FStar_Extraction_ML_Syntax.mlexpr' Prims.list  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun args -> (

let tac_arg = "t"
in (

let reify_tactic = (

let uu____1507 = (

let uu____1508 = (

let uu____1515 = (str_to_top_name "FStar_Tactics_Interpreter.reify_tactic")
in (

let uu____1516 = (

let uu____1519 = (str_to_top_name tac_arg)
in (uu____1519)::[])
in ((uu____1515), (uu____1516))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1508))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1507))
in (

let from_tac = (

let uu____1523 = (

let uu____1524 = (FStar_Util.string_of_int ((FStar_List.length args) - (Prims.parse_int "1")))
in (Prims.strcat "FStar_Tactics_Builtins.from_tac_" uu____1524))
in (str_to_top_name uu____1523))
in (

let unembed_tactic = (

let uu____1526 = (

let uu____1527 = (FStar_Util.string_of_int ((FStar_List.length args) - (Prims.parse_int "1")))
in (Prims.strcat "FStar_Tactics_Interpreter.unembed_tactic_" uu____1527))
in (str_to_top_name uu____1526))
in (

let app = (match ((FStar_List.length args)) with
| _0_43 when (_0_43 = (Prims.parse_int "1")) -> begin
(

let uu____1529 = (

let uu____1536 = (

let uu____1539 = (

let uu____1540 = (

let uu____1541 = (

let uu____1548 = (

let uu____1551 = (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) args)
in (FStar_List.append uu____1551 ((reify_tactic)::[])))
in ((unembed_tactic), (uu____1548)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1541))
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____1540))
in (uu____1539)::[])
in ((from_tac), (uu____1536)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1529))
end
| n1 -> begin
(

let uu____1559 = (

let uu____1560 = (

let uu____1563 = (FStar_Util.string_of_int n1)
in (uu____1563)::[])
in (FStar_Util.format "Unembedding not defined for tactics of %d arguments" uu____1560))
in (failwith uu____1559))
end)
in FStar_Extraction_ML_Syntax.MLE_Fun ((((((((tac_arg), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.MLTY_Top)))::((((("()"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.MLTY_Top)))::[]), ((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top app))))))))))


let rec mk_tac_param_type : FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun t -> (

let uu____1616 = (

let uu____1617 = (FStar_Syntax_Subst.compress t)
in uu____1617.FStar_Syntax_Syntax.n)
in (match (uu____1616) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid) -> begin
(fstar_syn_syn_prefix "t_int")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) -> begin
(fstar_syn_syn_prefix "t_bool")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(fstar_syn_syn_prefix "t_unit")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid) -> begin
(fstar_syn_syn_prefix "t_string")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1625 = (FStar_Reflection_Data.fstar_refl_types_lid "binder")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1625)) -> begin
(fstar_refl_data_prefix "t_binder")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1627 = (FStar_Reflection_Data.fstar_refl_types_lid "term")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1627)) -> begin
(fstar_refl_data_prefix "t_term")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1629 = (FStar_Reflection_Data.fstar_refl_types_lid "fv")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1629)) -> begin
(fstar_refl_data_prefix "t_fv")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1631 = (FStar_Reflection_Data.fstar_refl_syntax_lid "binder")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1631)) -> begin
(fstar_refl_data_prefix "t_binders")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1633 = (FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1633)) -> begin
(fstar_refl_data_prefix "t_norm_step")
end
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let uu____1656 = (

let uu____1657 = (FStar_Syntax_Subst.compress h)
in uu____1657.FStar_Syntax_Syntax.n)
in (match (uu____1656) with
| FStar_Syntax_Syntax.Tm_uinst (h', uu____1661) -> begin
(

let uu____1666 = (

let uu____1667 = (FStar_Syntax_Subst.compress h')
in uu____1667.FStar_Syntax_Syntax.n)
in (match (uu____1666) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.list_lid) -> begin
(

let arg_term = (

let uu____1674 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1674))
in (

let uu____1689 = (

let uu____1696 = (

let uu____1697 = (fstar_tc_common_prefix "t_list_of")
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____1697))
in (

let uu____1698 = (

let uu____1701 = (

let uu____1704 = (mk_tac_param_type arg_term)
in (uu____1704)::[])
in (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1701))
in ((uu____1696), (uu____1698))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1689)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.option_lid) -> begin
(

let arg_term = (

let uu____1711 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1711))
in (

let uu____1726 = (

let uu____1733 = (

let uu____1734 = (fstar_tc_common_prefix "t_option_of")
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____1734))
in (

let uu____1735 = (

let uu____1738 = (

let uu____1741 = (mk_tac_param_type arg_term)
in (uu____1741)::[])
in (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____1738))
in ((uu____1733), (uu____1735))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1726)))
end
| uu____1744 -> begin
(

let uu____1745 = (

let uu____1746 = (

let uu____1747 = (FStar_Syntax_Subst.compress h')
in (FStar_Syntax_Print.term_to_string uu____1747))
in (Prims.strcat "Type term not defined for higher-order type " uu____1746))
in (failwith uu____1745))
end))
end
| uu____1748 -> begin
(failwith "Impossible")
end))
end
| uu____1749 -> begin
(

let uu____1750 = (

let uu____1751 = (

let uu____1752 = (FStar_Syntax_Subst.compress t)
in (FStar_Syntax_Print.term_to_string uu____1752))
in (Prims.strcat "Type term not defined for " uu____1751))
in (failwith uu____1750))
end)))


let rec mk_tac_embedding_path : emb_decl  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun m t -> (

let uu____1761 = (

let uu____1762 = (FStar_Syntax_Subst.compress t)
in uu____1762.FStar_Syntax_Syntax.n)
in (match (uu____1761) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid) -> begin
(mk_basic_embedding m "int")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid) -> begin
(mk_basic_embedding m "bool")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) -> begin
(mk_basic_embedding m "unit")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid) -> begin
(mk_basic_embedding m "string")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1770 = (FStar_Reflection_Data.fstar_refl_types_lid "binder")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1770)) -> begin
(mk_embedding m "binder")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1772 = (FStar_Reflection_Data.fstar_refl_types_lid "term")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1772)) -> begin
(mk_embedding m "term")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1774 = (FStar_Reflection_Data.fstar_refl_types_lid "fv")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1774)) -> begin
(mk_embedding m "fvar")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1776 = (FStar_Reflection_Data.fstar_refl_syntax_lid "binders")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1776)) -> begin
(mk_embedding m "binders")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (

let uu____1778 = (FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step")
in (FStar_Syntax_Syntax.fv_eq_lid fv uu____1778)) -> begin
(mk_embedding m "norm_step")
end
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let uu____1801 = (

let uu____1802 = (FStar_Syntax_Subst.compress h)
in uu____1802.FStar_Syntax_Syntax.n)
in (match (uu____1801) with
| FStar_Syntax_Syntax.Tm_uinst (h', uu____1806) -> begin
(

let uu____1811 = (

let uu____1822 = (

let uu____1823 = (FStar_Syntax_Subst.compress h')
in uu____1823.FStar_Syntax_Syntax.n)
in (match (uu____1822) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.list_lid) -> begin
(

let arg_term = (

let uu____1840 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1840))
in (

let uu____1855 = (

let uu____1858 = (mk_tac_embedding_path m arg_term)
in (uu____1858)::[])
in (

let uu____1859 = (mk_tac_param_type arg_term)
in (("list"), (uu____1855), (uu____1859), (false)))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.option_lid) -> begin
(

let arg_term = (

let uu____1866 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1866))
in (

let uu____1881 = (

let uu____1884 = (mk_tac_embedding_path m arg_term)
in (uu____1884)::[])
in (

let uu____1885 = (mk_tac_param_type arg_term)
in (("option"), (uu____1881), (uu____1885), (false)))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.tactic_lid) -> begin
(

let arg_term = (

let uu____1892 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____1892))
in (

let uu____1907 = (

let uu____1910 = (mk_tac_embedding_path m arg_term)
in (uu____1910)::[])
in (

let uu____1911 = (mk_tac_param_type arg_term)
in (("list"), (uu____1907), (uu____1911), (true)))))
end
| uu____1914 -> begin
(

let uu____1915 = (

let uu____1916 = (

let uu____1917 = (FStar_Syntax_Subst.compress h')
in (FStar_Syntax_Print.term_to_string uu____1917))
in (Prims.strcat "Embedding not defined for higher-order type " uu____1916))
in (failwith uu____1915))
end))
in (match (uu____1811) with
| (ht, hargs, type_arg, is_tactic) -> begin
(

let hargs1 = (match (m) with
| Embed -> begin
(FStar_List.append hargs ((type_arg)::[]))
end
| Unembed -> begin
hargs
end)
in (match (is_tactic) with
| true -> begin
(match (m) with
| Embed -> begin
(failwith "Embedding not defined for tactic type")
end
| Unembed -> begin
(mk_tactic_unembedding hargs1)
end)
end
| uu____1941 -> begin
(

let uu____1942 = (

let uu____1949 = (

let uu____1950 = (mk_basic_embedding m ht)
in (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top uu____1950))
in (

let uu____1951 = (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) hargs1)
in ((uu____1949), (uu____1951))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1942))
end))
end))
end
| uu____1956 -> begin
(failwith "Impossible")
end))
end
| uu____1957 -> begin
(

let uu____1958 = (

let uu____1959 = (

let uu____1960 = (FStar_Syntax_Subst.compress t)
in (FStar_Syntax_Print.term_to_string uu____1960))
in (Prims.strcat "Embedding not defined for type " uu____1959))
in (failwith uu____1958))
end)))


let mk_interpretation_fun : 'Auu____1971 . FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlexpr'  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * 'Auu____1971) Prims.list  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun tac_lid assm_lid t bs -> (

let arg_types = (FStar_List.map (fun x -> (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort) bs)
in (

let arity = (FStar_List.length bs)
in (

let h = (

let uu____2023 = (

let uu____2024 = (FStar_Util.string_of_int arity)
in (Prims.strcat "FStar_Tactics_Interpreter.mk_tactic_interpretation_" uu____2024))
in (str_to_top_name uu____2023))
in (

let tac_fun = (

let uu____2032 = (

let uu____2039 = (

let uu____2040 = (

let uu____2041 = (FStar_Util.string_of_int arity)
in (Prims.strcat "FStar_Tactics_Native.from_tactic_" uu____2041))
in (str_to_top_name uu____2040))
in (

let uu____2048 = (

let uu____2051 = (lid_to_top_name tac_lid)
in (uu____2051)::[])
in ((uu____2039), (uu____2048))))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2032))
in (

let tac_lid_app = (

let uu____2055 = (

let uu____2062 = (str_to_top_name "FStar_Ident.lid_of_str")
in ((uu____2062), (((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top assm_lid))::[])))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2055))
in (

let args = (

let uu____2068 = (

let uu____2071 = (str_to_name "ps")
in (uu____2071)::(tac_fun)::[])
in (

let uu____2072 = (

let uu____2075 = (FStar_List.map (mk_tac_embedding_path Unembed) arg_types)
in (

let uu____2078 = (

let uu____2081 = (mk_tac_embedding_path Embed t)
in (

let uu____2082 = (

let uu____2085 = (mk_tac_param_type t)
in (

let uu____2086 = (

let uu____2089 = (

let uu____2092 = (str_to_name "args")
in (uu____2092)::[])
in (tac_lid_app)::uu____2089)
in (uu____2085)::uu____2086))
in (uu____2081)::uu____2082))
in (FStar_List.append uu____2075 uu____2078)))
in (FStar_List.append uu____2068 uu____2072)))
in (

let app = (

let uu____2094 = (

let uu____2095 = (

let uu____2102 = (FStar_List.map (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) args)
in ((h), (uu____2102)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____2095))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____2094))
in FStar_Extraction_ML_Syntax.MLE_Fun (((((((("ps"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.MLTY_Top)))::((((("args"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.MLTY_Top)))::[]), (app)))))))))))





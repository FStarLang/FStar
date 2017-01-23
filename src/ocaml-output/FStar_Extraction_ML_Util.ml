
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
(failwith (let _0_177 = (FStar_Range.string_of_range p)
in (let _0_176 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format2 "(%s) Failed to translate constant %s " _0_177 _0_176))))
end)


let rec subst_aux : (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun subst t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let uu____70 = (FStar_Util.find_opt (fun uu____76 -> (match (uu____76) with
| (y, uu____80) -> begin
(y = x)
end)) subst)
in (match (uu____70) with
| Some (ts) -> begin
(Prims.snd ts)
end
| None -> begin
t
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun ((let _0_179 = (subst_aux subst t1)
in (let _0_178 = (subst_aux subst t2)
in ((_0_179), (f), (_0_178)))))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
FStar_Extraction_ML_Syntax.MLTY_Named ((let _0_180 = (FStar_List.map (subst_aux subst) args)
in ((_0_180), (path))))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple ((FStar_List.map (subst_aux subst) ts))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let subst : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun uu____103 args -> (match (uu____103) with
| (formals, t) -> begin
(match (((FStar_List.length formals) <> (FStar_List.length args))) with
| true -> begin
(failwith "Substitution must be fully applied (see GitHub issue #490)")
end
| uu____112 -> begin
(let _0_181 = (FStar_List.zip formals args)
in (subst_aux _0_181 t))
end)
end))


let udelta_unfold : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.option = (fun g uu___106_119 -> (match (uu___106_119) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, n) -> begin
(

let uu____125 = (FStar_Extraction_ML_UEnv.lookup_ty_const g n)
in (match (uu____125) with
| Some (ts) -> begin
Some ((subst ts args))
end
| uu____129 -> begin
None
end))
end
| uu____131 -> begin
None
end))


let eff_leq : FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.e_tag  ->  Prims.bool = (fun f f' -> (match (((f), (f'))) with
| (FStar_Extraction_ML_Syntax.E_PURE, uu____138) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_GHOST, FStar_Extraction_ML_Syntax.E_GHOST) -> begin
true
end
| (FStar_Extraction_ML_Syntax.E_IMPURE, FStar_Extraction_ML_Syntax.E_IMPURE) -> begin
true
end
| uu____139 -> begin
false
end))


let eff_to_string : FStar_Extraction_ML_Syntax.e_tag  ->  Prims.string = (fun uu___107_144 -> (match (uu___107_144) with
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
| uu____154 -> begin
(failwith (let _0_182 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "Impossible (%s): Inconsistent effects %s and %s" _0_182 (eff_to_string f) (eff_to_string f'))))
end))


let join_l : FStar_Range.range  ->  FStar_Extraction_ML_Syntax.e_tag Prims.list  ->  FStar_Extraction_ML_Syntax.e_tag = (fun r fs -> (FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs))


let mk_ty_fun = (fun uu____176 -> (FStar_List.fold_right (fun uu____179 t -> (match (uu____179) with
| (uu____183, t0) -> begin
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
| uu____228 -> begin
((false), (None))
end)
end
| (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2), FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) -> begin
(

let mk_fun = (fun xs body -> (match (xs) with
| [] -> begin
body
end
| uu____251 -> begin
(

let e = (match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Fun (ys, body) -> begin
FStar_Extraction_ML_Syntax.MLE_Fun ((((FStar_List.append xs ys)), (body)))
end
| uu____269 -> begin
FStar_Extraction_ML_Syntax.MLE_Fun (((xs), (body)))
end)
in (let _0_183 = ((mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty)
in (FStar_Extraction_ML_Syntax.with_ty _0_183 e)))
end))
in (match (e) with
| Some ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((x)::xs, body); FStar_Extraction_ML_Syntax.mlty = uu____279; FStar_Extraction_ML_Syntax.loc = uu____280}) -> begin
(

let uu____291 = ((type_leq unfold_ty t1' t1) && (eff_leq f f'))
in (match (uu____291) with
| true -> begin
(match (((f = FStar_Extraction_ML_Syntax.E_PURE) && (f' = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
(

let uu____301 = (type_leq unfold_ty t2 t2')
in (match (uu____301) with
| true -> begin
(

let body = (

let uu____309 = (type_leq unfold_ty t2 FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____309) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____313 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t2') (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (t2')))))
end))
in (let _0_185 = Some ((let _0_184 = (FStar_Extraction_ML_Syntax.with_ty ((mk_ty_fun ()) ((x)::[]) body.FStar_Extraction_ML_Syntax.mlty))
in (FStar_All.pipe_left _0_184 (FStar_Extraction_ML_Syntax.MLE_Fun ((((x)::[]), (body)))))))
in ((true), (_0_185))))
end
| uu____326 -> begin
((false), (None))
end))
end
| uu____328 -> begin
(

let uu____329 = (let _0_188 = (let _0_187 = (mk_fun xs body)
in (FStar_All.pipe_left (fun _0_186 -> Some (_0_186)) _0_187))
in (type_leq_c unfold_ty _0_188 t2 t2'))
in (match (uu____329) with
| (ok, body) -> begin
(

let res = (match (body) with
| Some (body) -> begin
Some ((mk_fun ((x)::[]) body))
end
| uu____352 -> begin
None
end)
in ((ok), (res)))
end))
end)
end
| uu____355 -> begin
((false), (None))
end))
end
| uu____357 -> begin
(

let uu____359 = (((type_leq unfold_ty t1' t1) && (eff_leq f f')) && (type_leq unfold_ty t2 t2'))
in (match (uu____359) with
| true -> begin
((true), (e))
end
| uu____370 -> begin
((false), (None))
end))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (args, path), FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) -> begin
(match ((path = path')) with
| true -> begin
(

let uu____383 = (FStar_List.forall2 (type_leq unfold_ty) args args')
in (match (uu____383) with
| true -> begin
((true), (e))
end
| uu____391 -> begin
((false), (None))
end))
end
| uu____393 -> begin
(

let uu____394 = (unfold_ty t)
in (match (uu____394) with
| Some (t) -> begin
(type_leq_c unfold_ty e t t')
end
| None -> begin
(

let uu____404 = (unfold_ty t')
in (match (uu____404) with
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

let uu____419 = (FStar_List.forall2 (type_leq unfold_ty) ts ts')
in (match (uu____419) with
| true -> begin
((true), (e))
end
| uu____427 -> begin
((false), (None))
end))
end
| (FStar_Extraction_ML_Syntax.MLTY_Top, FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
((true), (e))
end
| (FStar_Extraction_ML_Syntax.MLTY_Named (uu____430), uu____431) -> begin
(

let uu____435 = (unfold_ty t)
in (match (uu____435) with
| Some (t) -> begin
(type_leq_c unfold_ty e t t')
end
| uu____445 -> begin
((false), (None))
end))
end
| (uu____448, FStar_Extraction_ML_Syntax.MLTY_Named (uu____449)) -> begin
(

let uu____453 = (unfold_ty t')
in (match (uu____453) with
| Some (t') -> begin
(type_leq_c unfold_ty e t t')
end
| uu____463 -> begin
((false), (None))
end))
end
| uu____466 -> begin
((false), (None))
end))
and type_leq : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (let _0_189 = (type_leq_c g None t1 t2)
in (FStar_All.pipe_right _0_189 Prims.fst)))


let is_type_abstraction = (fun uu___108_496 -> (match (uu___108_496) with
| ((FStar_Util.Inl (uu____502), uu____503))::uu____504 -> begin
true
end
| uu____516 -> begin
false
end))


let is_xtuple : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun uu____528 -> (match (uu____528) with
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
| uu____540 -> begin
None
end)
end
| uu____541 -> begin
None
end)
end))


let resugar_exp : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) -> begin
(match ((is_xtuple mlp)) with
| Some (n) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Tuple (args)))
end
| uu____550 -> begin
e
end)
end
| uu____552 -> begin
e
end))


let record_field_path : FStar_Ident.lident Prims.list  ->  Prims.string Prims.list = (fun uu___109_557 -> (match (uu___109_557) with
| (f)::uu____561 -> begin
(

let uu____563 = (FStar_Util.prefix f.FStar_Ident.ns)
in (match (uu____563) with
| (ns, uu____569) -> begin
(FStar_All.pipe_right ns (FStar_List.map (fun id -> id.FStar_Ident.idText)))
end))
end
| uu____575 -> begin
(failwith "impos")
end))


let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.ident.FStar_Ident.idText), (e))) fs vs))


let is_xtuple_ty : (Prims.string Prims.list * Prims.string)  ->  Prims.int Prims.option = (fun uu____607 -> (match (uu____607) with
| (ns, n) -> begin
(match ((ns = ("Prims")::[])) with
| true -> begin
(

let uu____618 = (FStar_Options.universes ())
in (match (uu____618) with
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
| uu____621 -> begin
None
end)
end
| uu____622 -> begin
(match (n) with
| "Tuple2" -> begin
Some ((Prims.parse_int "2"))
end
| "Tuple3" -> begin
Some ((Prims.parse_int "3"))
end
| "Tuple4" -> begin
Some ((Prims.parse_int "4"))
end
| "Tuple5" -> begin
Some ((Prims.parse_int "5"))
end
| "Tuple6" -> begin
Some ((Prims.parse_int "6"))
end
| "Tuple7" -> begin
Some ((Prims.parse_int "7"))
end
| "Tuple8" -> begin
Some ((Prims.parse_int "8"))
end
| uu____624 -> begin
None
end)
end))
end
| uu____625 -> begin
None
end)
end))


let resugar_mlty : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) -> begin
(

let uu____633 = (is_xtuple_ty mlp)
in (match (uu____633) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple (args)
end
| uu____636 -> begin
t
end))
end
| uu____638 -> begin
t
end))


let codegen_fsharp : Prims.unit  ->  Prims.bool = (fun uu____641 -> (let _0_190 = (FStar_Option.get (FStar_Options.codegen ()))
in (_0_190 = "FSharp")))


let flatten_ns : Prims.string Prims.list  ->  Prims.string = (fun ns -> (

let uu____647 = (codegen_fsharp ())
in (match (uu____647) with
| true -> begin
(FStar_String.concat "." ns)
end
| uu____648 -> begin
(FStar_String.concat "_" ns)
end)))


let flatten_mlpath : (Prims.string Prims.list * Prims.string)  ->  Prims.string = (fun uu____654 -> (match (uu____654) with
| (ns, n) -> begin
(

let uu____662 = (codegen_fsharp ())
in (match (uu____662) with
| true -> begin
(FStar_String.concat "." (FStar_List.append ns ((n)::[])))
end
| uu____663 -> begin
(FStar_String.concat "_" (FStar_List.append ns ((n)::[])))
end))
end))


let mlpath_of_lid : FStar_Ident.lident  ->  (Prims.string Prims.list * Prims.string) = (fun l -> (let _0_191 = (FStar_All.pipe_right l.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText)))
in ((_0_191), (l.FStar_Ident.ident.FStar_Ident.idText))))


let rec erasableType : unfold_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun unfold_ty t -> (match ((FStar_Extraction_ML_UEnv.erasableTypeNoDelta t)) with
| true -> begin
true
end
| uu____683 -> begin
(

let uu____684 = (unfold_ty t)
in (match (uu____684) with
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
FStar_Extraction_ML_Syntax.MLTY_Fun ((let _0_193 = (eraseTypeDeep unfold_ty tyd)
in (let _0_192 = (eraseTypeDeep unfold_ty tycd)
in ((_0_193), (etag), (_0_192)))))
end
| uu____709 -> begin
t
end)
end
| FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) -> begin
(

let uu____714 = (erasableType unfold_ty t)
in (match (uu____714) with
| true -> begin
FStar_Extraction_ML_UEnv.erasedContent
end
| uu____718 -> begin
FStar_Extraction_ML_Syntax.MLTY_Named ((let _0_194 = (FStar_List.map (eraseTypeDeep unfold_ty) lty)
in ((_0_194), (mlp))))
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (lty) -> begin
FStar_Extraction_ML_Syntax.MLTY_Tuple ((FStar_List.map (eraseTypeDeep unfold_ty) lty))
end
| uu____728 -> begin
t
end))


let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_Equality")))))


let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr = (let _0_195 = (FStar_Extraction_ML_Syntax.with_ty ((mk_ty_fun ()) (((((("x"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::((((("y"), ((Prims.parse_int "0")))), (FStar_Extraction_ML_Syntax.ml_bool_ty)))::[]) FStar_Extraction_ML_Syntax.ml_bool_ty))
in (FStar_All.pipe_left _0_195 (FStar_Extraction_ML_Syntax.MLE_Name (((("Prims")::[]), ("op_AmpAmp"))))))


let conjoin : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun e1 e2 -> (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_App (((prims_op_amp_amp), ((e1)::(e2)::[]))))))


let conjoin_opt : FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option = (fun e1 e2 -> (match (((e1), (e2))) with
| (None, None) -> begin
None
end
| ((Some (x), None)) | ((None, Some (x))) -> begin
Some (x)
end
| (Some (x), Some (y)) -> begin
Some ((conjoin x y))
end))


let mlloc_of_range : FStar_Range.range  ->  (Prims.int * Prims.string) = (fun r -> (

let pos = (FStar_Range.start_of_range r)
in (

let line = (FStar_Range.line_of_pos pos)
in (let _0_196 = (FStar_Range.file_of_range r)
in ((line), (_0_196))))))


let rec argTypes : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____795, b) -> begin
(let _0_197 = (argTypes b)
in (a)::_0_197)
end
| uu____797 -> begin
[]
end))


let rec uncurry_mlty_fun : FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlty Prims.list * FStar_Extraction_ML_Syntax.mlty) = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____808, b) -> begin
(

let uu____810 = (uncurry_mlty_fun b)
in (match (uu____810) with
| (args, res) -> begin
(((a)::args), (res))
end))
end
| uu____822 -> begin
(([]), (t))
end))





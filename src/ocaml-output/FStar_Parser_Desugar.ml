
open Prims

let imp_tag : FStar_Absyn_Syntax.arg_qualifier = FStar_Absyn_Syntax.Implicit (false)


let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _61_1 -> (match (_61_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (imp_tag)
end
| _61_36 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (imp_tag)))
end
| _61_43 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_61_47) -> begin
true
end
| _61_50 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _61_55 -> begin
t
end))


let rec unlabel : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _61_61, _61_63) -> begin
(unlabel t)
end
| _61_67 -> begin
t
end))


let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _153_17 = (let _153_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_153_16))
in (FStar_Parser_AST.mk_term _153_17 r FStar_Parser_AST.Kind)))


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _61_2 -> (match (_61_2) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' when (arity = 1) -> begin
"Minus"
end
| '-' -> begin
"Subtraction"
end
| '/' -> begin
"Slash"
end
| '<' -> begin
"Less"
end
| '=' -> begin
"Equals"
end
| '>' -> begin
"Greater"
end
| '_' -> begin
"Underscore"
end
| '|' -> begin
"Bar"
end
| '!' -> begin
"Bang"
end
| '^' -> begin
"Hat"
end
| '%' -> begin
"Percent"
end
| '*' -> begin
"Star"
end
| '?' -> begin
"Question"
end
| ':' -> begin
"Colon"
end
| _61_90 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _153_28 = (let _153_26 = (FStar_Util.char_at s i)
in (name_of_char _153_26))
in (let _153_27 = (aux (i + 1))
in (_153_28)::_153_27))
end)
in (let _153_30 = (let _153_29 = (aux 0)
in (FStar_String.concat "_" _153_29))
in (Prims.strcat "op_" _153_30)))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _153_40 = (let _153_39 = (let _153_38 = (let _153_37 = (compile_op n s)
in ((_153_37), (r)))
in (FStar_Absyn_Syntax.mk_ident _153_38))
in (_153_39)::[])
in (FStar_All.pipe_right _153_40 FStar_Absyn_Syntax.lid_of_ids)))


let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (

let r = (fun l -> (let _153_51 = (FStar_Ident.set_lid_range l rng)
in Some (_153_51)))
in (

let fallback = (fun _61_104 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Absyn_Const.op_Eq)
end
| ":=" -> begin
(r FStar_Absyn_Const.op_ColonEq)
end
| "<" -> begin
(r FStar_Absyn_Const.op_LT)
end
| "<=" -> begin
(r FStar_Absyn_Const.op_LTE)
end
| ">" -> begin
(r FStar_Absyn_Const.op_GT)
end
| ">=" -> begin
(r FStar_Absyn_Const.op_GTE)
end
| "&&" -> begin
(r FStar_Absyn_Const.op_And)
end
| "||" -> begin
(r FStar_Absyn_Const.op_Or)
end
| "*" -> begin
(r FStar_Absyn_Const.op_Multiply)
end
| "+" -> begin
(r FStar_Absyn_Const.op_Addition)
end
| "-" when (arity = 1) -> begin
(r FStar_Absyn_Const.op_Minus)
end
| "-" -> begin
(r FStar_Absyn_Const.op_Subtraction)
end
| "/" -> begin
(r FStar_Absyn_Const.op_Division)
end
| "%" -> begin
(r FStar_Absyn_Const.op_Modulus)
end
| "!" -> begin
(r FStar_Absyn_Const.read_lid)
end
| "@" -> begin
(r FStar_Absyn_Const.list_append_lid)
end
| "^" -> begin
(r FStar_Absyn_Const.strcat_lid)
end
| "|>" -> begin
(r FStar_Absyn_Const.pipe_right_lid)
end
| "<|" -> begin
(r FStar_Absyn_Const.pipe_left_lid)
end
| "<>" -> begin
(r FStar_Absyn_Const.op_notEq)
end
| _61_126 -> begin
None
end)
end))
in (match ((let _153_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _153_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _61_137); FStar_Absyn_Syntax.tk = _61_134; FStar_Absyn_Syntax.pos = _61_132; FStar_Absyn_Syntax.fvs = _61_130; FStar_Absyn_Syntax.uvs = _61_128}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _61_143 -> begin
(fallback ())
end))))


let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (

let r = (fun l -> (let _153_65 = (FStar_Ident.set_lid_range l rng)
in Some (_153_65)))
in (match (s) with
| "~" -> begin
(r FStar_Absyn_Const.not_lid)
end
| "==" -> begin
(r FStar_Absyn_Const.eq2_lid)
end
| "=!=" -> begin
(r FStar_Absyn_Const.neq2_lid)
end
| "<<" -> begin
(r FStar_Absyn_Const.precedes_lid)
end
| "/\\" -> begin
(r FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
(r FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
(r FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
(r FStar_Absyn_Const.iff_lid)
end
| s -> begin
(match ((let _153_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _153_66))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _61_166; FStar_Absyn_Syntax.pos = _61_164; FStar_Absyn_Syntax.fvs = _61_162; FStar_Absyn_Syntax.uvs = _61_160}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _61_172 -> begin
None
end)
end)))


let rec is_type : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _153_73 = (unparen t)
in _153_73.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_61_177) -> begin
true
end
| FStar_Parser_AST.Op ("*", (hd)::_61_181) -> begin
(is_type env hd)
end
| (FStar_Parser_AST.Op ("==", _)) | (FStar_Parser_AST.Op ("=!=", _)) | (FStar_Parser_AST.Op ("~", _)) | (FStar_Parser_AST.Op ("/\\", _)) | (FStar_Parser_AST.Op ("\\/", _)) | (FStar_Parser_AST.Op ("==>", _)) | (FStar_Parser_AST.Op ("<==>", _)) | (FStar_Parser_AST.Op ("<<", _)) -> begin
true
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) t.FStar_Parser_AST.range s)) with
| None -> begin
false
end
| _61_232 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_61_255) -> begin
true
end
| _61_258 -> begin
(FStar_Parser_DesugarEnv.is_type_lid env l)
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(FStar_Parser_DesugarEnv.is_type_lid env l)
end
| (FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (l); FStar_Parser_AST.range = _; FStar_Parser_AST.level = _}, arg, FStar_Parser_AST.Nothing)) | (FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = _; FStar_Parser_AST.level = _}, arg, FStar_Parser_AST.Nothing)) when (l.FStar_Ident.str = "ref") -> begin
(is_type env arg)
end
| (FStar_Parser_AST.App (t, _, _)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(is_type env t)
end
| FStar_Parser_AST.Product (_61_299, t) -> begin
(not ((is_kind env t)))
end
| FStar_Parser_AST.If (t, t1, t2) -> begin
(((is_type env t) || (is_type env t1)) || (is_type env t2))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(

let rec aux = (fun env pats -> (match (pats) with
| [] -> begin
(is_type env t)
end
| (hd)::pats -> begin
(match (hd.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatVar (_)) -> begin
(aux env pats)
end
| FStar_Parser_AST.PatTvar (id, _61_325) -> begin
(

let _61_331 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_61_331) with
| (env, _61_330) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(

let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _153_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _153_78 Prims.fst))
end
| _61_346 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _61_349 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_61_354); FStar_Parser_AST.prange = _61_352}, _61_358))::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_61_370); FStar_Parser_AST.prange = _61_368}, _61_374); FStar_Parser_AST.prange = _61_366}, _61_379))::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_61_389); FStar_Parser_AST.prange = _61_387}, _61_393))::[], t) -> begin
(is_type env t)
end
| _61_400 -> begin
false
end)
end)
and is_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _153_81 = (unparen t)
in _153_81.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _61_409; FStar_Ident.ident = _61_407; FStar_Ident.nsstr = _61_405; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_61_413, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _61_426 -> begin
false
end)
end)


let rec is_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  Prims.bool = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_61_430) -> begin
false
end
| (FStar_Parser_AST.TAnnotated (_)) | (FStar_Parser_AST.TVariable (_)) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end else begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_61_445) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected binder without annotation"), (b.FStar_Parser_AST.brange)))))
end
| FStar_Parser_AST.TVariable (_61_448) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_61_451) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _153_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _153_92)))


let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_61_467) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _61_474 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_61_474) with
| (env, _61_473) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_61_476, term) -> begin
(let _153_99 = (free_type_vars env term)
in ((env), (_153_99)))
end
| FStar_Parser_AST.TAnnotated (id, _61_482) -> begin
(

let _61_488 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_61_488) with
| (env, _61_487) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _153_100 = (free_type_vars env t)
in ((env), (_153_100)))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _153_103 = (unparen t)
in _153_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _61_497 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_61_533, ts) -> begin
(FStar_List.collect (fun _61_540 -> (match (_61_540) with
| (t, _61_539) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_61_542, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _61_549) -> begin
(let _153_106 = (free_type_vars env t1)
in (let _153_105 = (free_type_vars env t2)
in (FStar_List.append _153_106 _153_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _61_558 = (free_type_vars_b env b)
in (match (_61_558) with
| (env, f) -> begin
(let _153_107 = (free_type_vars env t)
in (FStar_List.append f _153_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _61_574 = (FStar_List.fold_left (fun _61_567 binder -> (match (_61_567) with
| (env, free) -> begin
(

let _61_571 = (free_type_vars_b env binder)
in (match (_61_571) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_61_574) with
| (env, free) -> begin
(let _153_110 = (free_type_vars env body)
in (FStar_List.append free _153_110))
end))
end
| FStar_Parser_AST.Project (t, _61_577) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _153_117 = (unparen t)
in _153_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _61_624 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _153_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _153_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _153_126 = (let _153_125 = (let _153_124 = (kind_star x.FStar_Ident.idRange)
in ((x), (_153_124)))
in FStar_Parser_AST.TAnnotated (_153_125))
in (FStar_Parser_AST.mk_binder _153_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _153_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _153_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _153_135 = (let _153_134 = (let _153_133 = (kind_star x.FStar_Ident.idRange)
in ((x), (_153_133)))
in FStar_Parser_AST.TAnnotated (_153_134))
in (FStar_Parser_AST.mk_binder _153_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _153_136 = (unlabel t)
in _153_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_61_637) -> begin
t
end
| _61_640 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))


let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _61_650 -> begin
((bs), (t))
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _61_654) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_61_660); FStar_Parser_AST.prange = _61_658}, _61_664) -> begin
true
end
| _61_668 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _61_680 = (destruct_app_pattern env is_top_level p)
in (match (_61_680) with
| (name, args, _61_679) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_685); FStar_Parser_AST.prange = _61_682}, args) when is_top_level -> begin
(let _153_150 = (let _153_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_153_149))
in ((_153_150), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_696); FStar_Parser_AST.prange = _61_693}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _61_704 -> begin
(FStar_All.failwith "Not an app pattern")
end))


type bnd =
| TBinder of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual)
| VBinder of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)


let is_TBinder = (fun _discr_ -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))


let is_VBinder = (fun _discr_ -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))


let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))


let ___TBinder____0 = (fun projectee -> (match (projectee) with
| TBinder (_61_707) -> begin
_61_707
end))


let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_61_710) -> begin
_61_710
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_61_713) -> begin
_61_713
end))


let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _61_3 -> (match (_61_3) with
| TBinder (a, k, aq) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), (aq))
end
| VBinder (x, t, aq) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (aq))
end
| _61_726 -> begin
(FStar_All.failwith "Impossible")
end))


let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _61_4 -> (match (_61_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _61_733 -> begin
None
end))


let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either  ->  (FStar_Absyn_Syntax.binder * FStar_Parser_DesugarEnv.env) = (fun env imp _61_5 -> (match (_61_5) with
| FStar_Util.Inl (None, k) -> begin
(let _153_203 = (FStar_Absyn_Syntax.null_t_binder k)
in ((_153_203), (env)))
end
| FStar_Util.Inr (None, t) -> begin
(let _153_204 = (FStar_Absyn_Syntax.null_v_binder t)
in ((_153_204), (env)))
end
| FStar_Util.Inl (Some (a), k) -> begin
(

let _61_752 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_752) with
| (env, a) -> begin
((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual imp)))), (env))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _61_760 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_760) with
| (env, x) -> begin
((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_Parser_DesugarEnv.env


type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list


let label_conjuncts : Prims.string  ->  Prims.bool  ->  Prims.string Prims.option  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun tag polarity label_opt f -> (

let label = (fun f -> (

let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _61_770 -> begin
(let _153_215 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _153_215))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (((f), (msg), (polarity)))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (

let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _153_219 = (let _153_218 = (aux g)
in FStar_Parser_AST.Paren (_153_218))
in (FStar_Parser_AST.mk_term _153_219 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", (f1)::(f2)::[]) -> begin
(let _153_225 = (let _153_224 = (let _153_223 = (let _153_222 = (aux f1)
in (let _153_221 = (let _153_220 = (aux f2)
in (_153_220)::[])
in (_153_222)::_153_221))
in (("/\\"), (_153_223)))
in FStar_Parser_AST.Op (_153_224))
in (FStar_Parser_AST.mk_term _153_225 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _153_229 = (let _153_228 = (let _153_227 = (aux f2)
in (let _153_226 = (aux f3)
in ((f1), (_153_227), (_153_226))))
in FStar_Parser_AST.If (_153_228))
in (FStar_Parser_AST.mk_term _153_229 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _153_232 = (let _153_231 = (let _153_230 = (aux g)
in ((binders), (_153_230)))
in FStar_Parser_AST.Abs (_153_231))
in (FStar_Parser_AST.mk_term _153_232 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _61_792 -> begin
(label f)
end))
in (aux f))))


let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _61_796 -> (match (_61_796) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))


let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _61_6 -> (match (_61_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _61_807 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
((l), (e), (y))
end
| _61_812 -> begin
(

let _61_815 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_61_815) with
| (e, x) -> begin
(((FStar_Util.Inr (x))::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _61_7 -> (match (_61_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _61_824 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
((l), (e), (b))
end
| _61_829 -> begin
(

let _61_832 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_61_832) with
| (e, a) -> begin
(((FStar_Util.Inl (a))::l), (e), (a))
end))
end))
in (

let rec aux = (fun loc env p -> (

let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Absyn_Syntax.withinfo q None r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _61_854 = (aux loc env p)
in (match (_61_854) with
| (loc, env, var, p, _61_853) -> begin
(

let _61_871 = (FStar_List.fold_left (fun _61_858 p -> (match (_61_858) with
| (loc, env, ps) -> begin
(

let _61_867 = (aux loc env p)
in (match (_61_867) with
| (loc, env, _61_863, p, _61_866) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_61_871) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (

let _61_873 = (let _153_304 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _153_304))
in ((loc), (env), (var), (pat), (false))))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_61_880) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(

let _61_886 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (((x), (imp))); FStar_Parser_AST.prange = _61_886.FStar_Parser_AST.prange})
end
| _61_889 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
p
end
in (

let _61_896 = (aux loc env p)
in (match (_61_896) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_61_898) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _61_902, aq) -> begin
(let _153_306 = (let _153_305 = (desugar_kind env t)
in ((x), (_153_305), (aq)))
in TBinder (_153_306))
end
| VBinder (x, _61_908, aq) -> begin
(

let t = (close_fun env t)
in (let _153_308 = (let _153_307 = (desugar_typ env t)
in ((x), (_153_307), (aq)))
in VBinder (_153_308)))
end)
in ((loc), (env'), (binder), (p), (imp)))
end)))
end
| FStar_Parser_AST.PatTvar (a, aq) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in if (a.FStar_Ident.idText = "\'_") then begin
(

let a = (FStar_All.pipe_left FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((a), (FStar_Absyn_Syntax.kun), (aq)))), (_153_309), (imp))))
end else begin
(

let _61_924 = (resolvea loc env a)
in (match (_61_924) with
| (loc, env, abvd) -> begin
(let _153_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((abvd), (FStar_Absyn_Syntax.kun), (aq)))), (_153_310), (imp)))
end))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (

let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_311), (false)))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_312), (false))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _61_940 = (resolvex loc env x)
in (match (_61_940) with
| (loc, env, xbvd) -> begin
(let _153_313 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((xbvd), (FStar_Absyn_Syntax.tun), (aq)))), (_153_313), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_314 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), ([])))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_314), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _61_946}, args) -> begin
(

let _61_968 = (FStar_List.fold_right (fun arg _61_957 -> (match (_61_957) with
| (loc, env, args) -> begin
(

let _61_964 = (aux loc env arg)
in (match (_61_964) with
| (loc, env, _61_961, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_61_968) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_317 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_317), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_61_972) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _61_992 = (FStar_List.fold_right (fun pat _61_980 -> (match (_61_980) with
| (loc, env, pats) -> begin
(

let _61_988 = (aux loc env pat)
in (match (_61_988) with
| (loc, env, _61_984, pat, _61_987) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_61_992) with
| (loc, env, pats) -> begin
(

let pat = (let _153_324 = (let _153_323 = (let _153_322 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _153_322))
in (FStar_All.pipe_left _153_323 (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ([]))))))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((hd), (false)))::(((tl), (false)))::[]))))))) pats _153_324))
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _61_1018 = (FStar_List.fold_left (fun _61_1005 p -> (match (_61_1005) with
| (loc, env, pats) -> begin
(

let _61_1014 = (aux loc env p)
in (match (_61_1014) with
| (loc, env, _61_1010, pat, _61_1013) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_61_1018) with
| (loc, env, args) -> begin
(

let args = (FStar_List.rev args)
in (

let l = if dep then begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (

let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (

let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _61_1024) -> begin
v
end
| _61_1028 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_327 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_327), (false))))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _61_1038 = (FStar_List.hd fields)
in (match (_61_1038) with
| (f, _61_1037) -> begin
(

let _61_1042 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_61_1042) with
| (record, _61_1041) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _61_1045 -> (match (_61_1045) with
| (f, p) -> begin
(let _153_329 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in ((_153_329), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _61_1050 -> (match (_61_1050) with
| (f, _61_1049) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _61_1054 -> (match (_61_1054) with
| (g, _61_1053) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_61_1057, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _61_1069 = (aux loc env app)
in (match (_61_1069) with
| (env, e, b, p, _61_1068) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _61_1072, args) -> begin
(let _153_337 = (let _153_336 = (let _153_335 = (let _153_334 = (let _153_333 = (let _153_332 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_153_332)))
in FStar_Absyn_Syntax.Record_ctor (_153_333))
in Some (_153_334))
in ((fv), (_153_335), (args)))
in FStar_Absyn_Syntax.Pat_cons (_153_336))
in (FStar_All.pipe_left pos _153_337))
end
| _61_1077 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _61_1086 = (aux [] env p)
in (match (_61_1086) with
| (_61_1080, env, b, p, _61_1085) -> begin
((env), (b), (p))
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _61_1092) -> begin
(let _153_343 = (let _153_342 = (let _153_341 = (FStar_Parser_DesugarEnv.qualify env x)
in ((_153_341), (FStar_Absyn_Syntax.tun)))
in LetBinder (_153_342))
in ((env), (_153_343), (None)))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _61_1099); FStar_Parser_AST.prange = _61_1096}, t) -> begin
(let _153_347 = (let _153_346 = (let _153_345 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _153_344 = (desugar_typ env t)
in ((_153_345), (_153_344))))
in LetBinder (_153_346))
in ((env), (_153_347), (None)))
end
| _61_1107 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _61_1111 = (desugar_data_pat env p)
in (match (_61_1111) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _61_1122 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _61_1126 env pat -> (

let _61_1134 = (desugar_data_pat env pat)
in (match (_61_1134) with
| (env, _61_1132, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _153_357 = (desugar_typ env t)
in FStar_Util.Inl (_153_357))
end else begin
(let _153_358 = (desugar_exp env t)
in FStar_Util.Inr (_153_358))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (

let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _61_1148 = e
in {FStar_Absyn_Syntax.n = _61_1148.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1148.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1148.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1148.FStar_Absyn_Syntax.uvs}))
in (match ((let _153_378 = (unparen top)
in _153_378.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (c) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_constant c))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_vlid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Unexpected operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (l) -> begin
(

let op = (FStar_Absyn_Util.fvar None l (FStar_Ident.range_of_lid l))
in (

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _153_382 = (desugar_typ_or_exp env t)
in ((_153_382), (None))))))
in (let _153_383 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _153_383))))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
if (l.FStar_Ident.str = "ref") then begin
(match ((FStar_Parser_DesugarEnv.try_lookup_lid env FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Identifier \'ref\' not found; include lib/FStar.ST.fst in your path"), ((FStar_Ident.range_of_lid l))))))
end
| Some (e) -> begin
(setpos e)
end)
end else begin
(let _153_384 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _153_384))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let dt = (let _153_389 = (let _153_388 = (let _153_387 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in ((_153_387), (Some (FStar_Absyn_Syntax.Data_ctor))))
in (FStar_Absyn_Syntax.mk_Exp_fvar _153_388))
in (FStar_All.pipe_left pos _153_389))
in (match (args) with
| [] -> begin
dt
end
| _61_1175 -> begin
(

let args = (FStar_List.map (fun _61_1178 -> (match (_61_1178) with
| (t, imp) -> begin
(

let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _153_394 = (let _153_393 = (let _153_392 = (let _153_391 = (FStar_Absyn_Util.mk_exp_app dt args)
in ((_153_391), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_153_392))
in (FStar_Absyn_Syntax.mk_Exp_meta _153_393))
in (FStar_All.pipe_left setpos _153_394)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _61_1215 = (FStar_List.fold_left (fun _61_1187 pat -> (match (_61_1187) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _61_1190}, t) -> begin
(

let ftvs = (let _153_397 = (free_type_vars env t)
in (FStar_List.append _153_397 ftvs))
in (let _153_399 = (let _153_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _153_398))
in ((_153_399), (ftvs))))
end
| FStar_Parser_AST.PatTvar (a, _61_1202) -> begin
(let _153_401 = (let _153_400 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _153_400))
in ((_153_401), (ftvs)))
end
| FStar_Parser_AST.PatAscribed (_61_1206, t) -> begin
(let _153_403 = (let _153_402 = (free_type_vars env t)
in (FStar_List.append _153_402 ftvs))
in ((env), (_153_403)))
end
| _61_1211 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_61_1215) with
| (_61_1213, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _153_405 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _153_405 binders))
in (

let rec aux = (fun env bs sc_pat_opt _61_8 -> (match (_61_8) with
| [] -> begin
(

let body = (desugar_exp env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(FStar_Absyn_Syntax.mk_Exp_match ((sc), ((((pat), (None), (body)))::[])) None body.FStar_Absyn_Syntax.pos)
end
| None -> begin
body
end)
in (FStar_Absyn_Syntax.mk_Exp_abs' (((FStar_List.rev bs)), (body)) None top.FStar_Parser_AST.range)))
end
| (p)::rest -> begin
(

let _61_1238 = (desugar_binding_pat env p)
in (match (_61_1238) with
| (env, b, pat) -> begin
(

let _61_1298 = (match (b) with
| LetBinder (_61_1240) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _153_414 = (binder_of_bnd b)
in ((_153_414), (sc_pat_opt)))
end
| VBinder (x, t, aq) -> begin
(

let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _61_1255) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _153_416 = (let _153_415 = (FStar_Absyn_Util.bvar_to_exp b)
in ((_153_415), (p)))
in Some (_153_416))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Absyn_Syntax.n), (p'.FStar_Absyn_Syntax.v))) with
| (FStar_Absyn_Syntax.Exp_bvar (_61_1269), _61_1272) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (

let sc = (let _153_423 = (let _153_422 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _153_421 = (let _153_420 = (FStar_Absyn_Syntax.varg sc)
in (let _153_419 = (let _153_418 = (let _153_417 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _153_417))
in (_153_418)::[])
in (_153_420)::_153_419))
in ((_153_422), (_153_421))))
in (FStar_Absyn_Syntax.mk_Exp_app _153_423 None top.FStar_Parser_AST.range))
in (

let p = (let _153_424 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((p'), (false)))::(((p), (false)))::[])))) None _153_424))
in Some (((sc), (p))))))
end
| (FStar_Absyn_Syntax.Exp_app (_61_1278, args), FStar_Absyn_Syntax.Pat_cons (_61_1283, _61_1285, pats)) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (

let sc = (let _153_430 = (let _153_429 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _153_428 = (let _153_427 = (let _153_426 = (let _153_425 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _153_425))
in (_153_426)::[])
in (FStar_List.append args _153_427))
in ((_153_429), (_153_428))))
in (FStar_Absyn_Syntax.mk_Exp_app _153_430 None top.FStar_Parser_AST.range))
in (

let p = (let _153_431 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((FStar_List.append pats ((((p), (false)))::[])))))) None _153_431))
in Some (((sc), (p))))))
end
| _61_1294 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((FStar_Util.Inr (b)), (aq))), (sc_pat_opt))))
end)
in (match (_61_1298) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _61_1302; FStar_Parser_AST.level = _61_1300}, arg, _61_1308) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env arg)
in (let _153_441 = (let _153_440 = (let _153_439 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _153_438 = (let _153_437 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _153_436 = (let _153_435 = (let _153_434 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _153_434))
in (_153_435)::[])
in (_153_437)::_153_436))
in ((_153_439), (_153_438))))
in (FStar_Absyn_Syntax.mk_Exp_app _153_440))
in (FStar_All.pipe_left pos _153_441)))
end
| FStar_Parser_AST.App (_61_1313) -> begin
(

let rec aux = (fun args e -> (match ((let _153_446 = (unparen e)
in _153_446.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _153_447 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _153_447))
in (aux ((arg)::args) e))
end
| _61_1325 -> begin
(

let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app ((head), (args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _153_453 = (let _153_452 = (let _153_451 = (let _153_450 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_153_450), (FStar_Absyn_Syntax.Sequence)))
in FStar_Absyn_Syntax.Meta_desugared (_153_451))
in (FStar_Absyn_Syntax.mk_Exp_meta _153_452))
in (FStar_All.pipe_left setpos _153_453))
end
| FStar_Parser_AST.Let (is_rec, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (is_rec = FStar_Parser_AST.Rec)
in (

let ds_let_rec = (fun _61_1342 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _61_1346 -> (match (_61_1346) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _153_457 = (destruct_app_pattern env top_level p)
in ((_153_457), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _153_458 = (destruct_app_pattern env top_level p)
in ((_153_458), (def)))
end
| _61_1352 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_1357); FStar_Parser_AST.prange = _61_1354}, t) -> begin
if top_level then begin
(let _153_461 = (let _153_460 = (let _153_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_153_459))
in ((_153_460), ([]), (Some (t))))
in ((_153_461), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _61_1366) -> begin
if top_level then begin
(let _153_464 = (let _153_463 = (let _153_462 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_153_462))
in ((_153_463), ([]), (None)))
in ((_153_464), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _61_1370 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _61_1396 = (FStar_List.fold_left (fun _61_1374 _61_1383 -> (match (((_61_1374), (_61_1383))) with
| ((env, fnames), ((f, _61_1377, _61_1379), _61_1382)) -> begin
(

let _61_1393 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _61_1388 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_1388) with
| (env, xx) -> begin
((env), (FStar_Util.Inl (xx)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _153_467 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in ((_153_467), (FStar_Util.Inr (l))))
end)
in (match (_61_1393) with
| (env, lbname) -> begin
((env), ((lbname)::fnames))
end))
end)) ((env), ([])) funs)
in (match (_61_1396) with
| (env', fnames) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _61_1407 -> (match (_61_1407) with
| ((_61_1402, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _153_474 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _153_474 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _61_1414 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (

let body = (desugar_exp env def)
in (mk_lb ((lbname), (FStar_Absyn_Syntax.tun), (body))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (

let body = (desugar_exp env' body)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs))), (body))))))))
end))))
end))
in (

let ds_non_rec = (fun pat t1 t2 -> (

let t1 = (desugar_exp env t1)
in (

let _61_1427 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_61_1427) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_61_1429) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(

let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]))), (body)))))
end
| VBinder (x, t, _61_1439) -> begin
(

let body = (desugar_exp env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _153_486 = (let _153_485 = (FStar_Absyn_Util.bvd_to_exp x t)
in ((_153_485), ((((pat), (None), (body)))::[])))
in (FStar_Absyn_Syntax.mk_Exp_match _153_486 None body.FStar_Absyn_Syntax.pos))
end)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((false), (((mk_lb ((FStar_Util.Inl (x)), (t), (t1))))::[]))), (body))))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec ())
end else begin
(ds_non_rec pat _snd body)
end)))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _153_499 = (let _153_498 = (let _153_497 = (desugar_exp env t1)
in (let _153_496 = (let _153_495 = (let _153_491 = (desugar_exp env t2)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range)), (None), (_153_491)))
in (let _153_494 = (let _153_493 = (let _153_492 = (desugar_exp env t3)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range)), (None), (_153_492)))
in (_153_493)::[])
in (_153_495)::_153_494))
in ((_153_497), (_153_496))))
in (FStar_Absyn_Syntax.mk_Exp_match _153_498))
in (FStar_All.pipe_left pos _153_499))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let r = top.FStar_Parser_AST.range
in (

let handler = (FStar_Parser_AST.mk_function branches r r)
in (

let body = (FStar_Parser_AST.mk_function (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r)), (None), (e)))::[]) r r)
in (

let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Absyn_Const.try_with_lid)) r top.FStar_Parser_AST.level)), (body), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (

let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((a1), (handler), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let desugar_branch = (fun _61_1478 -> (match (_61_1478) with
| (pat, wopt, b) -> begin
(

let _61_1481 = (desugar_match_pat env pat)
in (match (_61_1481) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _153_502 = (desugar_exp env e)
in Some (_153_502))
end)
in (

let b = (desugar_exp env b)
in ((pat), (wopt), (b))))
end))
end))
in (let _153_508 = (let _153_507 = (let _153_506 = (desugar_exp env e)
in (let _153_505 = (FStar_List.map desugar_branch branches)
in ((_153_506), (_153_505))))
in (FStar_Absyn_Syntax.mk_Exp_match _153_507))
in (FStar_All.pipe_left pos _153_508)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _153_514 = (let _153_513 = (let _153_512 = (desugar_exp env e)
in (let _153_511 = (desugar_typ env t)
in ((_153_512), (_153_511), (None))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _153_513))
in (FStar_All.pipe_left pos _153_514))
end
| FStar_Parser_AST.Record (_61_1492, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _61_1503 = (FStar_List.hd fields)
in (match (_61_1503) with
| (f, _61_1502) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _61_1509 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_61_1509) with
| (record, _61_1508) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _61_1517 -> (match (_61_1517) with
| (g, _61_1516) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_61_1521, e) -> begin
(let _153_522 = (qfn fn)
in ((_153_522), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _153_525 = (let _153_524 = (let _153_523 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_153_523), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_153_524))
in (Prims.raise _153_525))
end
| Some (x) -> begin
(let _153_526 = (qfn fn)
in ((_153_526), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _153_531 = (let _153_530 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _61_1533 -> (match (_61_1533) with
| (f, _61_1532) -> begin
(let _153_529 = (let _153_528 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _153_528))
in ((_153_529), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_DesugarEnv.constrname), (_153_530)))
in FStar_Parser_AST.Construct (_153_531))
end
| Some (e) -> begin
(

let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (

let xterm = (let _153_533 = (let _153_532 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_153_532))
in (FStar_Parser_AST.mk_term _153_533 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _153_536 = (let _153_535 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _61_1541 -> (match (_61_1541) with
| (f, _61_1540) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_153_535)))
in FStar_Parser_AST.Record (_153_536))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _61_1564); FStar_Absyn_Syntax.tk = _61_1561; FStar_Absyn_Syntax.pos = _61_1559; FStar_Absyn_Syntax.fvs = _61_1557; FStar_Absyn_Syntax.uvs = _61_1555}, args); FStar_Absyn_Syntax.tk = _61_1553; FStar_Absyn_Syntax.pos = _61_1551; FStar_Absyn_Syntax.fvs = _61_1549; FStar_Absyn_Syntax.uvs = _61_1547}, FStar_Absyn_Syntax.Data_app)) -> begin
(

let e = (let _153_546 = (let _153_545 = (let _153_544 = (let _153_543 = (let _153_542 = (let _153_541 = (let _153_540 = (let _153_539 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_153_539)))
in FStar_Absyn_Syntax.Record_ctor (_153_540))
in Some (_153_541))
in ((fv), (_153_542)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _153_543 None e.FStar_Absyn_Syntax.pos))
in ((_153_544), (args)))
in (FStar_Absyn_Syntax.mk_Exp_app _153_545))
in (FStar_All.pipe_left pos _153_546))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (FStar_Absyn_Syntax.Data_app))))))
end
| _61_1578 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _61_1585 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_61_1585) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_exp env e)
in (

let fn = (

let _61_1590 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_61_1590) with
| (ns, _61_1589) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _153_553 = (let _153_552 = (let _153_551 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (let _153_550 = (let _153_549 = (FStar_Absyn_Syntax.varg e)
in (_153_549)::[])
in ((_153_551), (_153_550))))
in (FStar_Absyn_Syntax.mk_Exp_app _153_552))
in (FStar_All.pipe_left pos _153_553)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _61_1596 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (

let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _61_1603 = t
in {FStar_Absyn_Syntax.n = _61_1603.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1603.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1603.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1603.FStar_Absyn_Syntax.uvs}))
in (

let top = (unparen top)
in (

let head_and_args = (fun t -> (

let rec aux = (fun args t -> (match ((let _153_576 = (unparen t)
in _153_576.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _61_1621 -> begin
((t), (args))
end))
in (aux [] t)))
in (match (top.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.tun)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(

let t = (label_conjuncts "pre-condition" true lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _153_577 = (desugar_exp env t)
in (FStar_All.pipe_right _153_577 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _153_578 = (desugar_exp env t)
in (FStar_All.pipe_right _153_578 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", (t1)::(_61_1635)::[]) -> begin
if (is_type env t1) then begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(

let rest = (flatten t2)
in (t1)::rest)
end
| _61_1650 -> begin
(t)::[]
end))
in (

let targs = (let _153_583 = (flatten top)
in (FStar_All.pipe_right _153_583 (FStar_List.map (fun t -> (let _153_582 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _153_582))))))
in (

let tup = (let _153_584 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _153_584))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))))
end else begin
(let _153_590 = (let _153_589 = (let _153_588 = (let _153_587 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _153_587))
in ((_153_588), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_153_589))
in (Prims.raise _153_590))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _153_591 = (desugar_exp env top)
in (FStar_All.pipe_right _153_591 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(

let args = (FStar_List.map (fun t -> (let _153_593 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _153_593))) args)
in (let _153_594 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _153_594 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _153_595 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _153_595))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _153_596 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _153_596))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _153_597 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _153_597)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let t = (let _153_598 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _153_598))
in (

let args = (FStar_List.map (fun _61_1686 -> (match (_61_1686) with
| (t, imp) -> begin
(let _153_600 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _153_600))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let rec aux = (fun env bs _61_9 -> (match (_61_9) with
| [] -> begin
(

let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_List.rev bs)), (body)))))
end
| (hd)::tl -> begin
(

let _61_1704 = (desugar_binding_pat env hd)
in (match (_61_1704) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _153_612 = (let _153_611 = (let _153_610 = (let _153_609 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _153_609))
in ((_153_610), (hd.FStar_Parser_AST.prange)))
in FStar_Absyn_Syntax.Error (_153_611))
in (Prims.raise _153_612))
end
| None -> begin
(

let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_61_1710) -> begin
(

let rec aux = (fun args e -> (match ((let _153_617 = (unparen e)
in _153_617.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(

let arg = (let _153_618 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _153_618))
in (aux ((arg)::args) e))
end
| _61_1722 -> begin
(

let head = (desugar_typ env e)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((head), (args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Product ([], t) -> begin
(FStar_All.failwith "Impossible: product with no binders")
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _61_1734 = (uncurry binders t)
in (match (_61_1734) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _61_10 -> (match (_61_10) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun (((FStar_List.rev bs)), (cod)))))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _61_1748 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_61_1748) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _61_1755) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _61_1769 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _61_1761), env) -> begin
((x), (env))
end
| _61_1766 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_61_1769) with
| (b, env) -> begin
(

let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _153_629 = (desugar_exp env f)
in (FStar_All.pipe_right _153_629 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine ((b), (f)))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _153_637 = (let _153_636 = (let _153_635 = (desugar_typ env t)
in (let _153_634 = (desugar_kind env k)
in ((_153_635), (_153_634))))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _153_636))
in (FStar_All.pipe_left wpos _153_637))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _61_1803 = (FStar_List.fold_left (fun _61_1788 b -> (match (_61_1788) with
| (env, tparams, typs) -> begin
(

let _61_1792 = (desugar_exp_binder env b)
in (match (_61_1792) with
| (xopt, t) -> begin
(

let _61_1798 = (match (xopt) with
| None -> begin
(let _153_640 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in ((env), (_153_640)))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_61_1798) with
| (env, x) -> begin
(let _153_644 = (let _153_643 = (let _153_642 = (let _153_641 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _153_641))
in (_153_642)::[])
in (FStar_List.append typs _153_643))
in ((env), ((FStar_List.append tparams ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (None)))::[]))), (_153_644)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_61_1803) with
| (env, _61_1801, targs) -> begin
(

let tup = (let _153_645 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _153_645))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))
end))
end
| FStar_Parser_AST.Record (_61_1806) -> begin
(FStar_All.failwith "Unexpected record type")
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, ((x, v))::[], t) -> begin
(

let let_v = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.let_in_typ)) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)), (v), (FStar_Parser_AST.Nothing)))) v.FStar_Parser_AST.range v.FStar_Parser_AST.level)
in (

let t' = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((let_v), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ((((x)::[]), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (FStar_Parser_AST.Nothing)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_typ env t')))
end
| (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _61_1825 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _61_1827 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r))))))
in (

let pre_process_comp_typ = (fun t -> (

let _61_1838 = (head_and_args t)
in (match (_61_1838) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let _61_1864 = (FStar_All.pipe_right args (FStar_List.partition (fun _61_1846 -> (match (_61_1846) with
| (arg, _61_1845) -> begin
(match ((let _153_657 = (unparen arg)
in _153_657.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _61_1850; FStar_Parser_AST.level = _61_1848}, _61_1855, _61_1857) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _61_1861 -> begin
false
end)
end))))
in (match (_61_1864) with
| (decreases_clause, args) -> begin
(

let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Not enough arguments to \'Lemma\'"), (t.FStar_Parser_AST.range)))))
end
| (ens)::[] -> begin
(

let req_true = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (None)))) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (unit)::(req_true)::(ens)::(nil_pat)::[])
end
| (req)::(ens)::[] -> begin
(unit)::(req)::(ens)::(nil_pat)::[]
end
| more -> begin
(unit)::more
end)
in (

let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((lemma), ((FStar_List.append args decreases_clause))))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _153_658 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _153_658 FStar_Absyn_Const.prims_lid))) -> begin
(

let args = (FStar_List.map (fun _61_1879 -> (match (_61_1879) with
| (t, imp) -> begin
(let _153_660 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _153_660))
end)) args)
in (let _153_661 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _153_661 args)))
end
| _61_1882 -> begin
(desugar_typ env t)
end)
end)))
in (

let t = (pre_process_comp_typ t)
in (

let _61_1886 = (FStar_Absyn_Util.head_and_args t)
in (match (_61_1886) with
| (head, args) -> begin
(match ((let _153_663 = (let _153_662 = (FStar_Absyn_Util.compress_typ head)
in _153_662.FStar_Absyn_Syntax.n)
in ((_153_663), (args)))) with
| (FStar_Absyn_Syntax.Typ_const (eff), ((FStar_Util.Inl (result_typ), _61_1893))::rest) -> begin
(

let _61_1933 = (FStar_All.pipe_right rest (FStar_List.partition (fun _61_11 -> (match (_61_11) with
| (FStar_Util.Inr (_61_1899), _61_1902) -> begin
false
end
| (FStar_Util.Inl (t), _61_1907) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _61_1916; FStar_Absyn_Syntax.pos = _61_1914; FStar_Absyn_Syntax.fvs = _61_1912; FStar_Absyn_Syntax.uvs = _61_1910}, ((FStar_Util.Inr (_61_1921), _61_1924))::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _61_1930 -> begin
false
end)
end))))
in (match (_61_1933) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _61_12 -> (match (_61_12) with
| (FStar_Util.Inl (t), _61_1938) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_61_1941, ((FStar_Util.Inr (arg), _61_1945))::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _61_1951 -> begin
(FStar_All.failwith "impos")
end)
end
| _61_1953 -> begin
(FStar_All.failwith "impos")
end))))
in if ((FStar_Parser_DesugarEnv.is_effect_name env eff.FStar_Absyn_Syntax.v) || (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid)) then begin
if ((FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Absyn_Syntax.mk_Total result_typ)
end else begin
(

let flags = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(FStar_Absyn_Syntax.LEMMA)::[]
end else begin
if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) then begin
(FStar_Absyn_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_ML_lid) then begin
(FStar_Absyn_Syntax.MLEFFECT)::[]
end else begin
[]
end
end
end
in (

let rest = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(match (rest) with
| (req)::(ens)::((FStar_Util.Inr (pat), aq))::[] -> begin
(let _153_670 = (let _153_669 = (let _153_668 = (let _153_667 = (let _153_666 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((pat), (FStar_Absyn_Syntax.Meta_smt_pat)))))
in FStar_Util.Inr (_153_666))
in ((_153_667), (aq)))
in (_153_668)::[])
in (ens)::_153_669)
in (req)::_153_670)
end
| _61_1964 -> begin
rest
end)
end else begin
rest
end
in (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = eff.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.result_typ = result_typ; FStar_Absyn_Syntax.effect_args = rest; FStar_Absyn_Syntax.flags = (FStar_List.append flags decreases_clause)})))
end
end else begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _153_672 = (let _153_671 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _153_671))
in (fail _153_672))
end
end)
end))
end
| _61_1967 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _153_674 = (let _153_673 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _153_673))
in (fail _153_674))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (

let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (

let setpos = (fun kk -> (

let _61_1974 = kk
in {FStar_Absyn_Syntax.n = _61_1974.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1974.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1974.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1974.FStar_Absyn_Syntax.uvs}))
in (

let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _61_1983; FStar_Ident.ident = _61_1981; FStar_Ident.nsstr = _61_1979; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _61_1992; FStar_Ident.ident = _61_1990; FStar_Ident.nsstr = _61_1988; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _153_686 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _153_686))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), ([]))), (FStar_Absyn_Syntax.mk_Kind_unknown))))
end
| _61_2000 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(

let _61_2008 = (uncurry bs k)
in (match (_61_2008) with
| (bs, k) -> begin
(

let rec aux = (fun env bs _61_13 -> (match (_61_13) with
| [] -> begin
(let _153_697 = (let _153_696 = (let _153_695 = (desugar_kind env k)
in (((FStar_List.rev bs)), (_153_695)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _153_696))
in (FStar_All.pipe_left pos _153_697))
end
| (hd)::tl -> begin
(

let _61_2019 = (let _153_699 = (let _153_698 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _153_698 hd))
in (FStar_All.pipe_right _153_699 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_61_2019) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_DesugarEnv.find_kind_abbrev env l)) with
| None -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end
| Some (l) -> begin
(

let args = (FStar_List.map (fun _61_2029 -> (match (_61_2029) with
| (t, b) -> begin
(

let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _153_701 = (desugar_typ_or_exp env t)
in ((_153_701), (qual))))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (FStar_Absyn_Syntax.mk_Kind_unknown)))))
end)
end
| _61_2033 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env f -> (

let connective = (fun s -> (match (s) with
| "/\\" -> begin
Some (FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
Some (FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
Some (FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
Some (FStar_Absyn_Const.iff_lid)
end
| "~" -> begin
Some (FStar_Absyn_Const.not_lid)
end
| _61_2044 -> begin
None
end))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _61_2049 = t
in {FStar_Absyn_Syntax.n = _61_2049.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_2049.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_2049.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_2049.FStar_Absyn_Syntax.uvs}))
in (

let desugar_quant = (fun q qt b pats body -> (

let tk = (desugar_binder env (

let _61_2057 = b
in {FStar_Parser_AST.b = _61_2057.FStar_Parser_AST.b; FStar_Parser_AST.brange = _61_2057.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _61_2057.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _153_737 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _153_737)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _61_2072 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2072) with
| (env, a) -> begin
(

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _61_2077 -> begin
(let _153_738 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
in (FStar_All.pipe_left setpos _153_738))
end)
in (

let body = (let _153_744 = (let _153_743 = (let _153_742 = (let _153_741 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_153_741)::[])
in ((_153_742), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _153_743))
in (FStar_All.pipe_left pos _153_744))
in (let _153_749 = (let _153_748 = (let _153_745 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _153_745 FStar_Absyn_Syntax.kun))
in (let _153_747 = (let _153_746 = (FStar_Absyn_Syntax.targ body)
in (_153_746)::[])
in (FStar_Absyn_Util.mk_typ_app _153_748 _153_747)))
in (FStar_All.pipe_left setpos _153_749))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _61_2087 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_2087) with
| (env, x) -> begin
(

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _61_2092 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
end)
in (

let body = (let _153_755 = (let _153_754 = (let _153_753 = (let _153_752 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_153_752)::[])
in ((_153_753), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _153_754))
in (FStar_All.pipe_left pos _153_755))
in (let _153_760 = (let _153_759 = (let _153_756 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _153_756 FStar_Absyn_Syntax.kun))
in (let _153_758 = (let _153_757 = (FStar_Absyn_Syntax.targ body)
in (_153_757)::[])
in (FStar_Absyn_Util.mk_typ_app _153_759 _153_758)))
in (FStar_All.pipe_left setpos _153_760))))))
end))
end
| _61_2096 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _153_775 = (q ((rest), (pats), (body)))
in (let _153_774 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _153_775 _153_774 FStar_Parser_AST.Formula)))
in (let _153_776 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _153_776 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _61_2110 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _153_777 = (unparen f)
in _153_777.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (l), (FStar_Absyn_Syntax.dummyRange), (p))))))
end
| FStar_Parser_AST.Op ("==", (hd)::_args) -> begin
(

let args = (hd)::_args
in (

let args = (FStar_List.map (fun t -> (let _153_779 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _153_779))) args)
in (

let eq = if (is_type env hd) then begin
(let _153_780 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _153_780 FStar_Absyn_Syntax.kun))
end else begin
(let _153_781 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _153_781 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((((connective s)), (args))) with
| (Some (conn), (_61_2136)::(_61_2134)::[]) -> begin
(let _153_786 = (let _153_782 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _153_782 FStar_Absyn_Syntax.kun))
in (let _153_785 = (FStar_List.map (fun x -> (let _153_784 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _153_784))) args)
in (FStar_Absyn_Util.mk_typ_app _153_786 _153_785)))
end
| _61_2141 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _153_787 = (desugar_exp env f)
in (FStar_All.pipe_right _153_787 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _153_792 = (let _153_788 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _153_788 FStar_Absyn_Syntax.kun))
in (let _153_791 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _153_790 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _153_790))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _153_792 _153_791)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _153_794 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _153_794)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _153_796 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _153_796)))
end
| FStar_Parser_AST.QForall ((b)::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.forall_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.QExists ((b)::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.exists_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _61_2203 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _153_797 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _153_797))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (

let _61_2206 = env
in {FStar_Parser_DesugarEnv.curmodule = _61_2206.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _61_2206.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _61_2206.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _61_2206.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _61_2206.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _61_2206.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _61_2206.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _61_2206.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _61_2206.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _61_2206.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _61_2206.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _153_802 = (desugar_type_binder env b)
in FStar_Util.Inl (_153_802))
end else begin
(let _153_803 = (desugar_exp_binder env b)
in FStar_Util.Inr (_153_803))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _61_2239 = (FStar_List.fold_left (fun _61_2214 b -> (match (_61_2214) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _61_2216 = b
in {FStar_Parser_AST.b = _61_2216.FStar_Parser_AST.b; FStar_Parser_AST.brange = _61_2216.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _61_2216.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _61_2226 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2226) with
| (env, a) -> begin
((env), ((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _61_2234 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_2234) with
| (env, x) -> begin
((env), ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| _61_2236 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_61_2239) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _153_810 = (desugar_typ env t)
in ((Some (x)), (_153_810)))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _153_811 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in ((None), (_153_811)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _153_812 = (desugar_typ env t)
in ((None), (_153_812)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Absyn_Syntax.tun))
end
| _61_2253 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a type)"), (b.FStar_Parser_AST.brange)))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (

let fail = (fun _61_2257 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a kind)"), (b.FStar_Parser_AST.brange)))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _153_817 = (desugar_kind env t)
in ((Some (x)), (_153_817)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _153_818 = (desugar_kind env t)
in ((None), (_153_818)))
end
| FStar_Parser_AST.TVariable (x) -> begin
((Some (x)), ((

let _61_2268 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _61_2268.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_2268.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _61_2268.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_2268.FStar_Absyn_Syntax.uvs})))
end
| _61_2271 -> begin
(fail ())
end)))


let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (

let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_61_2282, k) -> begin
(aux bs k)
end
| _61_2287 -> begin
bs
end))
in (let _153_827 = (aux tps k)
in (FStar_All.pipe_right _153_827 FStar_Absyn_Util.name_binders))))


let mk_data_discriminators : FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Ident.lid  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (

let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (

let binders = (gather_tc_binders tps k)
in (

let p = (FStar_Ident.range_of_lid t)
in (

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _61_2301 -> (match (_61_2301) with
| (x, _61_2300) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (let _153_848 = (let _153_847 = (let _153_846 = (let _153_845 = (let _153_844 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _153_843 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_153_844), (_153_843))))
in (FStar_Absyn_Syntax.mk_Typ_app' _153_845 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _153_846))
in (_153_847)::[])
in (FStar_List.append imp_binders _153_848))
in (

let disc_type = (let _153_851 = (let _153_850 = (let _153_849 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _153_849 p))
in ((binders), (_153_850)))
in (FStar_Absyn_Syntax.mk_Typ_fun _153_851 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _153_854 = (let _153_853 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in ((disc_name), (disc_type), (_153_853), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Absyn_Syntax.Sig_val_decl (_153_854)))))))))))))


let mk_indexed_projectors = (fun fvq refine_domain env _61_2313 lid formals t -> (match (_61_2313) with
| (tc, tps, k) -> begin
(

let binders = (gather_tc_binders tps k)
in (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (

let projectee = (let _153_865 = (FStar_Absyn_Syntax.mk_ident (("projectee"), (p)))
in (let _153_864 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _153_865; FStar_Absyn_Syntax.realname = _153_864}))
in (

let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (

let arg_binder = (

let arg_typ = (let _153_868 = (let _153_867 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _153_866 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_153_867), (_153_866))))
in (FStar_Absyn_Syntax.mk_Typ_app' _153_868 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(

let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (

let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _153_878 = (let _153_877 = (let _153_876 = (let _153_875 = (let _153_874 = (let _153_873 = (let _153_872 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _153_871 = (let _153_870 = (let _153_869 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _153_869))
in (_153_870)::[])
in ((_153_872), (_153_871))))
in (FStar_Absyn_Syntax.mk_Exp_app _153_873 None p))
in (FStar_Absyn_Util.b2t _153_874))
in ((x), (_153_875)))
in (FStar_Absyn_Syntax.mk_Typ_refine _153_876 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _153_877))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _153_878))))
end)
in (

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _61_2330 -> (match (_61_2330) with
| (x, _61_2329) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (let _153_886 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(

let _61_2341 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_61_2341) with
| (field_name, _61_2340) -> begin
(

let proj = (let _153_883 = (let _153_882 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in ((_153_882), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Typ_app _153_883 None p))
in (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _61_2348 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_61_2348) with
| (field_name, _61_2347) -> begin
(

let proj = (let _153_885 = (let _153_884 = (FStar_Absyn_Util.fvar None field_name p)
in ((_153_884), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Exp_app _153_885 None p))
in (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end))))
in (FStar_All.pipe_right _153_886 FStar_List.flatten))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _153_888 = (FStar_All.pipe_right tps (FStar_List.map (fun _61_2355 -> (match (_61_2355) with
| (b, _61_2354) -> begin
((b), (Some (imp_tag)))
end))))
in (FStar_List.append _153_888 formals))
in (let _153_918 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(

let _61_2364 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_61_2364) with
| (field_name, _61_2363) -> begin
(

let kk = (let _153_892 = (let _153_891 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in ((binders), (_153_891)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _153_892 p))
in (FStar_Absyn_Syntax.Sig_tycon (((field_name), ([]), (kk), ([]), ([]), ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inl (a.FStar_Absyn_Syntax.v)))))::[]), ((FStar_Ident.range_of_lid field_name)))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _61_2371 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_61_2371) with
| (field_name, _61_2370) -> begin
(

let t = (let _153_895 = (let _153_894 = (let _153_893 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _153_893 p))
in ((binders), (_153_894)))
in (FStar_Absyn_Syntax.mk_Typ_fun _153_895 None p))
in (

let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (

let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inr (x.FStar_Absyn_Syntax.v)))))::[]))
in (

let impl = if (((let _153_898 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _153_898)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _153_900 = (let _153_899 = (FStar_Parser_DesugarEnv.current_module env)
in _153_899.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _153_900))) then begin
[]
end else begin
(

let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (

let as_imp = (fun _61_14 -> (match (_61_14) with
| Some (FStar_Absyn_Syntax.Implicit (_61_2379)) -> begin
true
end
| _61_2383 -> begin
false
end))
in (

let arg_pats = (let _153_915 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_61_2388), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _153_908 = (let _153_907 = (let _153_906 = (let _153_905 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_153_905))
in (pos _153_906))
in ((_153_907), ((as_imp imp))))
in (_153_908)::[])
end
end
| (FStar_Util.Inr (_61_2393), imp) -> begin
if ((i + ntps) = j) then begin
(let _153_910 = (let _153_909 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in ((_153_909), ((as_imp imp))))
in (_153_910)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _153_914 = (let _153_913 = (let _153_912 = (let _153_911 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_153_911))
in (pos _153_912))
in ((_153_913), ((as_imp imp))))
in (_153_914)::[])
end
end
end))))
in (FStar_All.pipe_right _153_915 FStar_List.flatten))
in (

let pat = (let _153_917 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv lid)), (Some (fvq)), (arg_pats)))) pos)
in (let _153_916 = (FStar_Absyn_Util.bvar_to_exp projection)
in ((_153_917), (None), (_153_916))))
in (

let body = (FStar_Absyn_Syntax.mk_Exp_match ((arg_exp), ((pat)::[])) None p)
in (

let imp = (FStar_Absyn_Syntax.mk_Exp_abs ((binders), (body)) None (FStar_Ident.range_of_lid field_name))
in (

let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((((false), ((lb)::[]))), (p), ([]), (quals))))::[])))))))
end
in (FStar_Absyn_Syntax.Sig_val_decl (((field_name), (t), (quals), ((FStar_Ident.range_of_lid field_name)))))::impl))))
end))
end))))
in (FStar_All.pipe_right _153_918 FStar_List.flatten))))))))))))))
end))


let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _61_17 -> (match (_61_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _61_2410, _61_2412) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_15 -> (match (_61_15) with
| FStar_Absyn_Syntax.RecordConstructor (_61_2417) -> begin
true
end
| _61_2420 -> begin
false
end)))) then begin
false
end else begin
(

let _61_2426 = tycon
in (match (_61_2426) with
| (l, _61_2423, _61_2425) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _61_2430 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(

let cod = (FStar_Absyn_Util.comp_result cod)
in (

let qual = (match ((FStar_Util.find_map quals (fun _61_16 -> (match (_61_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor (((lid), (fns))))
end
| _61_2441 -> begin
None
end)))) with
| None -> begin
FStar_Absyn_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (mk_indexed_projectors qual refine_domain env tycon lid formals cod)))
end
| _61_2447 -> begin
[]
end))
end
| _61_2449 -> begin
[]
end))


let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _61_18 -> (match (_61_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _153_938 = (let _153_937 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_153_937))
in (FStar_Parser_AST.mk_term _153_938 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (

let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (

let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (

let apply_binders = (fun t binders -> (

let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _61_2514 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _153_951 = (let _153_950 = (let _153_949 = (binder_to_term b)
in ((out), (_153_949), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_153_950))
in (FStar_Parser_AST.mk_term _153_951 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _61_19 -> (match (_61_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _61_2527 -> (match (_61_2527) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Absyn_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _153_957 = (let _153_956 = (let _153_955 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_153_955))
in (FStar_Parser_AST.mk_term _153_956 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _153_957 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _153_959 = (FStar_All.pipe_right fields (FStar_List.map (fun _61_2534 -> (match (_61_2534) with
| (x, _61_2533) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (false)))::[])))), (_153_959)))))))
end
| _61_2536 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _61_20 -> (match (_61_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _61_2550 = (typars_of_binders _env binders)
in (match (_61_2550) with
| (_env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (

let tconstr = (let _153_970 = (let _153_969 = (let _153_968 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_153_968))
in (FStar_Parser_AST.mk_term _153_969 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _153_970 binders))
in (

let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (

let se = FStar_Absyn_Syntax.Sig_tycon (((qlid), (typars), (k), (mutuals), ([]), (quals), (rng)))
in (

let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (

let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in ((_env), (_env2), (se), (tconstr))))))))
end))
end
| _61_2561 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparam = (fun env _61_21 -> (match (_61_21) with
| (FStar_Util.Inr (x), _61_2568) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _61_2573) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (

let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (_61_2577))::[] -> begin
(

let tc = (FStar_List.hd tcs)
in (

let _61_2588 = (desugar_abstract_tc quals env [] tc)
in (match (_61_2588) with
| (_61_2582, _61_2584, se, _61_2587) -> begin
(

let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(

let _61_2589 = (let _153_980 = (FStar_Range.string_of_range rng)
in (let _153_979 = (let _153_978 = (let _153_977 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _153_977 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _153_978 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _153_980 _153_979)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))
end)))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _61_2602 = (typars_of_binders env binders)
in (match (_61_2602) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _61_22 -> (match (_61_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _61_2607 -> begin
false
end)) quals) then begin
FStar_Absyn_Syntax.mk_Kind_effect
end else begin
FStar_Absyn_Syntax.kun
end
end
| Some (k) -> begin
(desugar_kind env' k)
end)
in (

let t0 = t
in (

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_23 -> (match (_61_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _61_2615 -> begin
false
end)))) then begin
quals
end else begin
if (t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula) then begin
(FStar_Absyn_Syntax.Logic)::quals
end else begin
quals
end
end
in (

let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Effect)) then begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let _153_986 = (let _153_985 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _153_984 = (FStar_All.pipe_right quals (FStar_List.filter (fun _61_24 -> (match (_61_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _61_2621 -> begin
true
end))))
in ((_153_985), (typars), (c), (_153_984), (rng))))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_153_986)))
end else begin
(

let t = (desugar_typ env' t)
in (let _153_988 = (let _153_987 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_153_987), (typars), (k), (t), (quals), (rng)))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_153_988)))
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_61_2626))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _61_2632 = (tycon_record_as_variant trec)
in (match (_61_2632) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_61_2636)::_61_2634 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _61_2647 = et
in (match (_61_2647) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_61_2649) -> begin
(

let trec = tc
in (

let _61_2654 = (tycon_record_as_variant trec)
in (match (_61_2654) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _61_2666 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_61_2666) with
| (env, _61_2663, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _61_2678 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_61_2678) with
| (env, _61_2675, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _61_2680 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _61_2683 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_61_2683) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _61_26 -> (match (_61_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _61_2690, _61_2692, _61_2694, _61_2696), t, quals) -> begin
(

let env_tps = (push_tparams env tpars)
in (

let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev (((id), (tpars), (k), (t), ([]), (rng))))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _61_2710, tags, _61_2713), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let env_tps = (push_tparams env tpars)
in (

let _61_2744 = (let _153_1004 = (FStar_All.pipe_right constrs (FStar_List.map (fun _61_2726 -> (match (_61_2726) with
| (id, topt, of_notation) -> begin
(

let t = if of_notation then begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[]), (tconstr)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end
| None -> begin
tconstr
end)
end else begin
(match (topt) with
| None -> begin
(FStar_All.failwith "Impossible")
end
| Some (t) -> begin
t
end)
end
in (

let t = (let _153_999 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _153_998 = (close env_tps t)
in (desugar_typ _153_999 _153_998)))
in (

let name = (FStar_Parser_DesugarEnv.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _61_25 -> (match (_61_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _61_2740 -> begin
[]
end))))
in (let _153_1003 = (let _153_1002 = (let _153_1001 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in ((name), (_153_1001), (tycon), (quals), (mutuals), (rng)))
in FStar_Absyn_Syntax.Sig_datacon (_153_1002))
in ((name), (_153_1003)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _153_1004))
in (match (_61_2744) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon (((tname), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))::constrs
end))))
end
| _61_2746 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let bundle = (let _153_1006 = (let _153_1005 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_153_1005), (rng)))
in FStar_Absyn_Syntax.Sig_bundle (_153_1006))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _61_27 -> (match (_61_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _61_2756, constrs, quals, _61_2760) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _61_2764 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env ops)
in ((env), ((FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end)))))))))))


let desugar_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.binder Prims.list) = (fun env binders -> (

let _61_2795 = (FStar_List.fold_left (fun _61_2773 b -> (match (_61_2773) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _61_2782 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2782) with
| (env, a) -> begin
(let _153_1015 = (let _153_1014 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_153_1014)::binders)
in ((env), (_153_1015)))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _61_2790 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_2790) with
| (env, x) -> begin
(let _153_1017 = (let _153_1016 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_153_1016)::binders)
in ((env), (_153_1017)))
end))
end
| _61_2792 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_61_2795) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Absyn_Syntax.qualifier = (fun r _61_28 -> (match (_61_28) with
| FStar_Parser_AST.Private -> begin
FStar_Absyn_Syntax.Private
end
| FStar_Parser_AST.Assumption -> begin
FStar_Absyn_Syntax.Assumption
end
| FStar_Parser_AST.Opaque -> begin
FStar_Absyn_Syntax.Opaque
end
| FStar_Parser_AST.Logic -> begin
FStar_Absyn_Syntax.Logic
end
| FStar_Parser_AST.Abstract -> begin
FStar_Absyn_Syntax.Abstract
end
| FStar_Parser_AST.New -> begin
FStar_Absyn_Syntax.New
end
| FStar_Parser_AST.TotalEffect -> begin
FStar_Absyn_Syntax.TotalEffect
end
| FStar_Parser_AST.DefaultEffect -> begin
FStar_Absyn_Syntax.DefaultEffect (None)
end
| FStar_Parser_AST.Effect -> begin
FStar_Absyn_Syntax.Effect
end
| (FStar_Parser_AST.Reflectable) | (FStar_Parser_AST.Reifiable) | (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Irreducible) | (FStar_Parser_AST.Unfoldable) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("This qualifier is supported only with the --universes option"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _61_29 -> (match (_61_29) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Absyn_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (s) -> begin
FStar_Absyn_Syntax.ResetOptions (s)
end))


let trans_quals : FStar_Range.range  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun r -> (FStar_List.map (trans_qual r)))


let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env d -> (

let trans_quals = (trans_quals d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = FStar_Absyn_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.TopLevelModule (_61_2825) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Multiple modules in a file are no longer supported"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _153_1035 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in ((_153_1035), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _153_1036 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _153_1036 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _153_1038 = (let _153_1037 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _153_1037))
in _153_1038.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _61_2845) -> begin
(

let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _61_2852 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let quals = (match (quals) with
| (_61_2857)::_61_2855 -> begin
(trans_quals quals)
end
| _61_2860 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _61_30 -> (match (_61_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_61_2869); FStar_Absyn_Syntax.lbtyp = _61_2867; FStar_Absyn_Syntax.lbeff = _61_2865; FStar_Absyn_Syntax.lbdef = _61_2863} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _61_2877; FStar_Absyn_Syntax.lbeff = _61_2875; FStar_Absyn_Syntax.lbdef = _61_2873} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (

let s = FStar_Absyn_Syntax.Sig_let (((lbs), (d.FStar_Parser_AST.drange), (lids), (quals)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in ((env), ((s)::[]))))))
end
| _61_2885 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_exp env t)
in (

let se = FStar_Absyn_Syntax.Sig_main (((e), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(

let f = (desugar_formula env t)
in (let _153_1044 = (let _153_1043 = (let _153_1042 = (let _153_1041 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_153_1041), (f), ((FStar_Absyn_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_assume (_153_1042))
in (_153_1043)::[])
in ((env), (_153_1044))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _153_1045 = (close_fun env t)
in (desugar_typ env _153_1045))
in (

let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _153_1046 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_153_1046)
end else begin
(trans_quals quals)
end
in (

let se = (let _153_1048 = (let _153_1047 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_153_1047), (t), (quals), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_val_decl (_153_1048))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let t = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (

let l = (FStar_Parser_DesugarEnv.qualify env id)
in (

let se = FStar_Absyn_Syntax.Sig_datacon (((l), (t), (((FStar_Absyn_Const.exn_lid), ([]), (FStar_Absyn_Syntax.ktype))), ((FStar_Absyn_Syntax.ExceptionConstructor)::[]), ((FStar_Absyn_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Absyn_Syntax.Sig_bundle ((((se)::[]), ((FStar_Absyn_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (

let data_ops = (mk_data_projectors env se)
in (

let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_typ env term)
in (

let t = (let _153_1053 = (let _153_1052 = (let _153_1049 = (FStar_Absyn_Syntax.null_v_binder t)
in (_153_1049)::[])
in (let _153_1051 = (let _153_1050 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _153_1050))
in ((_153_1052), (_153_1051))))
in (FStar_Absyn_Syntax.mk_Typ_fun _153_1053 None d.FStar_Parser_AST.drange))
in (

let l = (FStar_Parser_DesugarEnv.qualify env id)
in (

let se = FStar_Absyn_Syntax.Sig_datacon (((l), (t), (((FStar_Absyn_Const.exn_lid), ([]), (FStar_Absyn_Syntax.ktype))), ((FStar_Absyn_Syntax.ExceptionConstructor)::[]), ((FStar_Absyn_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Absyn_Syntax.Sig_bundle ((((se)::[]), ((FStar_Absyn_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (

let data_ops = (mk_data_projectors env se)
in (

let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(

let _61_2938 = (desugar_binders env binders)
in (match (_61_2938) with
| (env_k, binders) -> begin
(

let k = (desugar_kind env_k k)
in (

let name = (FStar_Parser_DesugarEnv.qualify env id)
in (

let se = FStar_Absyn_Syntax.Sig_kind_abbrev (((name), (binders), (k), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))))
end))
end
| FStar_Parser_AST.NewEffectForFree (_61_2944) -> begin
(FStar_All.failwith "effects for free only supported in conjunction with --universes")
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let env0 = env
in (

let _61_2957 = (desugar_binders env eff_binders)
in (match (_61_2957) with
| (env, binders) -> begin
(

let defn = (desugar_typ env defn)
in (

let _61_2961 = (FStar_Absyn_Util.head_and_args defn)
in (match (_61_2961) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _153_1058 = (let _153_1057 = (let _153_1056 = (let _153_1055 = (let _153_1054 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat "Effect " _153_1054))
in (Prims.strcat _153_1055 " not found"))
in ((_153_1056), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_153_1057))
in (Prims.raise _153_1058))
end
| Some (ed) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (

let sub = (FStar_Absyn_Util.subst_typ subst)
in (

let ed = (let _153_1076 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _153_1075 = (trans_quals quals)
in (let _153_1074 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _153_1073 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _153_1072 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _153_1071 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _153_1070 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _153_1069 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _153_1068 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _153_1067 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _153_1066 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _153_1065 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _153_1064 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _153_1063 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _153_1062 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _153_1061 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _153_1060 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _153_1076; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _153_1075; FStar_Absyn_Syntax.signature = _153_1074; FStar_Absyn_Syntax.ret = _153_1073; FStar_Absyn_Syntax.bind_wp = _153_1072; FStar_Absyn_Syntax.bind_wlp = _153_1071; FStar_Absyn_Syntax.if_then_else = _153_1070; FStar_Absyn_Syntax.ite_wp = _153_1069; FStar_Absyn_Syntax.ite_wlp = _153_1068; FStar_Absyn_Syntax.wp_binop = _153_1067; FStar_Absyn_Syntax.wp_as_type = _153_1066; FStar_Absyn_Syntax.close_wp = _153_1065; FStar_Absyn_Syntax.close_wp_t = _153_1064; FStar_Absyn_Syntax.assert_p = _153_1063; FStar_Absyn_Syntax.assume_p = _153_1062; FStar_Absyn_Syntax.null_wp = _153_1061; FStar_Absyn_Syntax.trivial = _153_1060})))))))))))))))))
in (

let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)
end
| _61_2973 -> begin
(let _153_1080 = (let _153_1079 = (let _153_1078 = (let _153_1077 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _153_1077 " is not an effect"))
in ((_153_1078), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_153_1079))
in (Prims.raise _153_1080))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, _actions)) -> begin
(

let env0 = env
in (

let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (

let _61_2988 = (desugar_binders env eff_binders)
in (match (_61_2988) with
| (env, binders) -> begin
(

let eff_k = (desugar_kind env eff_kind)
in (

let _61_2999 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _61_2992 decl -> (match (_61_2992) with
| (env, out) -> begin
(

let _61_2996 = (desugar_decl env decl)
in (match (_61_2996) with
| (env, ses) -> begin
(let _153_1084 = (let _153_1083 = (FStar_List.hd ses)
in (_153_1083)::out)
in ((env), (_153_1084)))
end))
end)) ((env), ([]))))
in (match (_61_2999) with
| (env, decls) -> begin
(

let decls = (FStar_List.rev decls)
in (

let lookup = (fun s -> (match ((let _153_1088 = (let _153_1087 = (FStar_Absyn_Syntax.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.qualify env _153_1087))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _153_1088))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat (Prims.strcat (Prims.strcat "Monad " eff_name.FStar_Ident.idText) " expects definition of ") s)), (d.FStar_Parser_AST.drange)))))
end
| Some (t) -> begin
t
end))
in (

let ed = (let _153_1104 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _153_1103 = (trans_quals quals)
in (let _153_1102 = (lookup "return")
in (let _153_1101 = (lookup "bind_wp")
in (let _153_1100 = (lookup "bind_wlp")
in (let _153_1099 = (lookup "if_then_else")
in (let _153_1098 = (lookup "ite_wp")
in (let _153_1097 = (lookup "ite_wlp")
in (let _153_1096 = (lookup "wp_binop")
in (let _153_1095 = (lookup "wp_as_type")
in (let _153_1094 = (lookup "close_wp")
in (let _153_1093 = (lookup "close_wp_t")
in (let _153_1092 = (lookup "assert_p")
in (let _153_1091 = (lookup "assume_p")
in (let _153_1090 = (lookup "null_wp")
in (let _153_1089 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _153_1104; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _153_1103; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _153_1102; FStar_Absyn_Syntax.bind_wp = _153_1101; FStar_Absyn_Syntax.bind_wlp = _153_1100; FStar_Absyn_Syntax.if_then_else = _153_1099; FStar_Absyn_Syntax.ite_wp = _153_1098; FStar_Absyn_Syntax.ite_wlp = _153_1097; FStar_Absyn_Syntax.wp_binop = _153_1096; FStar_Absyn_Syntax.wp_as_type = _153_1095; FStar_Absyn_Syntax.close_wp = _153_1094; FStar_Absyn_Syntax.close_wp_t = _153_1093; FStar_Absyn_Syntax.assert_p = _153_1092; FStar_Absyn_Syntax.assume_p = _153_1091; FStar_Absyn_Syntax.null_wp = _153_1090; FStar_Absyn_Syntax.trivial = _153_1089}))))))))))))))))
in (

let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _153_1111 = (let _153_1110 = (let _153_1109 = (let _153_1108 = (let _153_1107 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Effect name " _153_1107))
in (Prims.strcat _153_1108 " not found"))
in ((_153_1109), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_153_1110))
in (Prims.raise _153_1111))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let non_reifiable = (fun _61_31 -> (match (_61_31) with
| FStar_Parser_AST.NonReifiableLift (f) -> begin
f
end
| _61_3022 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected reifiable sub-effect"), (d.FStar_Parser_AST.drange)))))
end))
in (

let lift = (let _153_1114 = (non_reifiable l.FStar_Parser_AST.lift_op)
in (desugar_typ env _153_1114))
in (

let se = FStar_Absyn_Syntax.Sig_sub_effect ((({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))))))
end)))


let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _61_3030 d -> (match (_61_3030) with
| (env, sigelts) -> begin
(

let _61_3034 = (desugar_decl env d)
in (match (_61_3034) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]


let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let open_ns = (fun mname d -> (

let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _153_1134 = (let _153_1133 = (let _153_1131 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_153_1131))
in (let _153_1132 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _153_1133 _153_1132)))
in (_153_1134)::d)
end else begin
d
end
in d))
in (

let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (

let _61_3061 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _153_1136 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _153_1135 = (open_ns mname decls)
in ((_153_1136), (mname), (_153_1135), (true))))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _153_1138 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _153_1137 = (open_ns mname decls)
in ((_153_1138), (mname), (_153_1137), (false))))
end)
in (match (_61_3061) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _61_3064 = (desugar_decls env decls)
in (match (_61_3064) with
| (env, sigelts) -> begin
(

let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in ((env), (modul), (pop_when_done)))
end))
end)))))


let desugar_partial_modul : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun curmod env m -> (

let m = if (FStar_Options.interactive_fsi ()) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, _61_3075, _61_3077) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _61_3085 = (desugar_modul_common curmod env m)
in (match (_61_3085) with
| (x, y, _61_3084) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (

let _61_3091 = (desugar_modul_common None env m)
in (match (_61_3091) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (

let _61_3093 = if (FStar_Options.dump_module modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _153_1149 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _153_1149))
end else begin
()
end
in (let _153_1150 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in ((_153_1150), (modul)))))
end)))


let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (

let _61_3106 = (FStar_List.fold_left (fun _61_3099 m -> (match (_61_3099) with
| (env, mods) -> begin
(

let _61_3103 = (desugar_modul env m)
in (match (_61_3103) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_61_3106) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (

let _61_3111 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_61_3111) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (

let _61_3112 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _61_3112.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _61_3112.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _61_3112.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _61_3112.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _61_3112.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _61_3112.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _61_3112.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _61_3112.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _61_3112.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _61_3112.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _61_3112.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))





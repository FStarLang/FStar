
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


let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _154_17 = (let _154_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_154_16))
in (FStar_Parser_AST.mk_term _154_17 r FStar_Parser_AST.Kind)))


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
(let _154_28 = (let _154_26 = (FStar_Util.char_at s i)
in (name_of_char _154_26))
in (let _154_27 = (aux (i + 1))
in (_154_28)::_154_27))
end)
in (let _154_30 = (let _154_29 = (aux 0)
in (FStar_String.concat "_" _154_29))
in (Prims.strcat "op_" _154_30)))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _154_40 = (let _154_39 = (let _154_38 = (let _154_37 = (compile_op n s)
in ((_154_37), (r)))
in (FStar_Absyn_Syntax.mk_ident _154_38))
in (_154_39)::[])
in (FStar_All.pipe_right _154_40 FStar_Absyn_Syntax.lid_of_ids)))


let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (

let r = (fun l -> (let _154_51 = (FStar_Ident.set_lid_range l rng)
in Some (_154_51)))
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
in (match ((let _154_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _154_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _61_137); FStar_Absyn_Syntax.tk = _61_134; FStar_Absyn_Syntax.pos = _61_132; FStar_Absyn_Syntax.fvs = _61_130; FStar_Absyn_Syntax.uvs = _61_128}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _61_143 -> begin
(fallback ())
end))))


let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (

let r = (fun l -> (let _154_65 = (FStar_Ident.set_lid_range l rng)
in Some (_154_65)))
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
(match ((let _154_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _154_66))) with
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
(match ((let _154_73 = (unparen t)
in _154_73.FStar_Parser_AST.tm)) with
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
(let _154_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _154_78 Prims.fst))
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
(match ((let _154_81 = (unparen t)
in _154_81.FStar_Parser_AST.tm)) with
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


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _154_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _154_92)))


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
(let _154_99 = (free_type_vars env term)
in ((env), (_154_99)))
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
(let _154_100 = (free_type_vars env t)
in ((env), (_154_100)))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _154_103 = (unparen t)
in _154_103.FStar_Parser_AST.tm)) with
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
(let _154_106 = (free_type_vars env t1)
in (let _154_105 = (free_type_vars env t2)
in (FStar_List.append _154_106 _154_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _61_558 = (free_type_vars_b env b)
in (match (_61_558) with
| (env, f) -> begin
(let _154_107 = (free_type_vars env t)
in (FStar_List.append f _154_107))
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
(let _154_110 = (free_type_vars env body)
in (FStar_List.append free _154_110))
end))
end
| FStar_Parser_AST.Project (t, _61_577) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _154_117 = (unparen t)
in _154_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _61_627 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _154_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _154_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _154_126 = (let _154_125 = (let _154_124 = (kind_star x.FStar_Ident.idRange)
in ((x), (_154_124)))
in FStar_Parser_AST.TAnnotated (_154_125))
in (FStar_Parser_AST.mk_binder _154_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _154_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _154_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _154_135 = (let _154_134 = (let _154_133 = (kind_star x.FStar_Ident.idRange)
in ((x), (_154_133)))
in FStar_Parser_AST.TAnnotated (_154_134))
in (FStar_Parser_AST.mk_binder _154_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _154_136 = (unlabel t)
in _154_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_61_640) -> begin
t
end
| _61_643 -> begin
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
| _61_653 -> begin
((bs), (t))
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _61_657) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_61_663); FStar_Parser_AST.prange = _61_661}, _61_667) -> begin
true
end
| _61_671 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _61_683 = (destruct_app_pattern env is_top_level p)
in (match (_61_683) with
| (name, args, _61_682) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_688); FStar_Parser_AST.prange = _61_685}, args) when is_top_level -> begin
(let _154_150 = (let _154_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_154_149))
in ((_154_150), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_699); FStar_Parser_AST.prange = _61_696}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _61_707 -> begin
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
| TBinder (_61_710) -> begin
_61_710
end))


let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_61_713) -> begin
_61_713
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_61_716) -> begin
_61_716
end))


let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _61_3 -> (match (_61_3) with
| TBinder (a, k, aq) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), (aq))
end
| VBinder (x, t, aq) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (aq))
end
| _61_729 -> begin
(FStar_All.failwith "Impossible")
end))


let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _61_4 -> (match (_61_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _61_736 -> begin
None
end))


let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either  ->  (FStar_Absyn_Syntax.binder * FStar_Parser_DesugarEnv.env) = (fun env imp _61_5 -> (match (_61_5) with
| FStar_Util.Inl (None, k) -> begin
(let _154_203 = (FStar_Absyn_Syntax.null_t_binder k)
in ((_154_203), (env)))
end
| FStar_Util.Inr (None, t) -> begin
(let _154_204 = (FStar_Absyn_Syntax.null_v_binder t)
in ((_154_204), (env)))
end
| FStar_Util.Inl (Some (a), k) -> begin
(

let _61_755 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_755) with
| (env, a) -> begin
((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual imp)))), (env))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _61_763 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_763) with
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
| _61_773 -> begin
(let _154_215 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _154_215))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (((f), (msg), (polarity)))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (

let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _154_219 = (let _154_218 = (aux g)
in FStar_Parser_AST.Paren (_154_218))
in (FStar_Parser_AST.mk_term _154_219 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", (f1)::(f2)::[]) -> begin
(let _154_225 = (let _154_224 = (let _154_223 = (let _154_222 = (aux f1)
in (let _154_221 = (let _154_220 = (aux f2)
in (_154_220)::[])
in (_154_222)::_154_221))
in (("/\\"), (_154_223)))
in FStar_Parser_AST.Op (_154_224))
in (FStar_Parser_AST.mk_term _154_225 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _154_229 = (let _154_228 = (let _154_227 = (aux f2)
in (let _154_226 = (aux f3)
in ((f1), (_154_227), (_154_226))))
in FStar_Parser_AST.If (_154_228))
in (FStar_Parser_AST.mk_term _154_229 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _154_232 = (let _154_231 = (let _154_230 = (aux g)
in ((binders), (_154_230)))
in FStar_Parser_AST.Abs (_154_231))
in (FStar_Parser_AST.mk_term _154_232 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _61_795 -> begin
(label f)
end))
in (aux f))))


let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _61_799 -> (match (_61_799) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))


let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _61_6 -> (match (_61_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _61_810 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
((l), (e), (y))
end
| _61_815 -> begin
(

let _61_818 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_61_818) with
| (e, x) -> begin
(((FStar_Util.Inr (x))::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _61_7 -> (match (_61_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _61_827 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
((l), (e), (b))
end
| _61_832 -> begin
(

let _61_835 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_61_835) with
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
| FStar_Parser_AST.PatOp (_61_846) -> begin
(FStar_All.failwith "let op not supported in stratified")
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _61_860 = (aux loc env p)
in (match (_61_860) with
| (loc, env, var, p, _61_859) -> begin
(

let _61_877 = (FStar_List.fold_left (fun _61_864 p -> (match (_61_864) with
| (loc, env, ps) -> begin
(

let _61_873 = (aux loc env p)
in (match (_61_873) with
| (loc, env, _61_869, p, _61_872) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_61_877) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (

let _61_879 = (let _154_304 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _154_304))
in ((loc), (env), (var), (pat), (false))))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_61_886) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(

let _61_892 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (((x), (imp))); FStar_Parser_AST.prange = _61_892.FStar_Parser_AST.prange})
end
| _61_895 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
p
end
in (

let _61_902 = (aux loc env p)
in (match (_61_902) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_61_904) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _61_908, aq) -> begin
(let _154_306 = (let _154_305 = (desugar_kind env t)
in ((x), (_154_305), (aq)))
in TBinder (_154_306))
end
| VBinder (x, _61_914, aq) -> begin
(

let t = (close_fun env t)
in (let _154_308 = (let _154_307 = (desugar_typ env t)
in ((x), (_154_307), (aq)))
in VBinder (_154_308)))
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
in (let _154_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((a), (FStar_Absyn_Syntax.kun), (aq)))), (_154_309), (imp))))
end else begin
(

let _61_930 = (resolvea loc env a)
in (match (_61_930) with
| (loc, env, abvd) -> begin
(let _154_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((abvd), (FStar_Absyn_Syntax.kun), (aq)))), (_154_310), (imp)))
end))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (

let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _154_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_154_311), (false)))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _154_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_154_312), (false))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _61_946 = (resolvex loc env x)
in (match (_61_946) with
| (loc, env, xbvd) -> begin
(let _154_313 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((xbvd), (FStar_Absyn_Syntax.tun), (aq)))), (_154_313), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _154_314 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), ([])))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_154_314), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _61_952}, args) -> begin
(

let _61_974 = (FStar_List.fold_right (fun arg _61_963 -> (match (_61_963) with
| (loc, env, args) -> begin
(

let _61_970 = (aux loc env arg)
in (match (_61_970) with
| (loc, env, _61_967, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_61_974) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _154_317 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_154_317), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_61_978) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _61_998 = (FStar_List.fold_right (fun pat _61_986 -> (match (_61_986) with
| (loc, env, pats) -> begin
(

let _61_994 = (aux loc env pat)
in (match (_61_994) with
| (loc, env, _61_990, pat, _61_993) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_61_998) with
| (loc, env, pats) -> begin
(

let pat = (let _154_324 = (let _154_323 = (let _154_322 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _154_322))
in (FStar_All.pipe_left _154_323 (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ([]))))))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((hd), (false)))::(((tl), (false)))::[]))))))) pats _154_324))
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _61_1024 = (FStar_List.fold_left (fun _61_1011 p -> (match (_61_1011) with
| (loc, env, pats) -> begin
(

let _61_1020 = (aux loc env p)
in (match (_61_1020) with
| (loc, env, _61_1016, pat, _61_1019) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_61_1024) with
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
| FStar_Absyn_Syntax.Exp_fvar (v, _61_1030) -> begin
v
end
| _61_1034 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _154_327 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_154_327), (false))))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _61_1044 = (FStar_List.hd fields)
in (match (_61_1044) with
| (f, _61_1043) -> begin
(

let _61_1048 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_61_1048) with
| (record, _61_1047) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _61_1051 -> (match (_61_1051) with
| (f, p) -> begin
(let _154_329 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in ((_154_329), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _61_1056 -> (match (_61_1056) with
| (f, _61_1055) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _61_1060 -> (match (_61_1060) with
| (g, _61_1059) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_61_1063, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _61_1075 = (aux loc env app)
in (match (_61_1075) with
| (env, e, b, p, _61_1074) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _61_1078, args) -> begin
(let _154_337 = (let _154_336 = (let _154_335 = (let _154_334 = (let _154_333 = (let _154_332 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_154_332)))
in FStar_Absyn_Syntax.Record_ctor (_154_333))
in Some (_154_334))
in ((fv), (_154_335), (args)))
in FStar_Absyn_Syntax.Pat_cons (_154_336))
in (FStar_All.pipe_left pos _154_337))
end
| _61_1083 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _61_1092 = (aux [] env p)
in (match (_61_1092) with
| (_61_1086, env, b, p, _61_1091) -> begin
((env), (b), (p))
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _61_1098) -> begin
(let _154_343 = (let _154_342 = (let _154_341 = (FStar_Parser_DesugarEnv.qualify env x)
in ((_154_341), (FStar_Absyn_Syntax.tun)))
in LetBinder (_154_342))
in ((env), (_154_343), (None)))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _61_1105); FStar_Parser_AST.prange = _61_1102}, t) -> begin
(let _154_347 = (let _154_346 = (let _154_345 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _154_344 = (desugar_typ env t)
in ((_154_345), (_154_344))))
in LetBinder (_154_346))
in ((env), (_154_347), (None)))
end
| _61_1113 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _61_1117 = (desugar_data_pat env p)
in (match (_61_1117) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _61_1128 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _61_1132 env pat -> (

let _61_1140 = (desugar_data_pat env pat)
in (match (_61_1140) with
| (env, _61_1138, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _154_357 = (desugar_typ env t)
in FStar_Util.Inl (_154_357))
end else begin
(let _154_358 = (desugar_exp env t)
in FStar_Util.Inr (_154_358))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (

let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _61_1154 = e
in {FStar_Absyn_Syntax.n = _61_1154.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1154.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1154.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1154.FStar_Absyn_Syntax.uvs}))
in (match ((let _154_378 = (unparen top)
in _154_378.FStar_Parser_AST.tm)) with
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

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _154_382 = (desugar_typ_or_exp env t)
in ((_154_382), (None))))))
in (let _154_383 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _154_383))))
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
(let _154_384 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _154_384))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let dt = (let _154_389 = (let _154_388 = (let _154_387 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in ((_154_387), (Some (FStar_Absyn_Syntax.Data_ctor))))
in (FStar_Absyn_Syntax.mk_Exp_fvar _154_388))
in (FStar_All.pipe_left pos _154_389))
in (match (args) with
| [] -> begin
dt
end
| _61_1181 -> begin
(

let args = (FStar_List.map (fun _61_1184 -> (match (_61_1184) with
| (t, imp) -> begin
(

let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _154_394 = (let _154_393 = (let _154_392 = (let _154_391 = (FStar_Absyn_Util.mk_exp_app dt args)
in ((_154_391), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_154_392))
in (FStar_Absyn_Syntax.mk_Exp_meta _154_393))
in (FStar_All.pipe_left setpos _154_394)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _61_1221 = (FStar_List.fold_left (fun _61_1193 pat -> (match (_61_1193) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _61_1196}, t) -> begin
(

let ftvs = (let _154_397 = (free_type_vars env t)
in (FStar_List.append _154_397 ftvs))
in (let _154_399 = (let _154_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _154_398))
in ((_154_399), (ftvs))))
end
| FStar_Parser_AST.PatTvar (a, _61_1208) -> begin
(let _154_401 = (let _154_400 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _154_400))
in ((_154_401), (ftvs)))
end
| FStar_Parser_AST.PatAscribed (_61_1212, t) -> begin
(let _154_403 = (let _154_402 = (free_type_vars env t)
in (FStar_List.append _154_402 ftvs))
in ((env), (_154_403)))
end
| _61_1217 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_61_1221) with
| (_61_1219, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _154_405 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _154_405 binders))
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

let _61_1244 = (desugar_binding_pat env p)
in (match (_61_1244) with
| (env, b, pat) -> begin
(

let _61_1304 = (match (b) with
| LetBinder (_61_1246) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _154_414 = (binder_of_bnd b)
in ((_154_414), (sc_pat_opt)))
end
| VBinder (x, t, aq) -> begin
(

let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _61_1261) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _154_416 = (let _154_415 = (FStar_Absyn_Util.bvar_to_exp b)
in ((_154_415), (p)))
in Some (_154_416))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Absyn_Syntax.n), (p'.FStar_Absyn_Syntax.v))) with
| (FStar_Absyn_Syntax.Exp_bvar (_61_1275), _61_1278) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (

let sc = (let _154_423 = (let _154_422 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _154_421 = (let _154_420 = (FStar_Absyn_Syntax.varg sc)
in (let _154_419 = (let _154_418 = (let _154_417 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _154_417))
in (_154_418)::[])
in (_154_420)::_154_419))
in ((_154_422), (_154_421))))
in (FStar_Absyn_Syntax.mk_Exp_app _154_423 None top.FStar_Parser_AST.range))
in (

let p = (let _154_424 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((p'), (false)))::(((p), (false)))::[])))) None _154_424))
in Some (((sc), (p))))))
end
| (FStar_Absyn_Syntax.Exp_app (_61_1284, args), FStar_Absyn_Syntax.Pat_cons (_61_1289, _61_1291, pats)) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (

let sc = (let _154_430 = (let _154_429 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _154_428 = (let _154_427 = (let _154_426 = (let _154_425 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _154_425))
in (_154_426)::[])
in (FStar_List.append args _154_427))
in ((_154_429), (_154_428))))
in (FStar_Absyn_Syntax.mk_Exp_app _154_430 None top.FStar_Parser_AST.range))
in (

let p = (let _154_431 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((FStar_List.append pats ((((p), (false)))::[])))))) None _154_431))
in Some (((sc), (p))))))
end
| _61_1300 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((FStar_Util.Inr (b)), (aq))), (sc_pat_opt))))
end)
in (match (_61_1304) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _61_1308; FStar_Parser_AST.level = _61_1306}, arg, _61_1314) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env arg)
in (let _154_441 = (let _154_440 = (let _154_439 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _154_438 = (let _154_437 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _154_436 = (let _154_435 = (let _154_434 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _154_434))
in (_154_435)::[])
in (_154_437)::_154_436))
in ((_154_439), (_154_438))))
in (FStar_Absyn_Syntax.mk_Exp_app _154_440))
in (FStar_All.pipe_left pos _154_441)))
end
| FStar_Parser_AST.App (_61_1319) -> begin
(

let rec aux = (fun args e -> (match ((let _154_446 = (unparen e)
in _154_446.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _154_447 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _154_447))
in (aux ((arg)::args) e))
end
| _61_1331 -> begin
(

let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app ((head), (args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _154_453 = (let _154_452 = (let _154_451 = (let _154_450 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_154_450), (FStar_Absyn_Syntax.Sequence)))
in FStar_Absyn_Syntax.Meta_desugared (_154_451))
in (FStar_Absyn_Syntax.mk_Exp_meta _154_452))
in (FStar_All.pipe_left setpos _154_453))
end
| FStar_Parser_AST.LetOpen (_61_1338) -> begin
(FStar_All.failwith "let open in universes")
end
| FStar_Parser_AST.Let (is_rec, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (is_rec = FStar_Parser_AST.Rec)
in (

let ds_let_rec = (fun _61_1351 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _61_1355 -> (match (_61_1355) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _154_457 = (destruct_app_pattern env top_level p)
in ((_154_457), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _154_458 = (destruct_app_pattern env top_level p)
in ((_154_458), (def)))
end
| _61_1361 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_1366); FStar_Parser_AST.prange = _61_1363}, t) -> begin
if top_level then begin
(let _154_461 = (let _154_460 = (let _154_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_154_459))
in ((_154_460), ([]), (Some (t))))
in ((_154_461), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _61_1375) -> begin
if top_level then begin
(let _154_464 = (let _154_463 = (let _154_462 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_154_462))
in ((_154_463), ([]), (None)))
in ((_154_464), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _61_1379 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _61_1405 = (FStar_List.fold_left (fun _61_1383 _61_1392 -> (match (((_61_1383), (_61_1392))) with
| ((env, fnames), ((f, _61_1386, _61_1388), _61_1391)) -> begin
(

let _61_1402 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _61_1397 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_1397) with
| (env, xx) -> begin
((env), (FStar_Util.Inl (xx)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _154_467 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in ((_154_467), (FStar_Util.Inr (l))))
end)
in (match (_61_1402) with
| (env, lbname) -> begin
((env), ((lbname)::fnames))
end))
end)) ((env), ([])) funs)
in (match (_61_1405) with
| (env', fnames) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _61_1416 -> (match (_61_1416) with
| ((_61_1411, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _154_474 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _154_474 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _61_1423 -> begin
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

let _61_1436 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_61_1436) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_61_1438) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(

let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]))), (body)))))
end
| VBinder (x, t, _61_1448) -> begin
(

let body = (desugar_exp env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _154_486 = (let _154_485 = (FStar_Absyn_Util.bvd_to_exp x t)
in ((_154_485), ((((pat), (None), (body)))::[])))
in (FStar_Absyn_Syntax.mk_Exp_match _154_486 None body.FStar_Absyn_Syntax.pos))
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
(let _154_499 = (let _154_498 = (let _154_497 = (desugar_exp env t1)
in (let _154_496 = (let _154_495 = (let _154_491 = (desugar_exp env t2)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range)), (None), (_154_491)))
in (let _154_494 = (let _154_493 = (let _154_492 = (desugar_exp env t3)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range)), (None), (_154_492)))
in (_154_493)::[])
in (_154_495)::_154_494))
in ((_154_497), (_154_496))))
in (FStar_Absyn_Syntax.mk_Exp_match _154_498))
in (FStar_All.pipe_left pos _154_499))
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

let desugar_branch = (fun _61_1487 -> (match (_61_1487) with
| (pat, wopt, b) -> begin
(

let _61_1490 = (desugar_match_pat env pat)
in (match (_61_1490) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _154_502 = (desugar_exp env e)
in Some (_154_502))
end)
in (

let b = (desugar_exp env b)
in ((pat), (wopt), (b))))
end))
end))
in (let _154_508 = (let _154_507 = (let _154_506 = (desugar_exp env e)
in (let _154_505 = (FStar_List.map desugar_branch branches)
in ((_154_506), (_154_505))))
in (FStar_Absyn_Syntax.mk_Exp_match _154_507))
in (FStar_All.pipe_left pos _154_508)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _154_514 = (let _154_513 = (let _154_512 = (desugar_exp env e)
in (let _154_511 = (desugar_typ env t)
in ((_154_512), (_154_511), (None))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _154_513))
in (FStar_All.pipe_left pos _154_514))
end
| FStar_Parser_AST.Record (_61_1501, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _61_1512 = (FStar_List.hd fields)
in (match (_61_1512) with
| (f, _61_1511) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _61_1518 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_61_1518) with
| (record, _61_1517) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _61_1526 -> (match (_61_1526) with
| (g, _61_1525) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_61_1530, e) -> begin
(let _154_522 = (qfn fn)
in ((_154_522), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _154_525 = (let _154_524 = (let _154_523 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_154_523), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_154_524))
in (Prims.raise _154_525))
end
| Some (x) -> begin
(let _154_526 = (qfn fn)
in ((_154_526), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _154_531 = (let _154_530 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _61_1542 -> (match (_61_1542) with
| (f, _61_1541) -> begin
(let _154_529 = (let _154_528 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _154_528))
in ((_154_529), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_DesugarEnv.constrname), (_154_530)))
in FStar_Parser_AST.Construct (_154_531))
end
| Some (e) -> begin
(

let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (

let xterm = (let _154_533 = (let _154_532 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_154_532))
in (FStar_Parser_AST.mk_term _154_533 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _154_536 = (let _154_535 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _61_1550 -> (match (_61_1550) with
| (f, _61_1549) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_154_535)))
in FStar_Parser_AST.Record (_154_536))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _61_1573); FStar_Absyn_Syntax.tk = _61_1570; FStar_Absyn_Syntax.pos = _61_1568; FStar_Absyn_Syntax.fvs = _61_1566; FStar_Absyn_Syntax.uvs = _61_1564}, args); FStar_Absyn_Syntax.tk = _61_1562; FStar_Absyn_Syntax.pos = _61_1560; FStar_Absyn_Syntax.fvs = _61_1558; FStar_Absyn_Syntax.uvs = _61_1556}, FStar_Absyn_Syntax.Data_app)) -> begin
(

let e = (let _154_546 = (let _154_545 = (let _154_544 = (let _154_543 = (let _154_542 = (let _154_541 = (let _154_540 = (let _154_539 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_154_539)))
in FStar_Absyn_Syntax.Record_ctor (_154_540))
in Some (_154_541))
in ((fv), (_154_542)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _154_543 None e.FStar_Absyn_Syntax.pos))
in ((_154_544), (args)))
in (FStar_Absyn_Syntax.mk_Exp_app _154_545))
in (FStar_All.pipe_left pos _154_546))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (FStar_Absyn_Syntax.Data_app))))))
end
| _61_1587 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _61_1594 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_61_1594) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_exp env e)
in (

let fn = (

let _61_1599 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_61_1599) with
| (ns, _61_1598) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _154_553 = (let _154_552 = (let _154_551 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (let _154_550 = (let _154_549 = (FStar_Absyn_Syntax.varg e)
in (_154_549)::[])
in ((_154_551), (_154_550))))
in (FStar_Absyn_Syntax.mk_Exp_app _154_552))
in (FStar_All.pipe_left pos _154_553)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _61_1605 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (

let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _61_1612 = t
in {FStar_Absyn_Syntax.n = _61_1612.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1612.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1612.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1612.FStar_Absyn_Syntax.uvs}))
in (

let top = (unparen top)
in (

let head_and_args = (fun t -> (

let rec aux = (fun args t -> (match ((let _154_576 = (unparen t)
in _154_576.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _61_1630 -> begin
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
(let _154_577 = (desugar_exp env t)
in (FStar_All.pipe_right _154_577 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _154_578 = (desugar_exp env t)
in (FStar_All.pipe_right _154_578 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", (t1)::(_61_1644)::[]) -> begin
if (is_type env t1) then begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _154_581 = (flatten t1)
in (FStar_List.append _154_581 ((t2)::[])))
end
| _61_1658 -> begin
(t)::[]
end))
in (

let targs = (let _154_584 = (flatten top)
in (FStar_All.pipe_right _154_584 (FStar_List.map (fun t -> (let _154_583 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _154_583))))))
in (

let tup = (let _154_585 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _154_585))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))))
end else begin
(let _154_591 = (let _154_590 = (let _154_589 = (let _154_588 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _154_588))
in ((_154_589), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_154_590))
in (Prims.raise _154_591))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _154_592 = (desugar_exp env top)
in (FStar_All.pipe_right _154_592 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(

let args = (FStar_List.map (fun t -> (let _154_594 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _154_594))) args)
in (let _154_595 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _154_595 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _154_596 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _154_596))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _154_597 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _154_597))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _154_598 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _154_598)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let t = (let _154_599 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _154_599))
in (

let args = (FStar_List.map (fun _61_1694 -> (match (_61_1694) with
| (t, imp) -> begin
(let _154_601 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _154_601))
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

let _61_1712 = (desugar_binding_pat env hd)
in (match (_61_1712) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _154_613 = (let _154_612 = (let _154_611 = (let _154_610 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _154_610))
in ((_154_611), (hd.FStar_Parser_AST.prange)))
in FStar_Absyn_Syntax.Error (_154_612))
in (Prims.raise _154_613))
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
| FStar_Parser_AST.App (_61_1718) -> begin
(

let rec aux = (fun args e -> (match ((let _154_618 = (unparen e)
in _154_618.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(

let arg = (let _154_619 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _154_619))
in (aux ((arg)::args) e))
end
| _61_1730 -> begin
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

let _61_1742 = (uncurry binders t)
in (match (_61_1742) with
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

let _61_1756 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_61_1756) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _61_1763) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _61_1777 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _61_1769), env) -> begin
((x), (env))
end
| _61_1774 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_61_1777) with
| (b, env) -> begin
(

let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _154_630 = (desugar_exp env f)
in (FStar_All.pipe_right _154_630 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine ((b), (f)))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _154_638 = (let _154_637 = (let _154_636 = (desugar_typ env t)
in (let _154_635 = (desugar_kind env k)
in ((_154_636), (_154_635))))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _154_637))
in (FStar_All.pipe_left wpos _154_638))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _61_1811 = (FStar_List.fold_left (fun _61_1796 b -> (match (_61_1796) with
| (env, tparams, typs) -> begin
(

let _61_1800 = (desugar_exp_binder env b)
in (match (_61_1800) with
| (xopt, t) -> begin
(

let _61_1806 = (match (xopt) with
| None -> begin
(let _154_641 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in ((env), (_154_641)))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_61_1806) with
| (env, x) -> begin
(let _154_645 = (let _154_644 = (let _154_643 = (let _154_642 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_642))
in (_154_643)::[])
in (FStar_List.append typs _154_644))
in ((env), ((FStar_List.append tparams ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (None)))::[]))), (_154_645)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_61_1811) with
| (env, _61_1809, targs) -> begin
(

let tup = (let _154_646 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _154_646))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))
end))
end
| FStar_Parser_AST.Record (_61_1814) -> begin
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
| _61_1833 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _61_1835 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r))))))
in (

let pre_process_comp_typ = (fun t -> (

let _61_1846 = (head_and_args t)
in (match (_61_1846) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let _61_1872 = (FStar_All.pipe_right args (FStar_List.partition (fun _61_1854 -> (match (_61_1854) with
| (arg, _61_1853) -> begin
(match ((let _154_658 = (unparen arg)
in _154_658.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _61_1858; FStar_Parser_AST.level = _61_1856}, _61_1863, _61_1865) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _61_1869 -> begin
false
end)
end))))
in (match (_61_1872) with
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
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _154_659 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _154_659 FStar_Absyn_Const.prims_lid))) -> begin
(

let args = (FStar_List.map (fun _61_1887 -> (match (_61_1887) with
| (t, imp) -> begin
(let _154_661 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _154_661))
end)) args)
in (let _154_662 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _154_662 args)))
end
| _61_1890 -> begin
(desugar_typ env t)
end)
end)))
in (

let t = (pre_process_comp_typ t)
in (

let _61_1894 = (FStar_Absyn_Util.head_and_args t)
in (match (_61_1894) with
| (head, args) -> begin
(match ((let _154_664 = (let _154_663 = (FStar_Absyn_Util.compress_typ head)
in _154_663.FStar_Absyn_Syntax.n)
in ((_154_664), (args)))) with
| (FStar_Absyn_Syntax.Typ_const (eff), ((FStar_Util.Inl (result_typ), _61_1901))::rest) -> begin
(

let _61_1941 = (FStar_All.pipe_right rest (FStar_List.partition (fun _61_11 -> (match (_61_11) with
| (FStar_Util.Inr (_61_1907), _61_1910) -> begin
false
end
| (FStar_Util.Inl (t), _61_1915) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _61_1924; FStar_Absyn_Syntax.pos = _61_1922; FStar_Absyn_Syntax.fvs = _61_1920; FStar_Absyn_Syntax.uvs = _61_1918}, ((FStar_Util.Inr (_61_1929), _61_1932))::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _61_1938 -> begin
false
end)
end))))
in (match (_61_1941) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _61_12 -> (match (_61_12) with
| (FStar_Util.Inl (t), _61_1946) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_61_1949, ((FStar_Util.Inr (arg), _61_1953))::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _61_1959 -> begin
(FStar_All.failwith "impos")
end)
end
| _61_1961 -> begin
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
(let _154_671 = (let _154_670 = (let _154_669 = (let _154_668 = (let _154_667 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((pat), (FStar_Absyn_Syntax.Meta_smt_pat)))))
in FStar_Util.Inr (_154_667))
in ((_154_668), (aq)))
in (_154_669)::[])
in (ens)::_154_670)
in (req)::_154_671)
end
| _61_1972 -> begin
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
(let _154_673 = (let _154_672 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _154_672))
in (fail _154_673))
end
end)
end))
end
| _61_1975 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _154_675 = (let _154_674 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _154_674))
in (fail _154_675))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (

let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (

let setpos = (fun kk -> (

let _61_1982 = kk
in {FStar_Absyn_Syntax.n = _61_1982.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1982.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1982.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1982.FStar_Absyn_Syntax.uvs}))
in (

let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _61_1991; FStar_Ident.ident = _61_1989; FStar_Ident.nsstr = _61_1987; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _61_2000; FStar_Ident.ident = _61_1998; FStar_Ident.nsstr = _61_1996; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _154_687 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _154_687))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), ([]))), (FStar_Absyn_Syntax.mk_Kind_unknown))))
end
| _61_2008 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(

let _61_2016 = (uncurry bs k)
in (match (_61_2016) with
| (bs, k) -> begin
(

let rec aux = (fun env bs _61_13 -> (match (_61_13) with
| [] -> begin
(let _154_698 = (let _154_697 = (let _154_696 = (desugar_kind env k)
in (((FStar_List.rev bs)), (_154_696)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _154_697))
in (FStar_All.pipe_left pos _154_698))
end
| (hd)::tl -> begin
(

let _61_2027 = (let _154_700 = (let _154_699 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _154_699 hd))
in (FStar_All.pipe_right _154_700 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_61_2027) with
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

let args = (FStar_List.map (fun _61_2037 -> (match (_61_2037) with
| (t, b) -> begin
(

let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _154_702 = (desugar_typ_or_exp env t)
in ((_154_702), (qual))))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (FStar_Absyn_Syntax.mk_Kind_unknown)))))
end)
end
| _61_2041 -> begin
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
| _61_2052 -> begin
None
end))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _61_2057 = t
in {FStar_Absyn_Syntax.n = _61_2057.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_2057.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_2057.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_2057.FStar_Absyn_Syntax.uvs}))
in (

let desugar_quant = (fun q qt b pats body -> (

let tk = (desugar_binder env (

let _61_2065 = b
in {FStar_Parser_AST.b = _61_2065.FStar_Parser_AST.b; FStar_Parser_AST.brange = _61_2065.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _61_2065.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _154_738 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _154_738)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _61_2080 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2080) with
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
| _61_2085 -> begin
(let _154_739 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
in (FStar_All.pipe_left setpos _154_739))
end)
in (

let body = (let _154_745 = (let _154_744 = (let _154_743 = (let _154_742 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_154_742)::[])
in ((_154_743), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_744))
in (FStar_All.pipe_left pos _154_745))
in (let _154_750 = (let _154_749 = (let _154_746 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _154_746 FStar_Absyn_Syntax.kun))
in (let _154_748 = (let _154_747 = (FStar_Absyn_Syntax.targ body)
in (_154_747)::[])
in (FStar_Absyn_Util.mk_typ_app _154_749 _154_748)))
in (FStar_All.pipe_left setpos _154_750))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _61_2095 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_2095) with
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
| _61_2100 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
end)
in (

let body = (let _154_756 = (let _154_755 = (let _154_754 = (let _154_753 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_154_753)::[])
in ((_154_754), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_755))
in (FStar_All.pipe_left pos _154_756))
in (let _154_761 = (let _154_760 = (let _154_757 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _154_757 FStar_Absyn_Syntax.kun))
in (let _154_759 = (let _154_758 = (FStar_Absyn_Syntax.targ body)
in (_154_758)::[])
in (FStar_Absyn_Util.mk_typ_app _154_760 _154_759)))
in (FStar_All.pipe_left setpos _154_761))))))
end))
end
| _61_2104 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _154_776 = (q ((rest), (pats), (body)))
in (let _154_775 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _154_776 _154_775 FStar_Parser_AST.Formula)))
in (let _154_777 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _154_777 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _61_2118 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _154_778 = (unparen f)
in _154_778.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (l), (FStar_Absyn_Syntax.dummyRange), (p))))))
end
| FStar_Parser_AST.Op ("==", (hd)::_args) -> begin
(

let args = (hd)::_args
in (

let args = (FStar_List.map (fun t -> (let _154_780 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _154_780))) args)
in (

let eq = if (is_type env hd) then begin
(let _154_781 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _154_781 FStar_Absyn_Syntax.kun))
end else begin
(let _154_782 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _154_782 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((((connective s)), (args))) with
| (Some (conn), (_61_2144)::(_61_2142)::[]) -> begin
(let _154_787 = (let _154_783 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _154_783 FStar_Absyn_Syntax.kun))
in (let _154_786 = (FStar_List.map (fun x -> (let _154_785 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_785))) args)
in (FStar_Absyn_Util.mk_typ_app _154_787 _154_786)))
end
| _61_2149 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _154_788 = (desugar_exp env f)
in (FStar_All.pipe_right _154_788 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _154_793 = (let _154_789 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _154_789 FStar_Absyn_Syntax.kun))
in (let _154_792 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _154_791 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_791))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _154_793 _154_792)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _154_795 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _154_795)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _154_797 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _154_797)))
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
| _61_2211 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _154_798 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _154_798))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (

let _61_2214 = env
in {FStar_Parser_DesugarEnv.curmodule = _61_2214.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _61_2214.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _61_2214.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _61_2214.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _61_2214.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _61_2214.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _61_2214.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _61_2214.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _61_2214.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _61_2214.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _61_2214.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _154_803 = (desugar_type_binder env b)
in FStar_Util.Inl (_154_803))
end else begin
(let _154_804 = (desugar_exp_binder env b)
in FStar_Util.Inr (_154_804))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _61_2247 = (FStar_List.fold_left (fun _61_2222 b -> (match (_61_2222) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _61_2224 = b
in {FStar_Parser_AST.b = _61_2224.FStar_Parser_AST.b; FStar_Parser_AST.brange = _61_2224.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _61_2224.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _61_2234 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2234) with
| (env, a) -> begin
((env), ((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _61_2242 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_2242) with
| (env, x) -> begin
((env), ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| _61_2244 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_61_2247) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _154_811 = (desugar_typ env t)
in ((Some (x)), (_154_811)))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _154_812 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in ((None), (_154_812)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _154_813 = (desugar_typ env t)
in ((None), (_154_813)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Absyn_Syntax.tun))
end
| _61_2261 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a type)"), (b.FStar_Parser_AST.brange)))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (

let fail = (fun _61_2265 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a kind)"), (b.FStar_Parser_AST.brange)))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _154_818 = (desugar_kind env t)
in ((Some (x)), (_154_818)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _154_819 = (desugar_kind env t)
in ((None), (_154_819)))
end
| FStar_Parser_AST.TVariable (x) -> begin
((Some (x)), ((

let _61_2276 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _61_2276.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_2276.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _61_2276.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_2276.FStar_Absyn_Syntax.uvs})))
end
| _61_2279 -> begin
(fail ())
end)))


let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (

let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_61_2290, k) -> begin
(aux bs k)
end
| _61_2295 -> begin
bs
end))
in (let _154_828 = (aux tps k)
in (FStar_All.pipe_right _154_828 FStar_Absyn_Util.name_binders))))


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

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _61_2309 -> (match (_61_2309) with
| (x, _61_2308) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (let _154_849 = (let _154_848 = (let _154_847 = (let _154_846 = (let _154_845 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _154_844 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_154_845), (_154_844))))
in (FStar_Absyn_Syntax.mk_Typ_app' _154_846 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _154_847))
in (_154_848)::[])
in (FStar_List.append imp_binders _154_849))
in (

let disc_type = (let _154_852 = (let _154_851 = (let _154_850 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _154_850 p))
in ((binders), (_154_851)))
in (FStar_Absyn_Syntax.mk_Typ_fun _154_852 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _154_855 = (let _154_854 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in ((disc_name), (disc_type), (_154_854), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Absyn_Syntax.Sig_val_decl (_154_855)))))))))))))


let mk_indexed_projectors = (fun fvq refine_domain env _61_2321 lid formals t -> (match (_61_2321) with
| (tc, tps, k) -> begin
(

let binders = (gather_tc_binders tps k)
in (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (

let projectee = (let _154_866 = (FStar_Absyn_Syntax.mk_ident (("projectee"), (p)))
in (let _154_865 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _154_866; FStar_Absyn_Syntax.realname = _154_865}))
in (

let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (

let arg_binder = (

let arg_typ = (let _154_869 = (let _154_868 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _154_867 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_154_868), (_154_867))))
in (FStar_Absyn_Syntax.mk_Typ_app' _154_869 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(

let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (

let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _154_879 = (let _154_878 = (let _154_877 = (let _154_876 = (let _154_875 = (let _154_874 = (let _154_873 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _154_872 = (let _154_871 = (let _154_870 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _154_870))
in (_154_871)::[])
in ((_154_873), (_154_872))))
in (FStar_Absyn_Syntax.mk_Exp_app _154_874 None p))
in (FStar_Absyn_Util.b2t _154_875))
in ((x), (_154_876)))
in (FStar_Absyn_Syntax.mk_Typ_refine _154_877 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _154_878))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _154_879))))
end)
in (

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _61_2338 -> (match (_61_2338) with
| (x, _61_2337) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (let _154_887 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(

let _61_2349 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_61_2349) with
| (field_name, _61_2348) -> begin
(

let proj = (let _154_884 = (let _154_883 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in ((_154_883), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Typ_app _154_884 None p))
in (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _61_2356 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_61_2356) with
| (field_name, _61_2355) -> begin
(

let proj = (let _154_886 = (let _154_885 = (FStar_Absyn_Util.fvar None field_name p)
in ((_154_885), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Exp_app _154_886 None p))
in (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end))))
in (FStar_All.pipe_right _154_887 FStar_List.flatten))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _154_889 = (FStar_All.pipe_right tps (FStar_List.map (fun _61_2363 -> (match (_61_2363) with
| (b, _61_2362) -> begin
((b), (Some (imp_tag)))
end))))
in (FStar_List.append _154_889 formals))
in (let _154_919 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(

let _61_2372 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_61_2372) with
| (field_name, _61_2371) -> begin
(

let kk = (let _154_893 = (let _154_892 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in ((binders), (_154_892)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _154_893 p))
in (FStar_Absyn_Syntax.Sig_tycon (((field_name), ([]), (kk), ([]), ([]), ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inl (a.FStar_Absyn_Syntax.v)))))::[]), ((FStar_Ident.range_of_lid field_name)))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _61_2379 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_61_2379) with
| (field_name, _61_2378) -> begin
(

let t = (let _154_896 = (let _154_895 = (let _154_894 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _154_894 p))
in ((binders), (_154_895)))
in (FStar_Absyn_Syntax.mk_Typ_fun _154_896 None p))
in (

let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (

let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inr (x.FStar_Absyn_Syntax.v)))))::[]))
in (

let impl = if (((let _154_899 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _154_899)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _154_901 = (let _154_900 = (FStar_Parser_DesugarEnv.current_module env)
in _154_900.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _154_901))) then begin
[]
end else begin
(

let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (

let as_imp = (fun _61_14 -> (match (_61_14) with
| Some (FStar_Absyn_Syntax.Implicit (_61_2387)) -> begin
true
end
| _61_2391 -> begin
false
end))
in (

let arg_pats = (let _154_916 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_61_2396), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _154_909 = (let _154_908 = (let _154_907 = (let _154_906 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_154_906))
in (pos _154_907))
in ((_154_908), ((as_imp imp))))
in (_154_909)::[])
end
end
| (FStar_Util.Inr (_61_2401), imp) -> begin
if ((i + ntps) = j) then begin
(let _154_911 = (let _154_910 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in ((_154_910), ((as_imp imp))))
in (_154_911)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _154_915 = (let _154_914 = (let _154_913 = (let _154_912 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_154_912))
in (pos _154_913))
in ((_154_914), ((as_imp imp))))
in (_154_915)::[])
end
end
end))))
in (FStar_All.pipe_right _154_916 FStar_List.flatten))
in (

let pat = (let _154_918 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv lid)), (Some (fvq)), (arg_pats)))) pos)
in (let _154_917 = (FStar_Absyn_Util.bvar_to_exp projection)
in ((_154_918), (None), (_154_917))))
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
in (FStar_All.pipe_right _154_919 FStar_List.flatten))))))))))))))
end))


let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _61_17 -> (match (_61_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _61_2418, _61_2420) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_15 -> (match (_61_15) with
| FStar_Absyn_Syntax.RecordConstructor (_61_2425) -> begin
true
end
| _61_2428 -> begin
false
end)))) then begin
false
end else begin
(

let _61_2434 = tycon
in (match (_61_2434) with
| (l, _61_2431, _61_2433) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _61_2438 -> begin
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
| _61_2449 -> begin
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
| _61_2455 -> begin
[]
end))
end
| _61_2457 -> begin
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
(let _154_939 = (let _154_938 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_154_938))
in (FStar_Parser_AST.mk_term _154_939 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _61_2522 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _154_952 = (let _154_951 = (let _154_950 = (binder_to_term b)
in ((out), (_154_950), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_154_951))
in (FStar_Parser_AST.mk_term _154_952 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _61_19 -> (match (_61_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _61_2537 -> (match (_61_2537) with
| (x, t, _61_2536) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Absyn_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _154_958 = (let _154_957 = (let _154_956 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_154_956))
in (FStar_Parser_AST.mk_term _154_957 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _154_958 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _154_960 = (FStar_All.pipe_right fields (FStar_List.map (fun _61_2546 -> (match (_61_2546) with
| (x, _61_2543, _61_2545) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_154_960)))))))
end
| _61_2548 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _61_20 -> (match (_61_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _61_2562 = (typars_of_binders _env binders)
in (match (_61_2562) with
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

let tconstr = (let _154_971 = (let _154_970 = (let _154_969 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_154_969))
in (FStar_Parser_AST.mk_term _154_970 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _154_971 binders))
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
| _61_2573 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparam = (fun env _61_21 -> (match (_61_21) with
| (FStar_Util.Inr (x), _61_2580) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _61_2585) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (

let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (_61_2589))::[] -> begin
(

let tc = (FStar_List.hd tcs)
in (

let _61_2600 = (desugar_abstract_tc quals env [] tc)
in (match (_61_2600) with
| (_61_2594, _61_2596, se, _61_2599) -> begin
(

let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(

let _61_2601 = (let _154_981 = (FStar_Range.string_of_range rng)
in (let _154_980 = (let _154_979 = (let _154_978 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _154_978 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _154_979 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _154_981 _154_980)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))
end)))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _61_2614 = (typars_of_binders env binders)
in (match (_61_2614) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _61_22 -> (match (_61_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _61_2619 -> begin
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
| _61_2627 -> begin
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
in (let _154_987 = (let _154_986 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _154_985 = (FStar_All.pipe_right quals (FStar_List.filter (fun _61_24 -> (match (_61_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _61_2633 -> begin
true
end))))
in ((_154_986), (typars), (c), (_154_985), (rng))))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_154_987)))
end else begin
(

let t = (desugar_typ env' t)
in (let _154_989 = (let _154_988 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_154_988), (typars), (k), (t), (quals), (rng)))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_154_989)))
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_61_2638))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _61_2644 = (tycon_record_as_variant trec)
in (match (_61_2644) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_61_2648)::_61_2646 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _61_2659 = et
in (match (_61_2659) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_61_2661) -> begin
(

let trec = tc
in (

let _61_2666 = (tycon_record_as_variant trec)
in (match (_61_2666) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _61_2678 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_61_2678) with
| (env, _61_2675, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _61_2690 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_61_2690) with
| (env, _61_2687, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _61_2692 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _61_2695 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_61_2695) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _61_26 -> (match (_61_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _61_2702, _61_2704, _61_2706, _61_2708), t, quals) -> begin
(

let env_tps = (push_tparams env tpars)
in (

let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev (((id), (tpars), (k), (t), ([]), (rng))))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _61_2722, tags, _61_2725), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let env_tps = (push_tparams env tpars)
in (

let _61_2758 = (let _154_1005 = (FStar_All.pipe_right constrs (FStar_List.map (fun _61_2740 -> (match (_61_2740) with
| (id, topt, _61_2738, of_notation) -> begin
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

let t = (let _154_1000 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _154_999 = (close env_tps t)
in (desugar_typ _154_1000 _154_999)))
in (

let name = (FStar_Parser_DesugarEnv.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _61_25 -> (match (_61_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _61_2754 -> begin
[]
end))))
in (let _154_1004 = (let _154_1003 = (let _154_1002 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in ((name), (_154_1002), (tycon), (quals), (mutuals), (rng)))
in FStar_Absyn_Syntax.Sig_datacon (_154_1003))
in ((name), (_154_1004)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _154_1005))
in (match (_61_2758) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon (((tname), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))::constrs
end))))
end
| _61_2760 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let bundle = (let _154_1007 = (let _154_1006 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_154_1006), (rng)))
in FStar_Absyn_Syntax.Sig_bundle (_154_1007))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _61_27 -> (match (_61_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _61_2770, constrs, quals, _61_2774) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _61_2778 -> begin
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

let _61_2809 = (FStar_List.fold_left (fun _61_2787 b -> (match (_61_2787) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _61_2796 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2796) with
| (env, a) -> begin
(let _154_1016 = (let _154_1015 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_154_1015)::binders)
in ((env), (_154_1016)))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _61_2804 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_2804) with
| (env, x) -> begin
(let _154_1018 = (let _154_1017 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_154_1017)::binders)
in ((env), (_154_1018)))
end))
end
| _61_2806 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_61_2809) with
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
| (FStar_Parser_AST.Reflectable) | (FStar_Parser_AST.Reifiable) | (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Irreducible) | (FStar_Parser_AST.Noeq) | (FStar_Parser_AST.Unopteq) | (FStar_Parser_AST.Unfoldable) -> begin
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
| FStar_Parser_AST.Fsdoc (_61_2838) -> begin
((env), ([]))
end
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = FStar_Absyn_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.TopLevelModule (_61_2844) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Multiple modules in a file are no longer supported"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _154_1036 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in ((_154_1036), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(

let tcs = (FStar_List.map (fun _61_2860 -> (match (_61_2860) with
| (x, _61_2859) -> begin
x
end)) tcs)
in (let _154_1038 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _154_1038 tcs)))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _154_1040 = (let _154_1039 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _154_1039))
in _154_1040.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _61_2869) -> begin
(

let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _61_2876 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let quals = (match (quals) with
| (_61_2881)::_61_2879 -> begin
(trans_quals quals)
end
| _61_2884 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _61_30 -> (match (_61_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_61_2893); FStar_Absyn_Syntax.lbtyp = _61_2891; FStar_Absyn_Syntax.lbeff = _61_2889; FStar_Absyn_Syntax.lbdef = _61_2887} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _61_2901; FStar_Absyn_Syntax.lbeff = _61_2899; FStar_Absyn_Syntax.lbdef = _61_2897} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (

let s = FStar_Absyn_Syntax.Sig_let (((lbs), (d.FStar_Parser_AST.drange), (lids), (quals)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in ((env), ((s)::[]))))))
end
| _61_2909 -> begin
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
in (let _154_1046 = (let _154_1045 = (let _154_1044 = (let _154_1043 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_154_1043), (f), ((FStar_Absyn_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_assume (_154_1044))
in (_154_1045)::[])
in ((env), (_154_1046))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _154_1047 = (close_fun env t)
in (desugar_typ env _154_1047))
in (

let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _154_1048 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_154_1048)
end else begin
(trans_quals quals)
end
in (

let se = (let _154_1050 = (let _154_1049 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_154_1049), (t), (quals), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_val_decl (_154_1050))
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

let t = (let _154_1055 = (let _154_1054 = (let _154_1051 = (FStar_Absyn_Syntax.null_v_binder t)
in (_154_1051)::[])
in (let _154_1053 = (let _154_1052 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _154_1052))
in ((_154_1054), (_154_1053))))
in (FStar_Absyn_Syntax.mk_Typ_fun _154_1055 None d.FStar_Parser_AST.drange))
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

let _61_2962 = (desugar_binders env binders)
in (match (_61_2962) with
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
| FStar_Parser_AST.NewEffectForFree (_61_2968) -> begin
(FStar_All.failwith "effects for free only supported in conjunction with --universes")
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let env0 = env
in (

let _61_2981 = (desugar_binders env eff_binders)
in (match (_61_2981) with
| (env, binders) -> begin
(

let defn = (desugar_typ env defn)
in (

let _61_2985 = (FStar_Absyn_Util.head_and_args defn)
in (match (_61_2985) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _154_1060 = (let _154_1059 = (let _154_1058 = (let _154_1057 = (let _154_1056 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat _154_1056 " not found"))
in (Prims.strcat "Effect " _154_1057))
in ((_154_1058), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_154_1059))
in (Prims.raise _154_1060))
end
| Some (ed) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (

let sub = (FStar_Absyn_Util.subst_typ subst)
in (

let ed = (let _154_1078 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _154_1077 = (trans_quals quals)
in (let _154_1076 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _154_1075 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _154_1074 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _154_1073 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _154_1072 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _154_1071 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _154_1070 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _154_1069 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _154_1068 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _154_1067 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _154_1066 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _154_1065 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _154_1064 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _154_1063 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _154_1062 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _154_1078; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _154_1077; FStar_Absyn_Syntax.signature = _154_1076; FStar_Absyn_Syntax.ret = _154_1075; FStar_Absyn_Syntax.bind_wp = _154_1074; FStar_Absyn_Syntax.bind_wlp = _154_1073; FStar_Absyn_Syntax.if_then_else = _154_1072; FStar_Absyn_Syntax.ite_wp = _154_1071; FStar_Absyn_Syntax.ite_wlp = _154_1070; FStar_Absyn_Syntax.wp_binop = _154_1069; FStar_Absyn_Syntax.wp_as_type = _154_1068; FStar_Absyn_Syntax.close_wp = _154_1067; FStar_Absyn_Syntax.close_wp_t = _154_1066; FStar_Absyn_Syntax.assert_p = _154_1065; FStar_Absyn_Syntax.assume_p = _154_1064; FStar_Absyn_Syntax.null_wp = _154_1063; FStar_Absyn_Syntax.trivial = _154_1062})))))))))))))))))
in (

let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)
end
| _61_2997 -> begin
(let _154_1082 = (let _154_1081 = (let _154_1080 = (let _154_1079 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _154_1079 " is not an effect"))
in ((_154_1080), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_154_1081))
in (Prims.raise _154_1082))
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

let _61_3012 = (desugar_binders env eff_binders)
in (match (_61_3012) with
| (env, binders) -> begin
(

let eff_k = (desugar_kind env eff_kind)
in (

let _61_3023 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _61_3016 decl -> (match (_61_3016) with
| (env, out) -> begin
(

let _61_3020 = (desugar_decl env decl)
in (match (_61_3020) with
| (env, ses) -> begin
(let _154_1086 = (let _154_1085 = (FStar_List.hd ses)
in (_154_1085)::out)
in ((env), (_154_1086)))
end))
end)) ((env), ([]))))
in (match (_61_3023) with
| (env, decls) -> begin
(

let decls = (FStar_List.rev decls)
in (

let lookup = (fun s -> (match ((let _154_1090 = (let _154_1089 = (FStar_Absyn_Syntax.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.qualify env _154_1089))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _154_1090))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Monad " (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat " expects definition of " s)))), (d.FStar_Parser_AST.drange)))))
end
| Some (t) -> begin
t
end))
in (

let ed = (let _154_1106 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _154_1105 = (trans_quals quals)
in (let _154_1104 = (lookup "return")
in (let _154_1103 = (lookup "bind_wp")
in (let _154_1102 = (lookup "bind_wlp")
in (let _154_1101 = (lookup "if_then_else")
in (let _154_1100 = (lookup "ite_wp")
in (let _154_1099 = (lookup "ite_wlp")
in (let _154_1098 = (lookup "wp_binop")
in (let _154_1097 = (lookup "wp_as_type")
in (let _154_1096 = (lookup "close_wp")
in (let _154_1095 = (lookup "close_wp_t")
in (let _154_1094 = (lookup "assert_p")
in (let _154_1093 = (lookup "assume_p")
in (let _154_1092 = (lookup "null_wp")
in (let _154_1091 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _154_1106; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _154_1105; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _154_1104; FStar_Absyn_Syntax.bind_wp = _154_1103; FStar_Absyn_Syntax.bind_wlp = _154_1102; FStar_Absyn_Syntax.if_then_else = _154_1101; FStar_Absyn_Syntax.ite_wp = _154_1100; FStar_Absyn_Syntax.ite_wlp = _154_1099; FStar_Absyn_Syntax.wp_binop = _154_1098; FStar_Absyn_Syntax.wp_as_type = _154_1097; FStar_Absyn_Syntax.close_wp = _154_1096; FStar_Absyn_Syntax.close_wp_t = _154_1095; FStar_Absyn_Syntax.assert_p = _154_1094; FStar_Absyn_Syntax.assume_p = _154_1093; FStar_Absyn_Syntax.null_wp = _154_1092; FStar_Absyn_Syntax.trivial = _154_1091}))))))))))))))))
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
(let _154_1113 = (let _154_1112 = (let _154_1111 = (let _154_1110 = (let _154_1109 = (FStar_Absyn_Print.sli l)
in (Prims.strcat _154_1109 " not found"))
in (Prims.strcat "Effect name " _154_1110))
in ((_154_1111), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_154_1112))
in (Prims.raise _154_1113))
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
| _61_3046 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected reifiable sub-effect"), (d.FStar_Parser_AST.drange)))))
end))
in (

let lift = (let _154_1116 = (non_reifiable l.FStar_Parser_AST.lift_op)
in (desugar_typ env _154_1116))
in (

let se = FStar_Absyn_Syntax.Sig_sub_effect ((({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))))))
end)))


let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _61_3054 d -> (match (_61_3054) with
| (env, sigelts) -> begin
(

let _61_3058 = (desugar_decl env d)
in (match (_61_3058) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.fsdoc Prims.option  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]


let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let open_ns = (fun mname d -> (

let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _154_1141 = (let _154_1140 = (let _154_1138 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_154_1138))
in (let _154_1139 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _154_1140 _154_1139 None)))
in (_154_1141)::d)
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

let _61_3085 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _154_1143 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _154_1142 = (open_ns mname decls)
in ((_154_1143), (mname), (_154_1142), (true))))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _154_1145 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _154_1144 = (open_ns mname decls)
in ((_154_1145), (mname), (_154_1144), (false))))
end)
in (match (_61_3085) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _61_3088 = (desugar_decls env decls)
in (match (_61_3088) with
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
| FStar_Parser_AST.Interface (mname, _61_3099, _61_3101) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _61_3109 = (desugar_modul_common curmod env m)
in (match (_61_3109) with
| (x, y, _61_3108) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (

let _61_3115 = (desugar_modul_common None env m)
in (match (_61_3115) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (

let _61_3117 = if (FStar_Options.dump_module modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _154_1156 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _154_1156))
end else begin
()
end
in (let _154_1157 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in ((_154_1157), (modul)))))
end)))


let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (

let _61_3130 = (FStar_List.fold_left (fun _61_3123 m -> (match (_61_3123) with
| (env, mods) -> begin
(

let _61_3127 = (desugar_modul env m)
in (match (_61_3127) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_61_3130) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (

let _61_3135 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_61_3135) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (

let _61_3136 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _61_3136.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _61_3136.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _61_3136.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _61_3136.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _61_3136.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _61_3136.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _61_3136.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _61_3136.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _61_3136.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _61_3136.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _61_3136.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))





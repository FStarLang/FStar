
open Prims

let imp_tag : FStar_Absyn_Syntax.arg_qualifier = FStar_Absyn_Syntax.Implicit (false)


let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _62_1 -> (match (_62_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (imp_tag)
end
| _62_36 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (imp_tag)))
end
| _62_43 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_62_47) -> begin
true
end
| _62_50 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _62_55 -> begin
t
end))


let rec unlabel : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _62_61, _62_63) -> begin
(unlabel t)
end
| _62_67 -> begin
t
end))


let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _156_17 = (let _156_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_156_16))
in (FStar_Parser_AST.mk_term _156_17 r FStar_Parser_AST.Kind)))


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _62_2 -> (match (_62_2) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' when (arity = (Prims.parse_int "1")) -> begin
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
| _62_90 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _156_28 = (let _156_26 = (FStar_Util.char_at s i)
in (name_of_char _156_26))
in (let _156_27 = (aux (i + (Prims.parse_int "1")))
in (_156_28)::_156_27))
end)
in (let _156_30 = (let _156_29 = (aux (Prims.parse_int "0"))
in (FStar_String.concat "_" _156_29))
in (Prims.strcat "op_" _156_30)))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _156_40 = (let _156_39 = (let _156_38 = (let _156_37 = (compile_op n s)
in ((_156_37), (r)))
in (FStar_Absyn_Syntax.mk_ident _156_38))
in (_156_39)::[])
in (FStar_All.pipe_right _156_40 FStar_Absyn_Syntax.lid_of_ids)))


let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (

let r = (fun l -> Some ((FStar_Ident.set_lid_range l rng)))
in (

let fallback = (fun _62_104 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Absyn_Const.op_Eq)
end
| ":=" -> begin
(r FStar_Absyn_Const.write_lid)
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
| "-" when (arity = (Prims.parse_int "1")) -> begin
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
| _62_126 -> begin
None
end)
end))
in (match ((let _156_53 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _156_53))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _62_137); FStar_Absyn_Syntax.tk = _62_134; FStar_Absyn_Syntax.pos = _62_132; FStar_Absyn_Syntax.fvs = _62_130; FStar_Absyn_Syntax.uvs = _62_128}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _62_143 -> begin
(fallback ())
end))))


let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (

let r = (fun l -> Some ((FStar_Ident.set_lid_range l rng)))
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
(match ((let _156_64 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _156_64))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _62_166; FStar_Absyn_Syntax.pos = _62_164; FStar_Absyn_Syntax.fvs = _62_162; FStar_Absyn_Syntax.uvs = _62_160}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _62_172 -> begin
None
end)
end)))


let rec is_type : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _156_71 = (unparen t)
in _156_71.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_62_177) -> begin
true
end
| FStar_Parser_AST.Op ("*", (hd)::_62_181) -> begin
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
| _62_232 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = (Prims.parse_int "0")) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_62_255) -> begin
true
end
| _62_258 -> begin
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
| FStar_Parser_AST.Product (_62_299, t) -> begin
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
| FStar_Parser_AST.PatTvar (id, _62_325) -> begin
(

let _62_331 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_62_331) with
| (env, _62_330) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(

let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _156_76 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _156_76 Prims.fst))
end
| _62_346 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _62_349 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_62_354); FStar_Parser_AST.prange = _62_352}, _62_358))::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_62_370); FStar_Parser_AST.prange = _62_368}, _62_374); FStar_Parser_AST.prange = _62_366}, _62_379))::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_62_389); FStar_Parser_AST.prange = _62_387}, _62_393))::[], t) -> begin
(is_type env t)
end
| _62_400 -> begin
false
end)
end)
and is_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _156_79 = (unparen t)
in _156_79.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _62_409; FStar_Ident.ident = _62_407; FStar_Ident.nsstr = _62_405; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_62_413, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _62_426 -> begin
false
end)
end)


let rec is_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  Prims.bool = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_62_430) -> begin
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
| FStar_Parser_AST.Variable (_62_445) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected binder without annotation"), (b.FStar_Parser_AST.brange)))))
end
| FStar_Parser_AST.TVariable (_62_448) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_62_451) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _156_90 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _156_90)))


let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_62_467) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _62_474 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_62_474) with
| (env, _62_473) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_62_476, term) -> begin
(let _156_97 = (free_type_vars env term)
in ((env), (_156_97)))
end
| FStar_Parser_AST.TAnnotated (id, _62_482) -> begin
(

let _62_488 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_62_488) with
| (env, _62_487) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _156_98 = (free_type_vars env t)
in ((env), (_156_98)))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _156_101 = (unparen t)
in _156_101.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _62_497 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_62_533, ts) -> begin
(FStar_List.collect (fun _62_540 -> (match (_62_540) with
| (t, _62_539) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_62_542, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _62_549) -> begin
(let _156_104 = (free_type_vars env t1)
in (let _156_103 = (free_type_vars env t2)
in (FStar_List.append _156_104 _156_103)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _62_558 = (free_type_vars_b env b)
in (match (_62_558) with
| (env, f) -> begin
(let _156_105 = (free_type_vars env t)
in (FStar_List.append f _156_105))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _62_574 = (FStar_List.fold_left (fun _62_567 binder -> (match (_62_567) with
| (env, free) -> begin
(

let _62_571 = (free_type_vars_b env binder)
in (match (_62_571) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_62_574) with
| (env, free) -> begin
(let _156_108 = (free_type_vars env body)
in (FStar_List.append free _156_108))
end))
end
| FStar_Parser_AST.Project (t, _62_577) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _156_115 = (unparen t)
in _156_115.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _62_627 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _156_120 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _156_120))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _156_124 = (let _156_123 = (let _156_122 = (kind_star x.FStar_Ident.idRange)
in ((x), (_156_122)))
in FStar_Parser_AST.TAnnotated (_156_123))
in (FStar_Parser_AST.mk_binder _156_124 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _156_129 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _156_129))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _156_133 = (let _156_132 = (let _156_131 = (kind_star x.FStar_Ident.idRange)
in ((x), (_156_131)))
in FStar_Parser_AST.TAnnotated (_156_132))
in (FStar_Parser_AST.mk_binder _156_133 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _156_134 = (unlabel t)
in _156_134.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_62_640) -> begin
t
end
| _62_643 -> begin
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
| _62_653 -> begin
((bs), (t))
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _62_657) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_62_663); FStar_Parser_AST.prange = _62_661}, _62_667) -> begin
true
end
| _62_671 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _62_683 = (destruct_app_pattern env is_top_level p)
in (match (_62_683) with
| (name, args, _62_682) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _62_688); FStar_Parser_AST.prange = _62_685}, args) when is_top_level -> begin
(let _156_148 = (let _156_147 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_156_147))
in ((_156_148), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _62_699); FStar_Parser_AST.prange = _62_696}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _62_707 -> begin
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
| TBinder (_62_710) -> begin
_62_710
end))


let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_62_713) -> begin
_62_713
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_62_716) -> begin
_62_716
end))


let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _62_3 -> (match (_62_3) with
| TBinder (a, k, aq) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), (aq))
end
| VBinder (x, t, aq) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (aq))
end
| _62_729 -> begin
(FStar_All.failwith "Impossible")
end))


let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _62_4 -> (match (_62_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _62_736 -> begin
None
end))


let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either  ->  (FStar_Absyn_Syntax.binder * FStar_Parser_DesugarEnv.env) = (fun env imp _62_5 -> (match (_62_5) with
| FStar_Util.Inl (None, k) -> begin
(let _156_201 = (FStar_Absyn_Syntax.null_t_binder k)
in ((_156_201), (env)))
end
| FStar_Util.Inr (None, t) -> begin
(let _156_202 = (FStar_Absyn_Syntax.null_v_binder t)
in ((_156_202), (env)))
end
| FStar_Util.Inl (Some (a), k) -> begin
(

let _62_755 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_62_755) with
| (env, a) -> begin
((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual imp)))), (env))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _62_763 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_763) with
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
| _62_773 -> begin
(let _156_213 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _156_213))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (((f), (msg), (polarity)))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (

let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _156_217 = (let _156_216 = (aux g)
in FStar_Parser_AST.Paren (_156_216))
in (FStar_Parser_AST.mk_term _156_217 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", (f1)::(f2)::[]) -> begin
(let _156_223 = (let _156_222 = (let _156_221 = (let _156_220 = (aux f1)
in (let _156_219 = (let _156_218 = (aux f2)
in (_156_218)::[])
in (_156_220)::_156_219))
in (("/\\"), (_156_221)))
in FStar_Parser_AST.Op (_156_222))
in (FStar_Parser_AST.mk_term _156_223 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _156_227 = (let _156_226 = (let _156_225 = (aux f2)
in (let _156_224 = (aux f3)
in ((f1), (_156_225), (_156_224))))
in FStar_Parser_AST.If (_156_226))
in (FStar_Parser_AST.mk_term _156_227 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _156_230 = (let _156_229 = (let _156_228 = (aux g)
in ((binders), (_156_228)))
in FStar_Parser_AST.Abs (_156_229))
in (FStar_Parser_AST.mk_term _156_230 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _62_795 -> begin
(label f)
end))
in (aux f))))


let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _62_799 -> (match (_62_799) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))


let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _62_6 -> (match (_62_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _62_810 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
((l), (e), (y))
end
| _62_815 -> begin
(

let _62_818 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_62_818) with
| (e, x) -> begin
(((FStar_Util.Inr (x))::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _62_7 -> (match (_62_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _62_827 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
((l), (e), (b))
end
| _62_832 -> begin
(

let _62_835 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_62_835) with
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
| FStar_Parser_AST.PatOp (_62_846) -> begin
(FStar_All.failwith "let op not supported in stratified")
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _62_860 = (aux loc env p)
in (match (_62_860) with
| (loc, env, var, p, _62_859) -> begin
(

let _62_877 = (FStar_List.fold_left (fun _62_864 p -> (match (_62_864) with
| (loc, env, ps) -> begin
(

let _62_873 = (aux loc env p)
in (match (_62_873) with
| (loc, env, _62_869, p, _62_872) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_62_877) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (

let _62_879 = (let _156_302 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _156_302))
in ((loc), (env), (var), (pat), (false))))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_62_886) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(

let _62_892 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (((x), (imp))); FStar_Parser_AST.prange = _62_892.FStar_Parser_AST.prange})
end
| _62_895 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
p
end
in (

let _62_902 = (aux loc env p)
in (match (_62_902) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_62_904) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _62_908, aq) -> begin
(let _156_304 = (let _156_303 = (desugar_kind env t)
in ((x), (_156_303), (aq)))
in TBinder (_156_304))
end
| VBinder (x, _62_914, aq) -> begin
(

let t = (close_fun env t)
in (let _156_306 = (let _156_305 = (desugar_typ env t)
in ((x), (_156_305), (aq)))
in VBinder (_156_306)))
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
in (let _156_307 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((a), (FStar_Absyn_Syntax.kun), (aq)))), (_156_307), (imp))))
end else begin
(

let _62_930 = (resolvea loc env a)
in (match (_62_930) with
| (loc, env, abvd) -> begin
(let _156_308 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((abvd), (FStar_Absyn_Syntax.kun), (aq)))), (_156_308), (imp)))
end))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (

let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _156_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_156_309), (false)))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _156_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_156_310), (false))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _62_946 = (resolvex loc env x)
in (match (_62_946) with
| (loc, env, xbvd) -> begin
(let _156_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((xbvd), (FStar_Absyn_Syntax.tun), (aq)))), (_156_311), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _156_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), ([])))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_156_312), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _62_952}, args) -> begin
(

let _62_974 = (FStar_List.fold_right (fun arg _62_963 -> (match (_62_963) with
| (loc, env, args) -> begin
(

let _62_970 = (aux loc env arg)
in (match (_62_970) with
| (loc, env, _62_967, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_62_974) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _156_315 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_156_315), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_62_978) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _62_998 = (FStar_List.fold_right (fun pat _62_986 -> (match (_62_986) with
| (loc, env, pats) -> begin
(

let _62_994 = (aux loc env pat)
in (match (_62_994) with
| (loc, env, _62_990, pat, _62_993) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_62_998) with
| (loc, env, pats) -> begin
(

let pat = (let _156_322 = (let _156_321 = (let _156_320 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _156_320))
in (FStar_All.pipe_left _156_321 (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ([]))))))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((hd), (false)))::(((tl), (false)))::[]))))))) pats _156_322))
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _62_1024 = (FStar_List.fold_left (fun _62_1011 p -> (match (_62_1011) with
| (loc, env, pats) -> begin
(

let _62_1020 = (aux loc env p)
in (match (_62_1020) with
| (loc, env, _62_1016, pat, _62_1019) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_62_1024) with
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
| FStar_Absyn_Syntax.Exp_fvar (v, _62_1030) -> begin
v
end
| _62_1034 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _156_325 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_156_325), (false))))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _62_1044 = (FStar_List.hd fields)
in (match (_62_1044) with
| (f, _62_1043) -> begin
(

let _62_1048 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_62_1048) with
| (record, _62_1047) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _62_1051 -> (match (_62_1051) with
| (f, p) -> begin
(let _156_327 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in ((_156_327), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _62_1056 -> (match (_62_1056) with
| (f, _62_1055) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _62_1060 -> (match (_62_1060) with
| (g, _62_1059) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_62_1063, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _62_1075 = (aux loc env app)
in (match (_62_1075) with
| (env, e, b, p, _62_1074) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _62_1078, args) -> begin
(let _156_335 = (let _156_334 = (let _156_333 = (let _156_332 = (let _156_331 = (let _156_330 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_156_330)))
in FStar_Absyn_Syntax.Record_ctor (_156_331))
in Some (_156_332))
in ((fv), (_156_333), (args)))
in FStar_Absyn_Syntax.Pat_cons (_156_334))
in (FStar_All.pipe_left pos _156_335))
end
| _62_1083 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _62_1092 = (aux [] env p)
in (match (_62_1092) with
| (_62_1086, env, b, p, _62_1091) -> begin
((env), (b), (p))
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _62_1098) -> begin
(let _156_341 = (let _156_340 = (let _156_339 = (FStar_Parser_DesugarEnv.qualify env x)
in ((_156_339), (FStar_Absyn_Syntax.tun)))
in LetBinder (_156_340))
in ((env), (_156_341), (None)))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _62_1105); FStar_Parser_AST.prange = _62_1102}, t) -> begin
(let _156_345 = (let _156_344 = (let _156_343 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _156_342 = (desugar_typ env t)
in ((_156_343), (_156_342))))
in LetBinder (_156_344))
in ((env), (_156_345), (None)))
end
| _62_1113 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _62_1117 = (desugar_data_pat env p)
in (match (_62_1117) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _62_1128 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _62_1132 env pat -> (

let _62_1140 = (desugar_data_pat env pat)
in (match (_62_1140) with
| (env, _62_1138, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _156_355 = (desugar_typ env t)
in FStar_Util.Inl (_156_355))
end else begin
(let _156_356 = (desugar_exp env t)
in FStar_Util.Inr (_156_356))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (

let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _62_1154 = e
in {FStar_Absyn_Syntax.n = _62_1154.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_1154.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _62_1154.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_1154.FStar_Absyn_Syntax.uvs}))
in (match ((let _156_376 = (unparen top)
in _156_376.FStar_Parser_AST.tm)) with
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

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _156_380 = (desugar_typ_or_exp env t)
in ((_156_380), (None))))))
in (let _156_381 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _156_381))))
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
(let _156_382 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _156_382))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let dt = (let _156_387 = (let _156_386 = (let _156_385 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in ((_156_385), (Some (FStar_Absyn_Syntax.Data_ctor))))
in (FStar_Absyn_Syntax.mk_Exp_fvar _156_386))
in (FStar_All.pipe_left pos _156_387))
in (match (args) with
| [] -> begin
dt
end
| _62_1181 -> begin
(

let args = (FStar_List.map (fun _62_1184 -> (match (_62_1184) with
| (t, imp) -> begin
(

let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _156_392 = (let _156_391 = (let _156_390 = (let _156_389 = (FStar_Absyn_Util.mk_exp_app dt args)
in ((_156_389), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_156_390))
in (FStar_Absyn_Syntax.mk_Exp_meta _156_391))
in (FStar_All.pipe_left setpos _156_392)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _62_1221 = (FStar_List.fold_left (fun _62_1193 pat -> (match (_62_1193) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _62_1196}, t) -> begin
(

let ftvs = (let _156_395 = (free_type_vars env t)
in (FStar_List.append _156_395 ftvs))
in (let _156_397 = (let _156_396 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _156_396))
in ((_156_397), (ftvs))))
end
| FStar_Parser_AST.PatTvar (a, _62_1208) -> begin
(let _156_399 = (let _156_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _156_398))
in ((_156_399), (ftvs)))
end
| FStar_Parser_AST.PatAscribed (_62_1212, t) -> begin
(let _156_401 = (let _156_400 = (free_type_vars env t)
in (FStar_List.append _156_400 ftvs))
in ((env), (_156_401)))
end
| _62_1217 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_62_1221) with
| (_62_1219, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _156_403 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _156_403 binders))
in (

let rec aux = (fun env bs sc_pat_opt _62_8 -> (match (_62_8) with
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

let _62_1244 = (desugar_binding_pat env p)
in (match (_62_1244) with
| (env, b, pat) -> begin
(

let _62_1304 = (match (b) with
| LetBinder (_62_1246) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _156_412 = (binder_of_bnd b)
in ((_156_412), (sc_pat_opt)))
end
| VBinder (x, t, aq) -> begin
(

let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _62_1261) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _156_414 = (let _156_413 = (FStar_Absyn_Util.bvar_to_exp b)
in ((_156_413), (p)))
in Some (_156_414))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Absyn_Syntax.n), (p'.FStar_Absyn_Syntax.v))) with
| (FStar_Absyn_Syntax.Exp_bvar (_62_1275), _62_1278) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (

let sc = (let _156_421 = (let _156_420 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _156_419 = (let _156_418 = (FStar_Absyn_Syntax.varg sc)
in (let _156_417 = (let _156_416 = (let _156_415 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _156_415))
in (_156_416)::[])
in (_156_418)::_156_417))
in ((_156_420), (_156_419))))
in (FStar_Absyn_Syntax.mk_Exp_app _156_421 None top.FStar_Parser_AST.range))
in (

let p = (let _156_422 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((p'), (false)))::(((p), (false)))::[])))) None _156_422))
in Some (((sc), (p))))))
end
| (FStar_Absyn_Syntax.Exp_app (_62_1284, args), FStar_Absyn_Syntax.Pat_cons (_62_1289, _62_1291, pats)) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (

let sc = (let _156_428 = (let _156_427 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _156_426 = (let _156_425 = (let _156_424 = (let _156_423 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _156_423))
in (_156_424)::[])
in (FStar_List.append args _156_425))
in ((_156_427), (_156_426))))
in (FStar_Absyn_Syntax.mk_Exp_app _156_428 None top.FStar_Parser_AST.range))
in (

let p = (let _156_429 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((FStar_List.append pats ((((p), (false)))::[])))))) None _156_429))
in Some (((sc), (p))))))
end
| _62_1300 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((FStar_Util.Inr (b)), (aq))), (sc_pat_opt))))
end)
in (match (_62_1304) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _62_1308; FStar_Parser_AST.level = _62_1306}, arg, _62_1314) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env arg)
in (let _156_439 = (let _156_438 = (let _156_437 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _156_436 = (let _156_435 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _156_434 = (let _156_433 = (let _156_432 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _156_432))
in (_156_433)::[])
in (_156_435)::_156_434))
in ((_156_437), (_156_436))))
in (FStar_Absyn_Syntax.mk_Exp_app _156_438))
in (FStar_All.pipe_left pos _156_439)))
end
| FStar_Parser_AST.App (_62_1319) -> begin
(

let rec aux = (fun args e -> (match ((let _156_444 = (unparen e)
in _156_444.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _156_445 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _156_445))
in (aux ((arg)::args) e))
end
| _62_1331 -> begin
(

let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app ((head), (args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _156_451 = (let _156_450 = (let _156_449 = (let _156_448 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_156_448), (FStar_Absyn_Syntax.Sequence)))
in FStar_Absyn_Syntax.Meta_desugared (_156_449))
in (FStar_Absyn_Syntax.mk_Exp_meta _156_450))
in (FStar_All.pipe_left setpos _156_451))
end
| FStar_Parser_AST.LetOpen (_62_1338) -> begin
(FStar_All.failwith "let open in universes")
end
| FStar_Parser_AST.Let (is_rec, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (is_rec = FStar_Parser_AST.Rec)
in (

let ds_let_rec = (fun _62_1351 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _62_1355 -> (match (_62_1355) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _156_455 = (destruct_app_pattern env top_level p)
in ((_156_455), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _156_456 = (destruct_app_pattern env top_level p)
in ((_156_456), (def)))
end
| _62_1361 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _62_1366); FStar_Parser_AST.prange = _62_1363}, t) -> begin
if top_level then begin
(let _156_459 = (let _156_458 = (let _156_457 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_156_457))
in ((_156_458), ([]), (Some (t))))
in ((_156_459), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _62_1375) -> begin
if top_level then begin
(let _156_462 = (let _156_461 = (let _156_460 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_156_460))
in ((_156_461), ([]), (None)))
in ((_156_462), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _62_1379 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _62_1405 = (FStar_List.fold_left (fun _62_1383 _62_1392 -> (match (((_62_1383), (_62_1392))) with
| ((env, fnames), ((f, _62_1386, _62_1388), _62_1391)) -> begin
(

let _62_1402 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _62_1397 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_1397) with
| (env, xx) -> begin
((env), (FStar_Util.Inl (xx)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _156_465 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in ((_156_465), (FStar_Util.Inr (l))))
end)
in (match (_62_1402) with
| (env, lbname) -> begin
((env), ((lbname)::fnames))
end))
end)) ((env), ([])) funs)
in (match (_62_1405) with
| (env', fnames) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _62_1416 -> (match (_62_1416) with
| ((_62_1411, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _156_472 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _156_472 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _62_1423 -> begin
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

let _62_1436 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_62_1436) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_62_1438) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(

let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]))), (body)))))
end
| VBinder (x, t, _62_1448) -> begin
(

let body = (desugar_exp env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _156_484 = (let _156_483 = (FStar_Absyn_Util.bvd_to_exp x t)
in ((_156_483), ((((pat), (None), (body)))::[])))
in (FStar_Absyn_Syntax.mk_Exp_match _156_484 None body.FStar_Absyn_Syntax.pos))
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
(let _156_497 = (let _156_496 = (let _156_495 = (desugar_exp env t1)
in (let _156_494 = (let _156_493 = (let _156_489 = (desugar_exp env t2)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range)), (None), (_156_489)))
in (let _156_492 = (let _156_491 = (let _156_490 = (desugar_exp env t3)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range)), (None), (_156_490)))
in (_156_491)::[])
in (_156_493)::_156_492))
in ((_156_495), (_156_494))))
in (FStar_Absyn_Syntax.mk_Exp_match _156_496))
in (FStar_All.pipe_left pos _156_497))
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

let desugar_branch = (fun _62_1487 -> (match (_62_1487) with
| (pat, wopt, b) -> begin
(

let _62_1490 = (desugar_match_pat env pat)
in (match (_62_1490) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _156_500 = (desugar_exp env e)
in Some (_156_500))
end)
in (

let b = (desugar_exp env b)
in ((pat), (wopt), (b))))
end))
end))
in (let _156_506 = (let _156_505 = (let _156_504 = (desugar_exp env e)
in (let _156_503 = (FStar_List.map desugar_branch branches)
in ((_156_504), (_156_503))))
in (FStar_Absyn_Syntax.mk_Exp_match _156_505))
in (FStar_All.pipe_left pos _156_506)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _156_512 = (let _156_511 = (let _156_510 = (desugar_exp env e)
in (let _156_509 = (desugar_typ env t)
in ((_156_510), (_156_509), (None))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _156_511))
in (FStar_All.pipe_left pos _156_512))
end
| FStar_Parser_AST.Record (_62_1501, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _62_1512 = (FStar_List.hd fields)
in (match (_62_1512) with
| (f, _62_1511) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _62_1518 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_62_1518) with
| (record, _62_1517) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _62_1526 -> (match (_62_1526) with
| (g, _62_1525) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_62_1530, e) -> begin
(let _156_520 = (qfn fn)
in ((_156_520), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _156_523 = (let _156_522 = (let _156_521 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_156_521), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_156_522))
in (Prims.raise _156_523))
end
| Some (x) -> begin
(let _156_524 = (qfn fn)
in ((_156_524), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _156_529 = (let _156_528 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _62_1542 -> (match (_62_1542) with
| (f, _62_1541) -> begin
(let _156_527 = (let _156_526 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _156_526))
in ((_156_527), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_DesugarEnv.constrname), (_156_528)))
in FStar_Parser_AST.Construct (_156_529))
end
| Some (e) -> begin
(

let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (

let xterm = (let _156_531 = (let _156_530 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_156_530))
in (FStar_Parser_AST.mk_term _156_531 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _156_534 = (let _156_533 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _62_1550 -> (match (_62_1550) with
| (f, _62_1549) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_156_533)))
in FStar_Parser_AST.Record (_156_534))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _62_1573); FStar_Absyn_Syntax.tk = _62_1570; FStar_Absyn_Syntax.pos = _62_1568; FStar_Absyn_Syntax.fvs = _62_1566; FStar_Absyn_Syntax.uvs = _62_1564}, args); FStar_Absyn_Syntax.tk = _62_1562; FStar_Absyn_Syntax.pos = _62_1560; FStar_Absyn_Syntax.fvs = _62_1558; FStar_Absyn_Syntax.uvs = _62_1556}, FStar_Absyn_Syntax.Data_app)) -> begin
(

let e = (let _156_544 = (let _156_543 = (let _156_542 = (let _156_541 = (let _156_540 = (let _156_539 = (let _156_538 = (let _156_537 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_156_537)))
in FStar_Absyn_Syntax.Record_ctor (_156_538))
in Some (_156_539))
in ((fv), (_156_540)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _156_541 None e.FStar_Absyn_Syntax.pos))
in ((_156_542), (args)))
in (FStar_Absyn_Syntax.mk_Exp_app _156_543))
in (FStar_All.pipe_left pos _156_544))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (FStar_Absyn_Syntax.Data_app))))))
end
| _62_1587 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _62_1594 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_62_1594) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_exp env e)
in (

let fn = (

let _62_1599 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_62_1599) with
| (ns, _62_1598) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _156_551 = (let _156_550 = (let _156_549 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (let _156_548 = (let _156_547 = (FStar_Absyn_Syntax.varg e)
in (_156_547)::[])
in ((_156_549), (_156_548))))
in (FStar_Absyn_Syntax.mk_Exp_app _156_550))
in (FStar_All.pipe_left pos _156_551)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _62_1605 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (

let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _62_1612 = t
in {FStar_Absyn_Syntax.n = _62_1612.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_1612.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _62_1612.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_1612.FStar_Absyn_Syntax.uvs}))
in (

let top = (unparen top)
in (

let head_and_args = (fun t -> (

let rec aux = (fun args t -> (match ((let _156_574 = (unparen t)
in _156_574.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _62_1630 -> begin
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
(let _156_575 = (desugar_exp env t)
in (FStar_All.pipe_right _156_575 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _156_576 = (desugar_exp env t)
in (FStar_All.pipe_right _156_576 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", (t1)::(_62_1644)::[]) -> begin
if (is_type env t1) then begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _156_579 = (flatten t1)
in (FStar_List.append _156_579 ((t2)::[])))
end
| _62_1658 -> begin
(t)::[]
end))
in (

let targs = (let _156_582 = (flatten top)
in (FStar_All.pipe_right _156_582 (FStar_List.map (fun t -> (let _156_581 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _156_581))))))
in (

let tup = (let _156_583 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _156_583))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))))
end else begin
(let _156_589 = (let _156_588 = (let _156_587 = (let _156_586 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _156_586))
in ((_156_587), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_156_588))
in (Prims.raise _156_589))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _156_590 = (desugar_exp env top)
in (FStar_All.pipe_right _156_590 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(

let args = (FStar_List.map (fun t -> (let _156_592 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _156_592))) args)
in (let _156_593 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _156_593 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _156_594 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _156_594))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = (Prims.parse_int "0")) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _156_595 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _156_595))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _156_596 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _156_596)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let t = (let _156_597 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _156_597))
in (

let args = (FStar_List.map (fun _62_1694 -> (match (_62_1694) with
| (t, imp) -> begin
(let _156_599 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _156_599))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let rec aux = (fun env bs _62_9 -> (match (_62_9) with
| [] -> begin
(

let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_List.rev bs)), (body)))))
end
| (hd)::tl -> begin
(

let _62_1712 = (desugar_binding_pat env hd)
in (match (_62_1712) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _156_611 = (let _156_610 = (let _156_609 = (let _156_608 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _156_608))
in ((_156_609), (hd.FStar_Parser_AST.prange)))
in FStar_Absyn_Syntax.Error (_156_610))
in (Prims.raise _156_611))
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
| FStar_Parser_AST.App (_62_1718) -> begin
(

let rec aux = (fun args e -> (match ((let _156_616 = (unparen e)
in _156_616.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(

let arg = (let _156_617 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _156_617))
in (aux ((arg)::args) e))
end
| _62_1730 -> begin
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

let _62_1742 = (uncurry binders t)
in (match (_62_1742) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _62_10 -> (match (_62_10) with
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

let _62_1756 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_62_1756) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _62_1763) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _62_1777 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _62_1769), env) -> begin
((x), (env))
end
| _62_1774 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_62_1777) with
| (b, env) -> begin
(

let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _156_628 = (desugar_exp env f)
in (FStar_All.pipe_right _156_628 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine ((b), (f)))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _156_636 = (let _156_635 = (let _156_634 = (desugar_typ env t)
in (let _156_633 = (desugar_kind env k)
in ((_156_634), (_156_633))))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _156_635))
in (FStar_All.pipe_left wpos _156_636))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _62_1811 = (FStar_List.fold_left (fun _62_1796 b -> (match (_62_1796) with
| (env, tparams, typs) -> begin
(

let _62_1800 = (desugar_exp_binder env b)
in (match (_62_1800) with
| (xopt, t) -> begin
(

let _62_1806 = (match (xopt) with
| None -> begin
(let _156_639 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in ((env), (_156_639)))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_62_1806) with
| (env, x) -> begin
(let _156_643 = (let _156_642 = (let _156_641 = (let _156_640 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _156_640))
in (_156_641)::[])
in (FStar_List.append typs _156_642))
in ((env), ((FStar_List.append tparams ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (None)))::[]))), (_156_643)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_62_1811) with
| (env, _62_1809, targs) -> begin
(

let tup = (let _156_644 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _156_644))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))
end))
end
| FStar_Parser_AST.Record (_62_1814) -> begin
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
| _62_1833 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _62_1835 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r))))))
in (

let pre_process_comp_typ = (fun t -> (

let _62_1846 = (head_and_args t)
in (match (_62_1846) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let _62_1872 = (FStar_All.pipe_right args (FStar_List.partition (fun _62_1854 -> (match (_62_1854) with
| (arg, _62_1853) -> begin
(match ((let _156_656 = (unparen arg)
in _156_656.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _62_1858; FStar_Parser_AST.level = _62_1856}, _62_1863, _62_1865) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _62_1869 -> begin
false
end)
end))))
in (match (_62_1872) with
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
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _156_657 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _156_657 FStar_Absyn_Const.prims_lid))) -> begin
(

let args = (FStar_List.map (fun _62_1887 -> (match (_62_1887) with
| (t, imp) -> begin
(let _156_659 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _156_659))
end)) args)
in (let _156_660 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _156_660 args)))
end
| _62_1890 -> begin
(desugar_typ env t)
end)
end)))
in (

let t = (pre_process_comp_typ t)
in (

let _62_1894 = (FStar_Absyn_Util.head_and_args t)
in (match (_62_1894) with
| (head, args) -> begin
(match ((let _156_662 = (let _156_661 = (FStar_Absyn_Util.compress_typ head)
in _156_661.FStar_Absyn_Syntax.n)
in ((_156_662), (args)))) with
| (FStar_Absyn_Syntax.Typ_const (eff), ((FStar_Util.Inl (result_typ), _62_1901))::rest) -> begin
(

let _62_1941 = (FStar_All.pipe_right rest (FStar_List.partition (fun _62_11 -> (match (_62_11) with
| (FStar_Util.Inr (_62_1907), _62_1910) -> begin
false
end
| (FStar_Util.Inl (t), _62_1915) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _62_1924; FStar_Absyn_Syntax.pos = _62_1922; FStar_Absyn_Syntax.fvs = _62_1920; FStar_Absyn_Syntax.uvs = _62_1918}, ((FStar_Util.Inr (_62_1929), _62_1932))::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _62_1938 -> begin
false
end)
end))))
in (match (_62_1941) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _62_12 -> (match (_62_12) with
| (FStar_Util.Inl (t), _62_1946) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_62_1949, ((FStar_Util.Inr (arg), _62_1953))::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _62_1959 -> begin
(FStar_All.failwith "impos")
end)
end
| _62_1961 -> begin
(FStar_All.failwith "impos")
end))))
in if ((FStar_Parser_DesugarEnv.is_effect_name env eff.FStar_Absyn_Syntax.v) || (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid)) then begin
if ((FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = (Prims.parse_int "0"))) then begin
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
(let _156_669 = (let _156_668 = (let _156_667 = (let _156_666 = (let _156_665 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((pat), (FStar_Absyn_Syntax.Meta_smt_pat)))))
in FStar_Util.Inr (_156_665))
in ((_156_666), (aq)))
in (_156_667)::[])
in (ens)::_156_668)
in (req)::_156_669)
end
| _62_1972 -> begin
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
(let _156_671 = (let _156_670 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _156_670))
in (fail _156_671))
end
end)
end))
end
| _62_1975 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _156_673 = (let _156_672 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _156_672))
in (fail _156_673))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (

let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (

let setpos = (fun kk -> (

let _62_1982 = kk
in {FStar_Absyn_Syntax.n = _62_1982.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_1982.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _62_1982.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_1982.FStar_Absyn_Syntax.uvs}))
in (

let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _62_1991; FStar_Ident.ident = _62_1989; FStar_Ident.nsstr = _62_1987; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _62_2000; FStar_Ident.ident = _62_1998; FStar_Ident.nsstr = _62_1996; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _156_685 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _156_685))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), ([]))), (FStar_Absyn_Syntax.mk_Kind_unknown))))
end
| _62_2008 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(

let _62_2016 = (uncurry bs k)
in (match (_62_2016) with
| (bs, k) -> begin
(

let rec aux = (fun env bs _62_13 -> (match (_62_13) with
| [] -> begin
(let _156_696 = (let _156_695 = (let _156_694 = (desugar_kind env k)
in (((FStar_List.rev bs)), (_156_694)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _156_695))
in (FStar_All.pipe_left pos _156_696))
end
| (hd)::tl -> begin
(

let _62_2027 = (let _156_698 = (let _156_697 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _156_697 hd))
in (FStar_All.pipe_right _156_698 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_62_2027) with
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

let args = (FStar_List.map (fun _62_2037 -> (match (_62_2037) with
| (t, b) -> begin
(

let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _156_700 = (desugar_typ_or_exp env t)
in ((_156_700), (qual))))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (FStar_Absyn_Syntax.mk_Kind_unknown)))))
end)
end
| _62_2041 -> begin
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
| _62_2052 -> begin
None
end))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _62_2057 = t
in {FStar_Absyn_Syntax.n = _62_2057.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_2057.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _62_2057.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_2057.FStar_Absyn_Syntax.uvs}))
in (

let desugar_quant = (fun q qt b pats body -> (

let tk = (desugar_binder env (

let _62_2065 = b
in {FStar_Parser_AST.b = _62_2065.FStar_Parser_AST.b; FStar_Parser_AST.brange = _62_2065.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _62_2065.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _156_736 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _156_736)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _62_2080 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_62_2080) with
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
| _62_2085 -> begin
(let _156_737 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
in (FStar_All.pipe_left setpos _156_737))
end)
in (

let body = (let _156_743 = (let _156_742 = (let _156_741 = (let _156_740 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_156_740)::[])
in ((_156_741), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _156_742))
in (FStar_All.pipe_left pos _156_743))
in (let _156_747 = (let _156_746 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange) FStar_Absyn_Syntax.kun)
in (let _156_745 = (let _156_744 = (FStar_Absyn_Syntax.targ body)
in (_156_744)::[])
in (FStar_Absyn_Util.mk_typ_app _156_746 _156_745)))
in (FStar_All.pipe_left setpos _156_747))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _62_2095 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_2095) with
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
| _62_2100 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
end)
in (

let body = (let _156_753 = (let _156_752 = (let _156_751 = (let _156_750 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_156_750)::[])
in ((_156_751), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _156_752))
in (FStar_All.pipe_left pos _156_753))
in (let _156_757 = (let _156_756 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) FStar_Absyn_Syntax.kun)
in (let _156_755 = (let _156_754 = (FStar_Absyn_Syntax.targ body)
in (_156_754)::[])
in (FStar_Absyn_Util.mk_typ_app _156_756 _156_755)))
in (FStar_All.pipe_left setpos _156_757))))))
end))
end
| _62_2104 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _156_772 = (q ((rest), (pats), (body)))
in (let _156_771 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _156_772 _156_771 FStar_Parser_AST.Formula)))
in (let _156_773 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _156_773 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _62_2118 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _156_774 = (unparen f)
in _156_774.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (l), (FStar_Absyn_Syntax.dummyRange), (p))))))
end
| FStar_Parser_AST.Op ("==", (hd)::_args) -> begin
(

let args = (hd)::_args
in (

let args = (FStar_List.map (fun t -> (let _156_776 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _156_776))) args)
in (

let eq = if (is_type env hd) then begin
(FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range) FStar_Absyn_Syntax.kun)
end else begin
(FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range) FStar_Absyn_Syntax.kun)
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((((connective s)), (args))) with
| (Some (conn), (_62_2144)::(_62_2142)::[]) -> begin
(let _156_780 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range) FStar_Absyn_Syntax.kun)
in (let _156_779 = (FStar_List.map (fun x -> (let _156_778 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _156_778))) args)
in (FStar_Absyn_Util.mk_typ_app _156_780 _156_779)))
end
| _62_2149 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _156_781 = (desugar_exp env f)
in (FStar_All.pipe_right _156_781 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _156_785 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range) FStar_Absyn_Syntax.kun)
in (let _156_784 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _156_783 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _156_783))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _156_785 _156_784)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _156_787 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _156_787)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _156_789 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _156_789)))
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
| _62_2211 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _156_790 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _156_790))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (

let _62_2214 = env
in {FStar_Parser_DesugarEnv.curmodule = _62_2214.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _62_2214.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _62_2214.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _62_2214.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _62_2214.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _62_2214.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _62_2214.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _62_2214.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _62_2214.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _62_2214.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _62_2214.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _156_795 = (desugar_type_binder env b)
in FStar_Util.Inl (_156_795))
end else begin
(let _156_796 = (desugar_exp_binder env b)
in FStar_Util.Inr (_156_796))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _62_2247 = (FStar_List.fold_left (fun _62_2222 b -> (match (_62_2222) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _62_2224 = b
in {FStar_Parser_AST.b = _62_2224.FStar_Parser_AST.b; FStar_Parser_AST.brange = _62_2224.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _62_2224.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _62_2234 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_62_2234) with
| (env, a) -> begin
((env), ((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _62_2242 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_2242) with
| (env, x) -> begin
((env), ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| _62_2244 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_62_2247) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _156_803 = (desugar_typ env t)
in ((Some (x)), (_156_803)))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _156_804 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in ((None), (_156_804)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _156_805 = (desugar_typ env t)
in ((None), (_156_805)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Absyn_Syntax.tun))
end
| _62_2261 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a type)"), (b.FStar_Parser_AST.brange)))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (

let fail = (fun _62_2265 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a kind)"), (b.FStar_Parser_AST.brange)))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _156_810 = (desugar_kind env t)
in ((Some (x)), (_156_810)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _156_811 = (desugar_kind env t)
in ((None), (_156_811)))
end
| FStar_Parser_AST.TVariable (x) -> begin
((Some (x)), ((

let _62_2276 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _62_2276.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_2276.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _62_2276.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_2276.FStar_Absyn_Syntax.uvs})))
end
| _62_2279 -> begin
(fail ())
end)))


let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (

let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_62_2290, k) -> begin
(aux bs k)
end
| _62_2295 -> begin
bs
end))
in (let _156_820 = (aux tps k)
in (FStar_All.pipe_right _156_820 FStar_Absyn_Util.name_binders))))


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

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _62_2309 -> (match (_62_2309) with
| (x, _62_2308) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (let _156_841 = (let _156_840 = (let _156_839 = (let _156_838 = (let _156_837 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _156_836 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_156_837), (_156_836))))
in (FStar_Absyn_Syntax.mk_Typ_app' _156_838 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _156_839))
in (_156_840)::[])
in (FStar_List.append imp_binders _156_841))
in (

let disc_type = (let _156_844 = (let _156_843 = (let _156_842 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _156_842 p))
in ((binders), (_156_843)))
in (FStar_Absyn_Syntax.mk_Typ_fun _156_844 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _156_847 = (let _156_846 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in ((disc_name), (disc_type), (_156_846), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Absyn_Syntax.Sig_val_decl (_156_847)))))))))))))


let mk_indexed_projectors = (fun fvq refine_domain env _62_2321 lid formals t -> (match (_62_2321) with
| (tc, tps, k) -> begin
(

let binders = (gather_tc_binders tps k)
in (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (

let projectee = (let _156_858 = (FStar_Absyn_Syntax.mk_ident (("projectee"), (p)))
in (let _156_857 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _156_858; FStar_Absyn_Syntax.realname = _156_857}))
in (

let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (

let arg_binder = (

let arg_typ = (let _156_861 = (let _156_860 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _156_859 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_156_860), (_156_859))))
in (FStar_Absyn_Syntax.mk_Typ_app' _156_861 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(

let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (

let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _156_871 = (let _156_870 = (let _156_869 = (let _156_868 = (let _156_867 = (let _156_866 = (let _156_865 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _156_864 = (let _156_863 = (let _156_862 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _156_862))
in (_156_863)::[])
in ((_156_865), (_156_864))))
in (FStar_Absyn_Syntax.mk_Exp_app _156_866 None p))
in (FStar_Absyn_Util.b2t _156_867))
in ((x), (_156_868)))
in (FStar_Absyn_Syntax.mk_Typ_refine _156_869 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _156_870))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _156_871))))
end)
in (

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _62_2338 -> (match (_62_2338) with
| (x, _62_2337) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (let _156_879 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(

let _62_2349 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_62_2349) with
| (field_name, _62_2348) -> begin
(

let proj = (let _156_876 = (let _156_875 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in ((_156_875), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Typ_app _156_876 None p))
in (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _62_2356 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_62_2356) with
| (field_name, _62_2355) -> begin
(

let proj = (let _156_878 = (let _156_877 = (FStar_Absyn_Util.fvar None field_name p)
in ((_156_877), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Exp_app _156_878 None p))
in (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end))))
in (FStar_All.pipe_right _156_879 FStar_List.flatten))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _156_881 = (FStar_All.pipe_right tps (FStar_List.map (fun _62_2363 -> (match (_62_2363) with
| (b, _62_2362) -> begin
((b), (Some (imp_tag)))
end))))
in (FStar_List.append _156_881 formals))
in (let _156_911 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(

let _62_2372 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_62_2372) with
| (field_name, _62_2371) -> begin
(

let kk = (let _156_885 = (let _156_884 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in ((binders), (_156_884)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _156_885 p))
in (FStar_Absyn_Syntax.Sig_tycon (((field_name), ([]), (kk), ([]), ([]), ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inl (a.FStar_Absyn_Syntax.v)))))::[]), ((FStar_Ident.range_of_lid field_name)))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _62_2379 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_62_2379) with
| (field_name, _62_2378) -> begin
(

let t = (let _156_888 = (let _156_887 = (let _156_886 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _156_886 p))
in ((binders), (_156_887)))
in (FStar_Absyn_Syntax.mk_Typ_fun _156_888 None p))
in (

let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (

let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inr (x.FStar_Absyn_Syntax.v)))))::[]))
in (

let impl = if (((let _156_891 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _156_891)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _156_893 = (let _156_892 = (FStar_Parser_DesugarEnv.current_module env)
in _156_892.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _156_893))) then begin
[]
end else begin
(

let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (

let as_imp = (fun _62_14 -> (match (_62_14) with
| Some (FStar_Absyn_Syntax.Implicit (_62_2387)) -> begin
true
end
| _62_2391 -> begin
false
end))
in (

let arg_pats = (let _156_908 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_62_2396), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _156_901 = (let _156_900 = (let _156_899 = (let _156_898 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_156_898))
in (pos _156_899))
in ((_156_900), ((as_imp imp))))
in (_156_901)::[])
end
end
| (FStar_Util.Inr (_62_2401), imp) -> begin
if ((i + ntps) = j) then begin
(let _156_903 = (let _156_902 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in ((_156_902), ((as_imp imp))))
in (_156_903)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _156_907 = (let _156_906 = (let _156_905 = (let _156_904 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_156_904))
in (pos _156_905))
in ((_156_906), ((as_imp imp))))
in (_156_907)::[])
end
end
end))))
in (FStar_All.pipe_right _156_908 FStar_List.flatten))
in (

let pat = (let _156_910 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv lid)), (Some (fvq)), (arg_pats)))) pos)
in (let _156_909 = (FStar_Absyn_Util.bvar_to_exp projection)
in ((_156_910), (None), (_156_909))))
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
in (FStar_All.pipe_right _156_911 FStar_List.flatten))))))))))))))
end))


let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _62_17 -> (match (_62_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _62_2418, _62_2420) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_15 -> (match (_62_15) with
| FStar_Absyn_Syntax.RecordConstructor (_62_2425) -> begin
true
end
| _62_2428 -> begin
false
end)))) then begin
false
end else begin
(

let _62_2434 = tycon
in (match (_62_2434) with
| (l, _62_2431, _62_2433) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > (Prims.parse_int "1"))
end
| _62_2438 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(

let cod = (FStar_Absyn_Util.comp_result cod)
in (

let qual = (match ((FStar_Util.find_map quals (fun _62_16 -> (match (_62_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor (((lid), (fns))))
end
| _62_2449 -> begin
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
| _62_2455 -> begin
[]
end))
end
| _62_2457 -> begin
[]
end))


let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _62_18 -> (match (_62_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _156_931 = (let _156_930 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_156_930))
in (FStar_Parser_AST.mk_term _156_931 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _62_2522 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _156_944 = (let _156_943 = (let _156_942 = (binder_to_term b)
in ((out), (_156_942), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_156_943))
in (FStar_Parser_AST.mk_term _156_944 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _62_19 -> (match (_62_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _62_2537 -> (match (_62_2537) with
| (x, t, _62_2536) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Absyn_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _156_950 = (let _156_949 = (let _156_948 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_156_948))
in (FStar_Parser_AST.mk_term _156_949 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _156_950 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _156_952 = (FStar_All.pipe_right fields (FStar_List.map (fun _62_2546 -> (match (_62_2546) with
| (x, _62_2543, _62_2545) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_156_952)))))))
end
| _62_2548 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _62_20 -> (match (_62_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _62_2562 = (typars_of_binders _env binders)
in (match (_62_2562) with
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

let tconstr = (let _156_963 = (let _156_962 = (let _156_961 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_156_961))
in (FStar_Parser_AST.mk_term _156_962 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _156_963 binders))
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
| _62_2573 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparam = (fun env _62_21 -> (match (_62_21) with
| (FStar_Util.Inr (x), _62_2580) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _62_2585) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (

let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (_62_2589))::[] -> begin
(

let tc = (FStar_List.hd tcs)
in (

let _62_2600 = (desugar_abstract_tc quals env [] tc)
in (match (_62_2600) with
| (_62_2594, _62_2596, se, _62_2599) -> begin
(

let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(

let _62_2601 = (let _156_973 = (FStar_Range.string_of_range rng)
in (let _156_972 = (let _156_971 = (let _156_970 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _156_970 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _156_971 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _156_973 _156_972)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))
end)))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _62_2614 = (typars_of_binders env binders)
in (match (_62_2614) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _62_22 -> (match (_62_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _62_2619 -> begin
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

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_23 -> (match (_62_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _62_2627 -> begin
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
in (let _156_979 = (let _156_978 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _156_977 = (FStar_All.pipe_right quals (FStar_List.filter (fun _62_24 -> (match (_62_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _62_2633 -> begin
true
end))))
in ((_156_978), (typars), (c), (_156_977), (rng))))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_156_979)))
end else begin
(

let t = (desugar_typ env' t)
in (let _156_981 = (let _156_980 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_156_980), (typars), (k), (t), (quals), (rng)))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_156_981)))
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_62_2638))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _62_2644 = (tycon_record_as_variant trec)
in (match (_62_2644) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_62_2648)::_62_2646 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _62_2659 = et
in (match (_62_2659) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_62_2661) -> begin
(

let trec = tc
in (

let _62_2666 = (tycon_record_as_variant trec)
in (match (_62_2666) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _62_2678 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_62_2678) with
| (env, _62_2675, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _62_2690 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_62_2690) with
| (env, _62_2687, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _62_2692 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _62_2695 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_62_2695) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _62_26 -> (match (_62_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _62_2702, _62_2704, _62_2706, _62_2708), t, quals) -> begin
(

let env_tps = (push_tparams env tpars)
in (

let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev (((id), (tpars), (k), (t), ([]), (rng))))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _62_2722, tags, _62_2725), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let env_tps = (push_tparams env tpars)
in (

let _62_2758 = (let _156_997 = (FStar_All.pipe_right constrs (FStar_List.map (fun _62_2740 -> (match (_62_2740) with
| (id, topt, _62_2738, of_notation) -> begin
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

let t = (let _156_992 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _156_991 = (close env_tps t)
in (desugar_typ _156_992 _156_991)))
in (

let name = (FStar_Parser_DesugarEnv.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _62_25 -> (match (_62_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _62_2754 -> begin
[]
end))))
in (let _156_996 = (let _156_995 = (let _156_994 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in ((name), (_156_994), (tycon), (quals), (mutuals), (rng)))
in FStar_Absyn_Syntax.Sig_datacon (_156_995))
in ((name), (_156_996)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _156_997))
in (match (_62_2758) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon (((tname), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))::constrs
end))))
end
| _62_2760 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let bundle = (let _156_999 = (let _156_998 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_156_998), (rng)))
in FStar_Absyn_Syntax.Sig_bundle (_156_999))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _62_27 -> (match (_62_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _62_2770, constrs, quals, _62_2774) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _62_2778 -> begin
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

let _62_2809 = (FStar_List.fold_left (fun _62_2787 b -> (match (_62_2787) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _62_2796 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_62_2796) with
| (env, a) -> begin
(let _156_1008 = (let _156_1007 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_156_1007)::binders)
in ((env), (_156_1008)))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _62_2804 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_2804) with
| (env, x) -> begin
(let _156_1010 = (let _156_1009 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_156_1009)::binders)
in ((env), (_156_1010)))
end))
end
| _62_2806 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_62_2809) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Absyn_Syntax.qualifier = (fun r _62_28 -> (match (_62_28) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _62_29 -> (match (_62_29) with
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
| FStar_Parser_AST.Fsdoc (_62_2838) -> begin
((env), ([]))
end
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = FStar_Absyn_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.TopLevelModule (id) -> begin
((env), ([]))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _156_1028 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in ((_156_1028), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(

let tcs = (FStar_List.map (fun _62_2859 -> (match (_62_2859) with
| (x, _62_2858) -> begin
x
end)) tcs)
in (let _156_1030 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _156_1030 tcs)))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _156_1032 = (let _156_1031 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _156_1031))
in _156_1032.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _62_2868) -> begin
(

let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _62_2875 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let quals = (match (quals) with
| (_62_2880)::_62_2878 -> begin
(trans_quals quals)
end
| _62_2883 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _62_30 -> (match (_62_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_62_2892); FStar_Absyn_Syntax.lbtyp = _62_2890; FStar_Absyn_Syntax.lbeff = _62_2888; FStar_Absyn_Syntax.lbdef = _62_2886} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _62_2900; FStar_Absyn_Syntax.lbeff = _62_2898; FStar_Absyn_Syntax.lbdef = _62_2896} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (

let s = FStar_Absyn_Syntax.Sig_let (((lbs), (d.FStar_Parser_AST.drange), (lids), (quals)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in ((env), ((s)::[]))))))
end
| _62_2908 -> begin
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
in (let _156_1038 = (let _156_1037 = (let _156_1036 = (let _156_1035 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_156_1035), (f), ((FStar_Absyn_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_assume (_156_1036))
in (_156_1037)::[])
in ((env), (_156_1038))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _156_1039 = (close_fun env t)
in (desugar_typ env _156_1039))
in (

let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _156_1040 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_156_1040)
end else begin
(trans_quals quals)
end
in (

let se = (let _156_1042 = (let _156_1041 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_156_1041), (t), (quals), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_val_decl (_156_1042))
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

let t = (let _156_1047 = (let _156_1046 = (let _156_1043 = (FStar_Absyn_Syntax.null_v_binder t)
in (_156_1043)::[])
in (let _156_1045 = (let _156_1044 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _156_1044))
in ((_156_1046), (_156_1045))))
in (FStar_Absyn_Syntax.mk_Typ_fun _156_1047 None d.FStar_Parser_AST.drange))
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

let _62_2961 = (desugar_binders env binders)
in (match (_62_2961) with
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
| FStar_Parser_AST.NewEffectForFree (_62_2967) -> begin
(FStar_All.failwith "effects for free only supported in conjunction with --universes")
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let env0 = env
in (

let _62_2980 = (desugar_binders env eff_binders)
in (match (_62_2980) with
| (env, binders) -> begin
(

let defn = (desugar_typ env defn)
in (

let _62_2984 = (FStar_Absyn_Util.head_and_args defn)
in (match (_62_2984) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _156_1052 = (let _156_1051 = (let _156_1050 = (let _156_1049 = (let _156_1048 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat _156_1048 " not found"))
in (Prims.strcat "Effect " _156_1049))
in ((_156_1050), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_156_1051))
in (Prims.raise _156_1052))
end
| Some (ed) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (

let sub = (FStar_Absyn_Util.subst_typ subst)
in (

let ed = (let _156_1070 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _156_1069 = (trans_quals quals)
in (let _156_1068 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _156_1067 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _156_1066 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _156_1065 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _156_1064 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _156_1063 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _156_1062 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _156_1061 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _156_1060 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _156_1059 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _156_1058 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _156_1057 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _156_1056 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _156_1055 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _156_1054 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _156_1070; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _156_1069; FStar_Absyn_Syntax.signature = _156_1068; FStar_Absyn_Syntax.ret = _156_1067; FStar_Absyn_Syntax.bind_wp = _156_1066; FStar_Absyn_Syntax.bind_wlp = _156_1065; FStar_Absyn_Syntax.if_then_else = _156_1064; FStar_Absyn_Syntax.ite_wp = _156_1063; FStar_Absyn_Syntax.ite_wlp = _156_1062; FStar_Absyn_Syntax.wp_binop = _156_1061; FStar_Absyn_Syntax.wp_as_type = _156_1060; FStar_Absyn_Syntax.close_wp = _156_1059; FStar_Absyn_Syntax.close_wp_t = _156_1058; FStar_Absyn_Syntax.assert_p = _156_1057; FStar_Absyn_Syntax.assume_p = _156_1056; FStar_Absyn_Syntax.null_wp = _156_1055; FStar_Absyn_Syntax.trivial = _156_1054})))))))))))))))))
in (

let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)
end
| _62_2996 -> begin
(let _156_1074 = (let _156_1073 = (let _156_1072 = (let _156_1071 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _156_1071 " is not an effect"))
in ((_156_1072), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_156_1073))
in (Prims.raise _156_1074))
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

let _62_3011 = (desugar_binders env eff_binders)
in (match (_62_3011) with
| (env, binders) -> begin
(

let eff_k = (desugar_kind env eff_kind)
in (

let _62_3022 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _62_3015 decl -> (match (_62_3015) with
| (env, out) -> begin
(

let _62_3019 = (desugar_decl env decl)
in (match (_62_3019) with
| (env, ses) -> begin
(let _156_1078 = (let _156_1077 = (FStar_List.hd ses)
in (_156_1077)::out)
in ((env), (_156_1078)))
end))
end)) ((env), ([]))))
in (match (_62_3022) with
| (env, decls) -> begin
(

let decls = (FStar_List.rev decls)
in (

let lookup = (fun s -> (match ((let _156_1082 = (let _156_1081 = (FStar_Absyn_Syntax.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.qualify env _156_1081))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _156_1082))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Monad " (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat " expects definition of " s)))), (d.FStar_Parser_AST.drange)))))
end
| Some (t) -> begin
t
end))
in (

let ed = (let _156_1098 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _156_1097 = (trans_quals quals)
in (let _156_1096 = (lookup "return")
in (let _156_1095 = (lookup "bind_wp")
in (let _156_1094 = (lookup "bind_wlp")
in (let _156_1093 = (lookup "if_then_else")
in (let _156_1092 = (lookup "ite_wp")
in (let _156_1091 = (lookup "ite_wlp")
in (let _156_1090 = (lookup "wp_binop")
in (let _156_1089 = (lookup "wp_as_type")
in (let _156_1088 = (lookup "close_wp")
in (let _156_1087 = (lookup "close_wp_t")
in (let _156_1086 = (lookup "assert_p")
in (let _156_1085 = (lookup "assume_p")
in (let _156_1084 = (lookup "null_wp")
in (let _156_1083 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _156_1098; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _156_1097; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _156_1096; FStar_Absyn_Syntax.bind_wp = _156_1095; FStar_Absyn_Syntax.bind_wlp = _156_1094; FStar_Absyn_Syntax.if_then_else = _156_1093; FStar_Absyn_Syntax.ite_wp = _156_1092; FStar_Absyn_Syntax.ite_wlp = _156_1091; FStar_Absyn_Syntax.wp_binop = _156_1090; FStar_Absyn_Syntax.wp_as_type = _156_1089; FStar_Absyn_Syntax.close_wp = _156_1088; FStar_Absyn_Syntax.close_wp_t = _156_1087; FStar_Absyn_Syntax.assert_p = _156_1086; FStar_Absyn_Syntax.assume_p = _156_1085; FStar_Absyn_Syntax.null_wp = _156_1084; FStar_Absyn_Syntax.trivial = _156_1083}))))))))))))))))
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
(let _156_1105 = (let _156_1104 = (let _156_1103 = (let _156_1102 = (let _156_1101 = (FStar_Absyn_Print.sli l)
in (Prims.strcat _156_1101 " not found"))
in (Prims.strcat "Effect name " _156_1102))
in ((_156_1103), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_156_1104))
in (Prims.raise _156_1105))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let non_reifiable = (fun _62_31 -> (match (_62_31) with
| FStar_Parser_AST.NonReifiableLift (f) -> begin
f
end
| _62_3045 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected reifiable sub-effect"), (d.FStar_Parser_AST.drange)))))
end))
in (

let lift = (let _156_1108 = (non_reifiable l.FStar_Parser_AST.lift_op)
in (desugar_typ env _156_1108))
in (

let se = FStar_Absyn_Syntax.Sig_sub_effect ((({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))))))
end)))


let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _62_3053 d -> (match (_62_3053) with
| (env, sigelts) -> begin
(

let _62_3057 = (desugar_decl env d)
in (match (_62_3057) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.fsdoc Prims.option  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]


let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let open_ns = (fun mname d -> (

let d = if ((FStar_List.length mname.FStar_Ident.ns) <> (Prims.parse_int "0")) then begin
(let _156_1133 = (let _156_1132 = (let _156_1130 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_156_1130))
in (let _156_1131 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _156_1132 _156_1131 None)))
in (_156_1133)::d)
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

let _62_3084 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _156_1135 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _156_1134 = (open_ns mname decls)
in ((_156_1135), (mname), (_156_1134), (true))))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _156_1137 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _156_1136 = (open_ns mname decls)
in ((_156_1137), (mname), (_156_1136), (false))))
end)
in (match (_62_3084) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _62_3087 = (desugar_decls env decls)
in (match (_62_3087) with
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
| FStar_Parser_AST.Interface (mname, _62_3098, _62_3100) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _62_3108 = (desugar_modul_common curmod env m)
in (match (_62_3108) with
| (x, y, _62_3107) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (

let _62_3114 = (desugar_modul_common None env m)
in (match (_62_3114) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (

let _62_3116 = if (FStar_Options.dump_module modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _156_1148 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _156_1148))
end else begin
()
end
in (let _156_1149 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in ((_156_1149), (modul)))))
end)))


let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (

let _62_3129 = (FStar_List.fold_left (fun _62_3122 m -> (match (_62_3122) with
| (env, mods) -> begin
(

let _62_3126 = (desugar_modul env m)
in (match (_62_3126) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_62_3129) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (

let _62_3134 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_62_3134) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (

let _62_3135 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _62_3135.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _62_3135.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _62_3135.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _62_3135.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _62_3135.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _62_3135.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _62_3135.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _62_3135.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _62_3135.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _62_3135.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _62_3135.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))





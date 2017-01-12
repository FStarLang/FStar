
open Prims

let imp_tag : FStar_Absyn_Syntax.arg_qualifier = FStar_Absyn_Syntax.Implicit (false)


let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _64_1 -> (match (_64_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (imp_tag)
end
| _64_36 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (imp_tag)))
end
| _64_43 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_64_47) -> begin
true
end
| _64_50 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _64_55 -> begin
t
end))


let rec unlabel : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _64_61, _64_63) -> begin
(unlabel t)
end
| _64_67 -> begin
t
end))


let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _163_17 = (let _163_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_163_16))
in (FStar_Parser_AST.mk_term _163_17 r FStar_Parser_AST.Kind)))


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _64_2 -> (match (_64_2) with
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
| _64_90 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _163_28 = (let _163_26 = (FStar_Util.char_at s i)
in (name_of_char _163_26))
in (let _163_27 = (aux (i + (Prims.parse_int "1")))
in (_163_28)::_163_27))
end)
in (let _163_30 = (let _163_29 = (aux (Prims.parse_int "0"))
in (FStar_String.concat "_" _163_29))
in (Prims.strcat "op_" _163_30)))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _163_40 = (let _163_39 = (let _163_38 = (let _163_37 = (compile_op n s)
in ((_163_37), (r)))
in (FStar_Absyn_Syntax.mk_ident _163_38))
in (_163_39)::[])
in (FStar_All.pipe_right _163_40 FStar_Absyn_Syntax.lid_of_ids)))


let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (

let r = (fun l -> Some ((FStar_Ident.set_lid_range l rng)))
in (

let fallback = (fun _64_104 -> (match (()) with
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
| _64_126 -> begin
None
end)
end))
in (match ((let _163_53 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _163_53))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _64_137); FStar_Absyn_Syntax.tk = _64_134; FStar_Absyn_Syntax.pos = _64_132; FStar_Absyn_Syntax.fvs = _64_130; FStar_Absyn_Syntax.uvs = _64_128}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _64_143 -> begin
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
(match ((let _163_64 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _163_64))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _64_166; FStar_Absyn_Syntax.pos = _64_164; FStar_Absyn_Syntax.fvs = _64_162; FStar_Absyn_Syntax.uvs = _64_160}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _64_172 -> begin
None
end)
end)))


let rec is_type : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _163_71 = (unparen t)
in _163_71.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_64_177) -> begin
true
end
| FStar_Parser_AST.Op ("*", (hd)::_64_181) -> begin
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
| _64_232 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = (Prims.parse_int "0")) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_64_255) -> begin
true
end
| _64_258 -> begin
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
| FStar_Parser_AST.Product (_64_299, t) -> begin
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
| FStar_Parser_AST.PatTvar (id, _64_325) -> begin
(

let _64_331 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_64_331) with
| (env, _64_330) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(

let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _163_76 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _163_76 Prims.fst))
end
| _64_346 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _64_349 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_354); FStar_Parser_AST.prange = _64_352}, _64_358))::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_370); FStar_Parser_AST.prange = _64_368}, _64_374); FStar_Parser_AST.prange = _64_366}, _64_379))::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_389); FStar_Parser_AST.prange = _64_387}, _64_393))::[], t) -> begin
(is_type env t)
end
| _64_400 -> begin
false
end)
end)
and is_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _163_79 = (unparen t)
in _163_79.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_409; FStar_Ident.ident = _64_407; FStar_Ident.nsstr = _64_405; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_64_413, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _64_426 -> begin
false
end)
end)


let rec is_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  Prims.bool = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_64_430) -> begin
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
| FStar_Parser_AST.Variable (_64_445) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected binder without annotation"), (b.FStar_Parser_AST.brange)))))
end
| FStar_Parser_AST.TVariable (_64_448) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_64_451) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _163_90 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _163_90)))


let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_64_467) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _64_474 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_64_474) with
| (env, _64_473) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_64_476, term) -> begin
(let _163_97 = (free_type_vars env term)
in ((env), (_163_97)))
end
| FStar_Parser_AST.TAnnotated (id, _64_482) -> begin
(

let _64_488 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_64_488) with
| (env, _64_487) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _163_98 = (free_type_vars env t)
in ((env), (_163_98)))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _163_101 = (unparen t)
in _163_101.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _64_497 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_64_542, ts) -> begin
(FStar_List.collect (fun _64_549 -> (match (_64_549) with
| (t, _64_548) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_64_551, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _64_558) -> begin
(let _163_104 = (free_type_vars env t1)
in (let _163_103 = (free_type_vars env t2)
in (FStar_List.append _163_104 _163_103)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _64_567 = (free_type_vars_b env b)
in (match (_64_567) with
| (env, f) -> begin
(let _163_105 = (free_type_vars env t)
in (FStar_List.append f _163_105))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _64_583 = (FStar_List.fold_left (fun _64_576 binder -> (match (_64_576) with
| (env, free) -> begin
(

let _64_580 = (free_type_vars_b env binder)
in (match (_64_580) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_64_583) with
| (env, free) -> begin
(let _163_108 = (free_type_vars env body)
in (FStar_List.append free _163_108))
end))
end
| FStar_Parser_AST.Project (t, _64_586) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _163_115 = (unparen t)
in _163_115.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _64_638 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _163_120 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _163_120))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _163_124 = (let _163_123 = (let _163_122 = (kind_star x.FStar_Ident.idRange)
in ((x), (_163_122)))
in FStar_Parser_AST.TAnnotated (_163_123))
in (FStar_Parser_AST.mk_binder _163_124 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _163_129 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _163_129))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _163_133 = (let _163_132 = (let _163_131 = (kind_star x.FStar_Ident.idRange)
in ((x), (_163_131)))
in FStar_Parser_AST.TAnnotated (_163_132))
in (FStar_Parser_AST.mk_binder _163_133 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _163_134 = (unlabel t)
in _163_134.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_64_651) -> begin
t
end
| _64_654 -> begin
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
| _64_664 -> begin
((bs), (t))
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _64_668) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_674); FStar_Parser_AST.prange = _64_672}, _64_678) -> begin
true
end
| _64_682 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _64_694 = (destruct_app_pattern env is_top_level p)
in (match (_64_694) with
| (name, args, _64_693) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_699); FStar_Parser_AST.prange = _64_696}, args) when is_top_level -> begin
(let _163_148 = (let _163_147 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_163_147))
in ((_163_148), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_710); FStar_Parser_AST.prange = _64_707}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _64_718 -> begin
(failwith "Not an app pattern")
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
| TBinder (_64_721) -> begin
_64_721
end))


let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_64_724) -> begin
_64_724
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_64_727) -> begin
_64_727
end))


let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _64_3 -> (match (_64_3) with
| TBinder (a, k, aq) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), (aq))
end
| VBinder (x, t, aq) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (aq))
end
| _64_740 -> begin
(failwith "Impossible")
end))


let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _64_4 -> (match (_64_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _64_747 -> begin
None
end))


let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either  ->  (FStar_Absyn_Syntax.binder * FStar_Parser_DesugarEnv.env) = (fun env imp _64_5 -> (match (_64_5) with
| FStar_Util.Inl (None, k) -> begin
(let _163_201 = (FStar_Absyn_Syntax.null_t_binder k)
in ((_163_201), (env)))
end
| FStar_Util.Inr (None, t) -> begin
(let _163_202 = (FStar_Absyn_Syntax.null_v_binder t)
in ((_163_202), (env)))
end
| FStar_Util.Inl (Some (a), k) -> begin
(

let _64_766 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_64_766) with
| (env, a) -> begin
((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual imp)))), (env))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _64_774 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_774) with
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
| _64_784 -> begin
(let _163_213 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _163_213))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (((f), (msg), (polarity)))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (

let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _163_217 = (let _163_216 = (aux g)
in FStar_Parser_AST.Paren (_163_216))
in (FStar_Parser_AST.mk_term _163_217 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", (f1)::(f2)::[]) -> begin
(let _163_223 = (let _163_222 = (let _163_221 = (let _163_220 = (aux f1)
in (let _163_219 = (let _163_218 = (aux f2)
in (_163_218)::[])
in (_163_220)::_163_219))
in (("/\\"), (_163_221)))
in FStar_Parser_AST.Op (_163_222))
in (FStar_Parser_AST.mk_term _163_223 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _163_227 = (let _163_226 = (let _163_225 = (aux f2)
in (let _163_224 = (aux f3)
in ((f1), (_163_225), (_163_224))))
in FStar_Parser_AST.If (_163_226))
in (FStar_Parser_AST.mk_term _163_227 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _163_230 = (let _163_229 = (let _163_228 = (aux g)
in ((binders), (_163_228)))
in FStar_Parser_AST.Abs (_163_229))
in (FStar_Parser_AST.mk_term _163_230 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _64_806 -> begin
(label f)
end))
in (aux f))))


let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _64_810 -> (match (_64_810) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))


let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _64_6 -> (match (_64_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _64_821 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
((l), (e), (y))
end
| _64_826 -> begin
(

let _64_829 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_64_829) with
| (e, x) -> begin
(((FStar_Util.Inr (x))::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _64_7 -> (match (_64_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _64_838 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
((l), (e), (b))
end
| _64_843 -> begin
(

let _64_846 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_64_846) with
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
| FStar_Parser_AST.PatOp (_64_857) -> begin
(failwith "let op not supported in stratified")
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _64_871 = (aux loc env p)
in (match (_64_871) with
| (loc, env, var, p, _64_870) -> begin
(

let _64_888 = (FStar_List.fold_left (fun _64_875 p -> (match (_64_875) with
| (loc, env, ps) -> begin
(

let _64_884 = (aux loc env p)
in (match (_64_884) with
| (loc, env, _64_880, p, _64_883) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_64_888) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (

let _64_890 = (let _163_307 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _163_307))
in ((loc), (env), (var), (pat), (false))))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_64_897) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(

let _64_903 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (((x), (imp))); FStar_Parser_AST.prange = _64_903.FStar_Parser_AST.prange})
end
| _64_906 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
p
end
in (

let _64_913 = (aux loc env p)
in (match (_64_913) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_64_915) -> begin
(failwith "impossible")
end
| TBinder (x, _64_919, aq) -> begin
(let _163_309 = (let _163_308 = (desugar_kind env t)
in ((x), (_163_308), (aq)))
in TBinder (_163_309))
end
| VBinder (x, _64_925, aq) -> begin
(

let t = (close_fun env t)
in (let _163_311 = (let _163_310 = (desugar_typ env t)
in ((x), (_163_310), (aq)))
in VBinder (_163_311)))
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
in (let _163_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((a), (FStar_Absyn_Syntax.kun), (aq)))), (_163_312), (imp))))
end else begin
(

let _64_941 = (resolvea loc env a)
in (match (_64_941) with
| (loc, env, abvd) -> begin
(let _163_313 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((abvd), (FStar_Absyn_Syntax.kun), (aq)))), (_163_313), (imp)))
end))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (

let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _163_314 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_163_314), (false)))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _163_315 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_163_315), (false))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _64_957 = (resolvex loc env x)
in (match (_64_957) with
| (loc, env, xbvd) -> begin
(let _163_316 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((xbvd), (FStar_Absyn_Syntax.tun), (aq)))), (_163_316), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _163_317 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), ([])))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_163_317), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _64_963}, args) -> begin
(

let _64_985 = (FStar_List.fold_right (fun arg _64_974 -> (match (_64_974) with
| (loc, env, args) -> begin
(

let _64_981 = (aux loc env arg)
in (match (_64_981) with
| (loc, env, _64_978, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_64_985) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _163_320 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_163_320), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_64_989) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _64_1009 = (FStar_List.fold_right (fun pat _64_997 -> (match (_64_997) with
| (loc, env, pats) -> begin
(

let _64_1005 = (aux loc env pat)
in (match (_64_1005) with
| (loc, env, _64_1001, pat, _64_1004) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_64_1009) with
| (loc, env, pats) -> begin
(

let pat = (let _163_327 = (let _163_326 = (let _163_325 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _163_325))
in (FStar_All.pipe_left _163_326 (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ([]))))))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((hd), (false)))::(((tl), (false)))::[]))))))) pats _163_327))
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _64_1035 = (FStar_List.fold_left (fun _64_1022 p -> (match (_64_1022) with
| (loc, env, pats) -> begin
(

let _64_1031 = (aux loc env p)
in (match (_64_1031) with
| (loc, env, _64_1027, pat, _64_1030) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_64_1035) with
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
| FStar_Absyn_Syntax.Exp_fvar (v, _64_1041) -> begin
v
end
| _64_1045 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _163_330 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_163_330), (false))))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _64_1055 = (FStar_List.hd fields)
in (match (_64_1055) with
| (f, _64_1054) -> begin
(

let _64_1059 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_64_1059) with
| (record, _64_1058) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _64_1062 -> (match (_64_1062) with
| (f, p) -> begin
(let _163_332 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in ((_163_332), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _64_1067 -> (match (_64_1067) with
| (f, _64_1066) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _64_1071 -> (match (_64_1071) with
| (g, _64_1070) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_64_1074, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _64_1086 = (aux loc env app)
in (match (_64_1086) with
| (env, e, b, p, _64_1085) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _64_1089, args) -> begin
(let _163_340 = (let _163_339 = (let _163_338 = (let _163_337 = (let _163_336 = (let _163_335 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_163_335)))
in FStar_Absyn_Syntax.Record_ctor (_163_336))
in Some (_163_337))
in ((fv), (_163_338), (args)))
in FStar_Absyn_Syntax.Pat_cons (_163_339))
in (FStar_All.pipe_left pos _163_340))
end
| _64_1094 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _64_1103 = (aux [] env p)
in (match (_64_1103) with
| (_64_1097, env, b, p, _64_1102) -> begin
((env), (b), (p))
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _64_1109) -> begin
(let _163_346 = (let _163_345 = (let _163_344 = (FStar_Parser_DesugarEnv.qualify env x)
in ((_163_344), (FStar_Absyn_Syntax.tun)))
in LetBinder (_163_345))
in ((env), (_163_346), (None)))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _64_1116); FStar_Parser_AST.prange = _64_1113}, t) -> begin
(let _163_350 = (let _163_349 = (let _163_348 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _163_347 = (desugar_typ env t)
in ((_163_348), (_163_347))))
in LetBinder (_163_349))
in ((env), (_163_350), (None)))
end
| _64_1124 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _64_1128 = (desugar_data_pat env p)
in (match (_64_1128) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _64_1139 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _64_1143 env pat -> (

let _64_1151 = (desugar_data_pat env pat)
in (match (_64_1151) with
| (env, _64_1149, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _163_360 = (desugar_typ env t)
in FStar_Util.Inl (_163_360))
end else begin
(let _163_361 = (desugar_exp env t)
in FStar_Util.Inr (_163_361))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_name : (FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun setpos env l -> if (l.FStar_Ident.str = "ref") then begin
(match ((FStar_Parser_DesugarEnv.try_lookup_lid env FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Identifier \'ref\' not found; include lib/FStar.ST.fst in your path"), ((FStar_Ident.range_of_lid l))))))
end
| Some (e) -> begin
(setpos e)
end)
end else begin
(let _163_370 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _163_370))
end)
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (

let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _64_1171 = e
in {FStar_Absyn_Syntax.n = _64_1171.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_1171.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _64_1171.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_1171.FStar_Absyn_Syntax.uvs}))
in (match ((let _163_388 = (unparen top)
in _163_388.FStar_Parser_AST.tm)) with
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

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _163_392 = (desugar_typ_or_exp env t)
in ((_163_392), (None))))))
in (let _163_393 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _163_393))))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(desugar_name setpos env l)
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let dt = (let _163_398 = (let _163_397 = (let _163_396 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in ((_163_396), (Some (FStar_Absyn_Syntax.Data_ctor))))
in (FStar_Absyn_Syntax.mk_Exp_fvar _163_397))
in (FStar_All.pipe_left pos _163_398))
in (match (args) with
| [] -> begin
dt
end
| _64_1195 -> begin
(

let args = (FStar_List.map (fun _64_1198 -> (match (_64_1198) with
| (t, imp) -> begin
(

let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _163_403 = (let _163_402 = (let _163_401 = (let _163_400 = (FStar_Absyn_Util.mk_exp_app dt args)
in ((_163_400), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_163_401))
in (FStar_Absyn_Syntax.mk_Exp_meta _163_402))
in (FStar_All.pipe_left setpos _163_403)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _64_1235 = (FStar_List.fold_left (fun _64_1207 pat -> (match (_64_1207) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _64_1210}, t) -> begin
(

let ftvs = (let _163_406 = (free_type_vars env t)
in (FStar_List.append _163_406 ftvs))
in (let _163_408 = (let _163_407 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _163_407))
in ((_163_408), (ftvs))))
end
| FStar_Parser_AST.PatTvar (a, _64_1222) -> begin
(let _163_410 = (let _163_409 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _163_409))
in ((_163_410), (ftvs)))
end
| FStar_Parser_AST.PatAscribed (_64_1226, t) -> begin
(let _163_412 = (let _163_411 = (free_type_vars env t)
in (FStar_List.append _163_411 ftvs))
in ((env), (_163_412)))
end
| _64_1231 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_64_1235) with
| (_64_1233, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _163_414 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _163_414 binders))
in (

let rec aux = (fun env bs sc_pat_opt _64_8 -> (match (_64_8) with
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

let _64_1258 = (desugar_binding_pat env p)
in (match (_64_1258) with
| (env, b, pat) -> begin
(

let _64_1318 = (match (b) with
| LetBinder (_64_1260) -> begin
(failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _163_423 = (binder_of_bnd b)
in ((_163_423), (sc_pat_opt)))
end
| VBinder (x, t, aq) -> begin
(

let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _64_1275) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _163_425 = (let _163_424 = (FStar_Absyn_Util.bvar_to_exp b)
in ((_163_424), (p)))
in Some (_163_425))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Absyn_Syntax.n), (p'.FStar_Absyn_Syntax.v))) with
| (FStar_Absyn_Syntax.Exp_bvar (_64_1289), _64_1292) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (

let sc = (let _163_432 = (let _163_431 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _163_430 = (let _163_429 = (FStar_Absyn_Syntax.varg sc)
in (let _163_428 = (let _163_427 = (let _163_426 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _163_426))
in (_163_427)::[])
in (_163_429)::_163_428))
in ((_163_431), (_163_430))))
in (FStar_Absyn_Syntax.mk_Exp_app _163_432 None top.FStar_Parser_AST.range))
in (

let p = (let _163_433 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((p'), (false)))::(((p), (false)))::[])))) None _163_433))
in Some (((sc), (p))))))
end
| (FStar_Absyn_Syntax.Exp_app (_64_1298, args), FStar_Absyn_Syntax.Pat_cons (_64_1303, _64_1305, pats)) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (

let sc = (let _163_439 = (let _163_438 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _163_437 = (let _163_436 = (let _163_435 = (let _163_434 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _163_434))
in (_163_435)::[])
in (FStar_List.append args _163_436))
in ((_163_438), (_163_437))))
in (FStar_Absyn_Syntax.mk_Exp_app _163_439 None top.FStar_Parser_AST.range))
in (

let p = (let _163_440 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((FStar_List.append pats ((((p), (false)))::[])))))) None _163_440))
in Some (((sc), (p))))))
end
| _64_1314 -> begin
(failwith "Impossible")
end)
end)
in ((((FStar_Util.Inr (b)), (aq))), (sc_pat_opt))))
end)
in (match (_64_1318) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _64_1322; FStar_Parser_AST.level = _64_1320}, arg, _64_1328) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env arg)
in (let _163_450 = (let _163_449 = (let _163_448 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _163_447 = (let _163_446 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _163_445 = (let _163_444 = (let _163_443 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _163_443))
in (_163_444)::[])
in (_163_446)::_163_445))
in ((_163_448), (_163_447))))
in (FStar_Absyn_Syntax.mk_Exp_app _163_449))
in (FStar_All.pipe_left pos _163_450)))
end
| FStar_Parser_AST.App (_64_1333) -> begin
(

let rec aux = (fun args e -> (match ((let _163_455 = (unparen e)
in _163_455.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _163_456 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _163_456))
in (aux ((arg)::args) e))
end
| _64_1345 -> begin
(

let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app ((head), (args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _163_462 = (let _163_461 = (let _163_460 = (let _163_459 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_163_459), (FStar_Absyn_Syntax.Sequence)))
in FStar_Absyn_Syntax.Meta_desugared (_163_460))
in (FStar_Absyn_Syntax.mk_Exp_meta _163_461))
in (FStar_All.pipe_left setpos _163_462))
end
| FStar_Parser_AST.LetOpen (_64_1352) -> begin
(failwith "let open in universes")
end
| FStar_Parser_AST.Let (is_rec, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (is_rec = FStar_Parser_AST.Rec)
in (

let ds_let_rec = (fun _64_1365 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _64_1369 -> (match (_64_1369) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _163_466 = (destruct_app_pattern env top_level p)
in ((_163_466), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _163_467 = (destruct_app_pattern env top_level p)
in ((_163_467), (def)))
end
| _64_1375 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_1380); FStar_Parser_AST.prange = _64_1377}, t) -> begin
if top_level then begin
(let _163_470 = (let _163_469 = (let _163_468 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_163_468))
in ((_163_469), ([]), (Some (t))))
in ((_163_470), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _64_1389) -> begin
if top_level then begin
(let _163_473 = (let _163_472 = (let _163_471 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_163_471))
in ((_163_472), ([]), (None)))
in ((_163_473), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _64_1393 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _64_1419 = (FStar_List.fold_left (fun _64_1397 _64_1406 -> (match (((_64_1397), (_64_1406))) with
| ((env, fnames), ((f, _64_1400, _64_1402), _64_1405)) -> begin
(

let _64_1416 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _64_1411 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_1411) with
| (env, xx) -> begin
((env), (FStar_Util.Inl (xx)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _163_476 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in ((_163_476), (FStar_Util.Inr (l))))
end)
in (match (_64_1416) with
| (env, lbname) -> begin
((env), ((lbname)::fnames))
end))
end)) ((env), ([])) funs)
in (match (_64_1419) with
| (env', fnames) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _64_1430 -> (match (_64_1430) with
| ((_64_1425, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _163_483 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _163_483 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _64_1437 -> begin
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

let _64_1450 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_64_1450) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_64_1452) -> begin
(failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(

let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]))), (body)))))
end
| VBinder (x, t, _64_1462) -> begin
(

let body = (desugar_exp env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _163_495 = (let _163_494 = (FStar_Absyn_Util.bvd_to_exp x t)
in ((_163_494), ((((pat), (None), (body)))::[])))
in (FStar_Absyn_Syntax.mk_Exp_match _163_495 None body.FStar_Absyn_Syntax.pos))
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
(let _163_508 = (let _163_507 = (let _163_506 = (desugar_exp env t1)
in (let _163_505 = (let _163_504 = (let _163_500 = (desugar_exp env t2)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range)), (None), (_163_500)))
in (let _163_503 = (let _163_502 = (let _163_501 = (desugar_exp env t3)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range)), (None), (_163_501)))
in (_163_502)::[])
in (_163_504)::_163_503))
in ((_163_506), (_163_505))))
in (FStar_Absyn_Syntax.mk_Exp_match _163_507))
in (FStar_All.pipe_left pos _163_508))
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

let desugar_branch = (fun _64_1501 -> (match (_64_1501) with
| (pat, wopt, b) -> begin
(

let _64_1504 = (desugar_match_pat env pat)
in (match (_64_1504) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _163_511 = (desugar_exp env e)
in Some (_163_511))
end)
in (

let b = (desugar_exp env b)
in ((pat), (wopt), (b))))
end))
end))
in (let _163_517 = (let _163_516 = (let _163_515 = (desugar_exp env e)
in (let _163_514 = (FStar_List.map desugar_branch branches)
in ((_163_515), (_163_514))))
in (FStar_Absyn_Syntax.mk_Exp_match _163_516))
in (FStar_All.pipe_left pos _163_517)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _163_523 = (let _163_522 = (let _163_521 = (desugar_exp env e)
in (let _163_520 = (desugar_typ env t)
in ((_163_521), (_163_520), (None))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _163_522))
in (FStar_All.pipe_left pos _163_523))
end
| FStar_Parser_AST.Record (_64_1515, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _64_1526 = (FStar_List.hd fields)
in (match (_64_1526) with
| (f, _64_1525) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _64_1532 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_64_1532) with
| (record, _64_1531) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _64_1540 -> (match (_64_1540) with
| (g, _64_1539) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_64_1544, e) -> begin
(let _163_531 = (qfn fn)
in ((_163_531), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _163_534 = (let _163_533 = (let _163_532 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_163_532), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_163_533))
in (Prims.raise _163_534))
end
| Some (x) -> begin
(let _163_535 = (qfn fn)
in ((_163_535), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _163_540 = (let _163_539 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _64_1556 -> (match (_64_1556) with
| (f, _64_1555) -> begin
(let _163_538 = (let _163_537 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _163_537))
in ((_163_538), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_DesugarEnv.constrname), (_163_539)))
in FStar_Parser_AST.Construct (_163_540))
end
| Some (e) -> begin
(

let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (

let xterm = (let _163_542 = (let _163_541 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_163_541))
in (FStar_Parser_AST.mk_term _163_542 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _163_545 = (let _163_544 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _64_1564 -> (match (_64_1564) with
| (f, _64_1563) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_163_544)))
in FStar_Parser_AST.Record (_163_545))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _64_1587); FStar_Absyn_Syntax.tk = _64_1584; FStar_Absyn_Syntax.pos = _64_1582; FStar_Absyn_Syntax.fvs = _64_1580; FStar_Absyn_Syntax.uvs = _64_1578}, args); FStar_Absyn_Syntax.tk = _64_1576; FStar_Absyn_Syntax.pos = _64_1574; FStar_Absyn_Syntax.fvs = _64_1572; FStar_Absyn_Syntax.uvs = _64_1570}, FStar_Absyn_Syntax.Data_app)) -> begin
(

let e = (let _163_555 = (let _163_554 = (let _163_553 = (let _163_552 = (let _163_551 = (let _163_550 = (let _163_549 = (let _163_548 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_163_548)))
in FStar_Absyn_Syntax.Record_ctor (_163_549))
in Some (_163_550))
in ((fv), (_163_551)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _163_552 None e.FStar_Absyn_Syntax.pos))
in ((_163_553), (args)))
in (FStar_Absyn_Syntax.mk_Exp_app _163_554))
in (FStar_All.pipe_left pos _163_555))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (FStar_Absyn_Syntax.Data_app))))))
end
| _64_1601 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _64_1608 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_64_1608) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_exp env e)
in (

let fn = (

let _64_1613 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_64_1613) with
| (ns, _64_1612) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _163_562 = (let _163_561 = (let _163_560 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (let _163_559 = (let _163_558 = (FStar_Absyn_Syntax.varg e)
in (_163_558)::[])
in ((_163_560), (_163_559))))
in (FStar_Absyn_Syntax.mk_Exp_app _163_561))
in (FStar_All.pipe_left pos _163_562)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| FStar_Parser_AST.Projector (ns, id) -> begin
(

let l = (FStar_Parser_DesugarEnv.qual ns id)
in (desugar_name setpos env l))
end
| FStar_Parser_AST.Discrim (lid) -> begin
(

let lid' = (FStar_Absyn_Util.mk_discriminator lid)
in (desugar_name setpos env lid'))
end
| _64_1627 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (

let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _64_1634 = t
in {FStar_Absyn_Syntax.n = _64_1634.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_1634.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _64_1634.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_1634.FStar_Absyn_Syntax.uvs}))
in (

let top = (unparen top)
in (

let head_and_args = (fun t -> (

let rec aux = (fun args t -> (match ((let _163_585 = (unparen t)
in _163_585.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _64_1652 -> begin
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
(let _163_586 = (desugar_exp env t)
in (FStar_All.pipe_right _163_586 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _163_587 = (desugar_exp env t)
in (FStar_All.pipe_right _163_587 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", (t1)::(_64_1666)::[]) -> begin
if (is_type env t1) then begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _163_590 = (flatten t1)
in (FStar_List.append _163_590 ((t2)::[])))
end
| _64_1680 -> begin
(t)::[]
end))
in (

let targs = (let _163_593 = (flatten top)
in (FStar_All.pipe_right _163_593 (FStar_List.map (fun t -> (let _163_592 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _163_592))))))
in (

let tup = (let _163_594 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _163_594))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))))
end else begin
(let _163_600 = (let _163_599 = (let _163_598 = (let _163_597 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _163_597))
in ((_163_598), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_163_599))
in (Prims.raise _163_600))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _163_601 = (desugar_exp env top)
in (FStar_All.pipe_right _163_601 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(

let args = (FStar_List.map (fun t -> (let _163_603 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _163_603))) args)
in (let _163_604 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _163_604 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _163_605 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _163_605))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = (Prims.parse_int "0")) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _163_606 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _163_606))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _163_607 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _163_607)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let t = (let _163_608 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _163_608))
in (

let args = (FStar_List.map (fun _64_1716 -> (match (_64_1716) with
| (t, imp) -> begin
(let _163_610 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _163_610))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let rec aux = (fun env bs _64_9 -> (match (_64_9) with
| [] -> begin
(

let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_List.rev bs)), (body)))))
end
| (hd)::tl -> begin
(

let _64_1734 = (desugar_binding_pat env hd)
in (match (_64_1734) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _163_622 = (let _163_621 = (let _163_620 = (let _163_619 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _163_619))
in ((_163_620), (hd.FStar_Parser_AST.prange)))
in FStar_Absyn_Syntax.Error (_163_621))
in (Prims.raise _163_622))
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
| FStar_Parser_AST.App (_64_1740) -> begin
(

let rec aux = (fun args e -> (match ((let _163_627 = (unparen e)
in _163_627.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(

let arg = (let _163_628 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _163_628))
in (aux ((arg)::args) e))
end
| _64_1752 -> begin
(

let head = (desugar_typ env e)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((head), (args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Product ([], t) -> begin
(failwith "Impossible: product with no binders")
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _64_1764 = (uncurry binders t)
in (match (_64_1764) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _64_10 -> (match (_64_10) with
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

let _64_1778 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_64_1778) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _64_1785) -> begin
(failwith "Missing binder in refinement")
end
| b -> begin
(

let _64_1799 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _64_1791), env) -> begin
((x), (env))
end
| _64_1796 -> begin
(failwith "impossible")
end)
in (match (_64_1799) with
| (b, env) -> begin
(

let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _163_639 = (desugar_exp env f)
in (FStar_All.pipe_right _163_639 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine ((b), (f)))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _163_647 = (let _163_646 = (let _163_645 = (desugar_typ env t)
in (let _163_644 = (desugar_kind env k)
in ((_163_645), (_163_644))))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _163_646))
in (FStar_All.pipe_left wpos _163_647))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _64_1833 = (FStar_List.fold_left (fun _64_1818 b -> (match (_64_1818) with
| (env, tparams, typs) -> begin
(

let _64_1822 = (desugar_exp_binder env b)
in (match (_64_1822) with
| (xopt, t) -> begin
(

let _64_1828 = (match (xopt) with
| None -> begin
(let _163_650 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in ((env), (_163_650)))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_64_1828) with
| (env, x) -> begin
(let _163_654 = (let _163_653 = (let _163_652 = (let _163_651 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _163_651))
in (_163_652)::[])
in (FStar_List.append typs _163_653))
in ((env), ((FStar_List.append tparams ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (None)))::[]))), (_163_654)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_64_1833) with
| (env, _64_1831, targs) -> begin
(

let tup = (let _163_655 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _163_655))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))
end))
end
| FStar_Parser_AST.Record (_64_1836) -> begin
(failwith "Unexpected record type")
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
| _64_1855 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _64_1857 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r))))))
in (

let pre_process_comp_typ = (fun t -> (

let _64_1868 = (head_and_args t)
in (match (_64_1868) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let _64_1894 = (FStar_All.pipe_right args (FStar_List.partition (fun _64_1876 -> (match (_64_1876) with
| (arg, _64_1875) -> begin
(match ((let _163_667 = (unparen arg)
in _163_667.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _64_1880; FStar_Parser_AST.level = _64_1878}, _64_1885, _64_1887) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _64_1891 -> begin
false
end)
end))))
in (match (_64_1894) with
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
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _163_668 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _163_668 FStar_Absyn_Const.prims_lid))) -> begin
(

let args = (FStar_List.map (fun _64_1909 -> (match (_64_1909) with
| (t, imp) -> begin
(let _163_670 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _163_670))
end)) args)
in (let _163_671 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _163_671 args)))
end
| _64_1912 -> begin
(desugar_typ env t)
end)
end)))
in (

let t = (pre_process_comp_typ t)
in (

let _64_1916 = (FStar_Absyn_Util.head_and_args t)
in (match (_64_1916) with
| (head, args) -> begin
(match ((let _163_673 = (let _163_672 = (FStar_Absyn_Util.compress_typ head)
in _163_672.FStar_Absyn_Syntax.n)
in ((_163_673), (args)))) with
| (FStar_Absyn_Syntax.Typ_const (eff), ((FStar_Util.Inl (result_typ), _64_1923))::rest) -> begin
(

let _64_1963 = (FStar_All.pipe_right rest (FStar_List.partition (fun _64_11 -> (match (_64_11) with
| (FStar_Util.Inr (_64_1929), _64_1932) -> begin
false
end
| (FStar_Util.Inl (t), _64_1937) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _64_1946; FStar_Absyn_Syntax.pos = _64_1944; FStar_Absyn_Syntax.fvs = _64_1942; FStar_Absyn_Syntax.uvs = _64_1940}, ((FStar_Util.Inr (_64_1951), _64_1954))::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _64_1960 -> begin
false
end)
end))))
in (match (_64_1963) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _64_12 -> (match (_64_12) with
| (FStar_Util.Inl (t), _64_1968) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_64_1971, ((FStar_Util.Inr (arg), _64_1975))::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _64_1981 -> begin
(failwith "impos")
end)
end
| _64_1983 -> begin
(failwith "impos")
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
(let _163_680 = (let _163_679 = (let _163_678 = (let _163_677 = (let _163_676 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((pat), (FStar_Absyn_Syntax.Meta_smt_pat)))))
in FStar_Util.Inr (_163_676))
in ((_163_677), (aq)))
in (_163_678)::[])
in (ens)::_163_679)
in (req)::_163_680)
end
| _64_1994 -> begin
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
(let _163_682 = (let _163_681 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _163_681))
in (fail _163_682))
end
end)
end))
end
| _64_1997 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _163_684 = (let _163_683 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _163_683))
in (fail _163_684))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (

let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (

let setpos = (fun kk -> (

let _64_2004 = kk
in {FStar_Absyn_Syntax.n = _64_2004.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_2004.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _64_2004.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_2004.FStar_Absyn_Syntax.uvs}))
in (

let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_2013; FStar_Ident.ident = _64_2011; FStar_Ident.nsstr = _64_2009; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_2022; FStar_Ident.ident = _64_2020; FStar_Ident.nsstr = _64_2018; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _163_696 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _163_696))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), ([]))), (FStar_Absyn_Syntax.mk_Kind_unknown))))
end
| _64_2030 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(

let _64_2038 = (uncurry bs k)
in (match (_64_2038) with
| (bs, k) -> begin
(

let rec aux = (fun env bs _64_13 -> (match (_64_13) with
| [] -> begin
(let _163_707 = (let _163_706 = (let _163_705 = (desugar_kind env k)
in (((FStar_List.rev bs)), (_163_705)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _163_706))
in (FStar_All.pipe_left pos _163_707))
end
| (hd)::tl -> begin
(

let _64_2049 = (let _163_709 = (let _163_708 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _163_708 hd))
in (FStar_All.pipe_right _163_709 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_64_2049) with
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

let args = (FStar_List.map (fun _64_2059 -> (match (_64_2059) with
| (t, b) -> begin
(

let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _163_711 = (desugar_typ_or_exp env t)
in ((_163_711), (qual))))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (FStar_Absyn_Syntax.mk_Kind_unknown)))))
end)
end
| _64_2063 -> begin
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
| _64_2074 -> begin
None
end))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _64_2079 = t
in {FStar_Absyn_Syntax.n = _64_2079.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_2079.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _64_2079.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_2079.FStar_Absyn_Syntax.uvs}))
in (

let desugar_quant = (fun q qt b pats body -> (

let tk = (desugar_binder env (

let _64_2087 = b
in {FStar_Parser_AST.b = _64_2087.FStar_Parser_AST.b; FStar_Parser_AST.brange = _64_2087.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _64_2087.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _163_747 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _163_747)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _64_2102 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_64_2102) with
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
| _64_2107 -> begin
(let _163_748 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
in (FStar_All.pipe_left setpos _163_748))
end)
in (

let body = (let _163_754 = (let _163_753 = (let _163_752 = (let _163_751 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_163_751)::[])
in ((_163_752), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _163_753))
in (FStar_All.pipe_left pos _163_754))
in (let _163_758 = (let _163_757 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange) FStar_Absyn_Syntax.kun)
in (let _163_756 = (let _163_755 = (FStar_Absyn_Syntax.targ body)
in (_163_755)::[])
in (FStar_Absyn_Util.mk_typ_app _163_757 _163_756)))
in (FStar_All.pipe_left setpos _163_758))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _64_2117 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_2117) with
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
| _64_2122 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
end)
in (

let body = (let _163_764 = (let _163_763 = (let _163_762 = (let _163_761 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_163_761)::[])
in ((_163_762), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _163_763))
in (FStar_All.pipe_left pos _163_764))
in (let _163_768 = (let _163_767 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) FStar_Absyn_Syntax.kun)
in (let _163_766 = (let _163_765 = (FStar_Absyn_Syntax.targ body)
in (_163_765)::[])
in (FStar_Absyn_Util.mk_typ_app _163_767 _163_766)))
in (FStar_All.pipe_left setpos _163_768))))))
end))
end
| _64_2126 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _163_783 = (q ((rest), (pats), (body)))
in (let _163_782 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _163_783 _163_782 FStar_Parser_AST.Formula)))
in (let _163_784 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _163_784 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _64_2140 -> begin
(failwith "impossible")
end))
in (match ((let _163_785 = (unparen f)
in _163_785.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (l), (FStar_Absyn_Syntax.dummyRange), (p))))))
end
| FStar_Parser_AST.Op ("==", (hd)::_args) -> begin
(

let args = (hd)::_args
in (

let args = (FStar_List.map (fun t -> (let _163_787 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _163_787))) args)
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
| (Some (conn), (_64_2166)::(_64_2164)::[]) -> begin
(let _163_791 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range) FStar_Absyn_Syntax.kun)
in (let _163_790 = (FStar_List.map (fun x -> (let _163_789 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _163_789))) args)
in (FStar_Absyn_Util.mk_typ_app _163_791 _163_790)))
end
| _64_2171 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _163_792 = (desugar_exp env f)
in (FStar_All.pipe_right _163_792 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _163_796 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range) FStar_Absyn_Syntax.kun)
in (let _163_795 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _163_794 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _163_794))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _163_796 _163_795)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _163_798 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _163_798)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _163_800 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _163_800)))
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
| _64_2233 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _163_801 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _163_801))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (

let _64_2236 = env
in {FStar_Parser_DesugarEnv.curmodule = _64_2236.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _64_2236.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _64_2236.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _64_2236.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _64_2236.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _64_2236.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _64_2236.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _64_2236.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _64_2236.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _64_2236.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _64_2236.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _163_806 = (desugar_type_binder env b)
in FStar_Util.Inl (_163_806))
end else begin
(let _163_807 = (desugar_exp_binder env b)
in FStar_Util.Inr (_163_807))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _64_2269 = (FStar_List.fold_left (fun _64_2244 b -> (match (_64_2244) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _64_2246 = b
in {FStar_Parser_AST.b = _64_2246.FStar_Parser_AST.b; FStar_Parser_AST.brange = _64_2246.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _64_2246.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _64_2256 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_64_2256) with
| (env, a) -> begin
((env), ((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _64_2264 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_2264) with
| (env, x) -> begin
((env), ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| _64_2266 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_64_2269) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _163_814 = (desugar_typ env t)
in ((Some (x)), (_163_814)))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _163_815 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in ((None), (_163_815)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _163_816 = (desugar_typ env t)
in ((None), (_163_816)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Absyn_Syntax.tun))
end
| _64_2283 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a type)"), (b.FStar_Parser_AST.brange)))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (

let fail = (fun _64_2287 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a kind)"), (b.FStar_Parser_AST.brange)))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _163_821 = (desugar_kind env t)
in ((Some (x)), (_163_821)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _163_822 = (desugar_kind env t)
in ((None), (_163_822)))
end
| FStar_Parser_AST.TVariable (x) -> begin
((Some (x)), ((

let _64_2298 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _64_2298.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _64_2298.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _64_2298.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _64_2298.FStar_Absyn_Syntax.uvs})))
end
| _64_2301 -> begin
(fail ())
end)))


let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (

let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_64_2312, k) -> begin
(aux bs k)
end
| _64_2317 -> begin
bs
end))
in (let _163_831 = (aux tps k)
in (FStar_All.pipe_right _163_831 FStar_Absyn_Util.name_binders))))


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

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _64_2331 -> (match (_64_2331) with
| (x, _64_2330) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (let _163_852 = (let _163_851 = (let _163_850 = (let _163_849 = (let _163_848 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _163_847 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_163_848), (_163_847))))
in (FStar_Absyn_Syntax.mk_Typ_app' _163_849 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _163_850))
in (_163_851)::[])
in (FStar_List.append imp_binders _163_852))
in (

let disc_type = (let _163_855 = (let _163_854 = (let _163_853 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _163_853 p))
in ((binders), (_163_854)))
in (FStar_Absyn_Syntax.mk_Typ_fun _163_855 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _163_858 = (let _163_857 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in ((disc_name), (disc_type), (_163_857), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Absyn_Syntax.Sig_val_decl (_163_858)))))))))))))


let mk_indexed_projectors = (fun fvq refine_domain env _64_2343 lid formals t -> (match (_64_2343) with
| (tc, tps, k) -> begin
(

let binders = (gather_tc_binders tps k)
in (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (

let projectee = (let _163_869 = (FStar_Absyn_Syntax.mk_ident (("projectee"), (p)))
in (let _163_868 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _163_869; FStar_Absyn_Syntax.realname = _163_868}))
in (

let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (

let arg_binder = (

let arg_typ = (let _163_872 = (let _163_871 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _163_870 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_163_871), (_163_870))))
in (FStar_Absyn_Syntax.mk_Typ_app' _163_872 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(

let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (

let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _163_882 = (let _163_881 = (let _163_880 = (let _163_879 = (let _163_878 = (let _163_877 = (let _163_876 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _163_875 = (let _163_874 = (let _163_873 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _163_873))
in (_163_874)::[])
in ((_163_876), (_163_875))))
in (FStar_Absyn_Syntax.mk_Exp_app _163_877 None p))
in (FStar_Absyn_Util.b2t _163_878))
in ((x), (_163_879)))
in (FStar_Absyn_Syntax.mk_Typ_refine _163_880 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _163_881))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _163_882))))
end)
in (

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _64_2360 -> (match (_64_2360) with
| (x, _64_2359) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (let _163_890 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(

let _64_2371 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_64_2371) with
| (field_name, _64_2370) -> begin
(

let proj = (let _163_887 = (let _163_886 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in ((_163_886), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Typ_app _163_887 None p))
in (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _64_2378 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_64_2378) with
| (field_name, _64_2377) -> begin
(

let proj = (let _163_889 = (let _163_888 = (FStar_Absyn_Util.fvar None field_name p)
in ((_163_888), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Exp_app _163_889 None p))
in (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end))))
in (FStar_All.pipe_right _163_890 FStar_List.flatten))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _163_892 = (FStar_All.pipe_right tps (FStar_List.map (fun _64_2385 -> (match (_64_2385) with
| (b, _64_2384) -> begin
((b), (Some (imp_tag)))
end))))
in (FStar_List.append _163_892 formals))
in (let _163_922 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(

let _64_2394 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_64_2394) with
| (field_name, _64_2393) -> begin
(

let kk = (let _163_896 = (let _163_895 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in ((binders), (_163_895)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _163_896 p))
in (FStar_Absyn_Syntax.Sig_tycon (((field_name), ([]), (kk), ([]), ([]), ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inl (a.FStar_Absyn_Syntax.v)))))::[]), ((FStar_Ident.range_of_lid field_name)))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _64_2401 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_64_2401) with
| (field_name, _64_2400) -> begin
(

let t = (let _163_899 = (let _163_898 = (let _163_897 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _163_897 p))
in ((binders), (_163_898)))
in (FStar_Absyn_Syntax.mk_Typ_fun _163_899 None p))
in (

let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (

let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inr (x.FStar_Absyn_Syntax.v)))))::[]))
in (

let impl = if (((let _163_902 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _163_902)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _163_904 = (let _163_903 = (FStar_Parser_DesugarEnv.current_module env)
in _163_903.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _163_904))) then begin
[]
end else begin
(

let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (

let as_imp = (fun _64_14 -> (match (_64_14) with
| Some (FStar_Absyn_Syntax.Implicit (_64_2409)) -> begin
true
end
| _64_2413 -> begin
false
end))
in (

let arg_pats = (let _163_919 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_64_2418), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _163_912 = (let _163_911 = (let _163_910 = (let _163_909 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_163_909))
in (pos _163_910))
in ((_163_911), ((as_imp imp))))
in (_163_912)::[])
end
end
| (FStar_Util.Inr (_64_2423), imp) -> begin
if ((i + ntps) = j) then begin
(let _163_914 = (let _163_913 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in ((_163_913), ((as_imp imp))))
in (_163_914)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _163_918 = (let _163_917 = (let _163_916 = (let _163_915 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_163_915))
in (pos _163_916))
in ((_163_917), ((as_imp imp))))
in (_163_918)::[])
end
end
end))))
in (FStar_All.pipe_right _163_919 FStar_List.flatten))
in (

let pat = (let _163_921 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv lid)), (Some (fvq)), (arg_pats)))) pos)
in (let _163_920 = (FStar_Absyn_Util.bvar_to_exp projection)
in ((_163_921), (None), (_163_920))))
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
in (FStar_All.pipe_right _163_922 FStar_List.flatten))))))))))))))
end))


let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _64_17 -> (match (_64_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _64_2440, _64_2442) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_15 -> (match (_64_15) with
| FStar_Absyn_Syntax.RecordConstructor (_64_2447) -> begin
true
end
| _64_2450 -> begin
false
end)))) then begin
false
end else begin
(

let _64_2456 = tycon
in (match (_64_2456) with
| (l, _64_2453, _64_2455) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > (Prims.parse_int "1"))
end
| _64_2460 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(

let cod = (FStar_Absyn_Util.comp_result cod)
in (

let qual = (match ((FStar_Util.find_map quals (fun _64_16 -> (match (_64_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor (((lid), (fns))))
end
| _64_2471 -> begin
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
| _64_2477 -> begin
[]
end))
end
| _64_2479 -> begin
[]
end))


let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _64_18 -> (match (_64_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _163_942 = (let _163_941 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_163_941))
in (FStar_Parser_AST.mk_term _163_942 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _64_2544 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _163_955 = (let _163_954 = (let _163_953 = (binder_to_term b)
in ((out), (_163_953), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_163_954))
in (FStar_Parser_AST.mk_term _163_955 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _64_19 -> (match (_64_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _64_2559 -> (match (_64_2559) with
| (x, t, _64_2558) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Absyn_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _163_961 = (let _163_960 = (let _163_959 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_163_959))
in (FStar_Parser_AST.mk_term _163_960 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _163_961 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _163_963 = (FStar_All.pipe_right fields (FStar_List.map (fun _64_2568 -> (match (_64_2568) with
| (x, _64_2565, _64_2567) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_163_963)))))))
end
| _64_2570 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _64_20 -> (match (_64_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _64_2584 = (typars_of_binders _env binders)
in (match (_64_2584) with
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

let tconstr = (let _163_974 = (let _163_973 = (let _163_972 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_163_972))
in (FStar_Parser_AST.mk_term _163_973 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _163_974 binders))
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
| _64_2595 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparam = (fun env _64_21 -> (match (_64_21) with
| (FStar_Util.Inr (x), _64_2602) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _64_2607) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (

let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (_64_2611))::[] -> begin
(

let tc = (FStar_List.hd tcs)
in (

let _64_2622 = (desugar_abstract_tc quals env [] tc)
in (match (_64_2622) with
| (_64_2616, _64_2618, se, _64_2621) -> begin
(

let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(

let _64_2623 = (let _163_984 = (FStar_Range.string_of_range rng)
in (let _163_983 = (let _163_982 = (let _163_981 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _163_981 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _163_982 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _163_984 _163_983)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))
end)))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _64_2636 = (typars_of_binders env binders)
in (match (_64_2636) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _64_22 -> (match (_64_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _64_2641 -> begin
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

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_23 -> (match (_64_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _64_2649 -> begin
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
in (let _163_990 = (let _163_989 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _163_988 = (FStar_All.pipe_right quals (FStar_List.filter (fun _64_24 -> (match (_64_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _64_2655 -> begin
true
end))))
in ((_163_989), (typars), (c), (_163_988), (rng))))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_163_990)))
end else begin
(

let t = (desugar_typ env' t)
in (let _163_992 = (let _163_991 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_163_991), (typars), (k), (t), (quals), (rng)))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_163_992)))
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_64_2660))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _64_2666 = (tycon_record_as_variant trec)
in (match (_64_2666) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_64_2670)::_64_2668 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _64_2681 = et
in (match (_64_2681) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_64_2683) -> begin
(

let trec = tc
in (

let _64_2688 = (tycon_record_as_variant trec)
in (match (_64_2688) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _64_2700 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_64_2700) with
| (env, _64_2697, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _64_2712 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_64_2712) with
| (env, _64_2709, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _64_2714 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _64_2717 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_64_2717) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _64_26 -> (match (_64_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _64_2724, _64_2726, _64_2728, _64_2730), t, quals) -> begin
(

let env_tps = (push_tparams env tpars)
in (

let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev (((id), (tpars), (k), (t), ([]), (rng))))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _64_2744, tags, _64_2747), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let env_tps = (push_tparams env tpars)
in (

let _64_2780 = (let _163_1008 = (FStar_All.pipe_right constrs (FStar_List.map (fun _64_2762 -> (match (_64_2762) with
| (id, topt, _64_2760, of_notation) -> begin
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
(failwith "Impossible")
end
| Some (t) -> begin
t
end)
end
in (

let t = (let _163_1003 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _163_1002 = (close env_tps t)
in (desugar_typ _163_1003 _163_1002)))
in (

let name = (FStar_Parser_DesugarEnv.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _64_25 -> (match (_64_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _64_2776 -> begin
[]
end))))
in (let _163_1007 = (let _163_1006 = (let _163_1005 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in ((name), (_163_1005), (tycon), (quals), (mutuals), (rng)))
in FStar_Absyn_Syntax.Sig_datacon (_163_1006))
in ((name), (_163_1007)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _163_1008))
in (match (_64_2780) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon (((tname), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))::constrs
end))))
end
| _64_2782 -> begin
(failwith "impossible")
end))))
in (

let bundle = (let _163_1010 = (let _163_1009 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_163_1009), (rng)))
in FStar_Absyn_Syntax.Sig_bundle (_163_1010))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _64_27 -> (match (_64_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _64_2792, constrs, quals, _64_2796) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _64_2800 -> begin
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
(failwith "impossible")
end)))))))))))


let desugar_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.binder Prims.list) = (fun env binders -> (

let _64_2831 = (FStar_List.fold_left (fun _64_2809 b -> (match (_64_2809) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _64_2818 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_64_2818) with
| (env, a) -> begin
(let _163_1019 = (let _163_1018 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_163_1018)::binders)
in ((env), (_163_1019)))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _64_2826 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_64_2826) with
| (env, x) -> begin
(let _163_1021 = (let _163_1020 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_163_1020)::binders)
in ((env), (_163_1021)))
end))
end
| _64_2828 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_64_2831) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Absyn_Syntax.qualifier = (fun r _64_28 -> (match (_64_28) with
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
| (FStar_Parser_AST.Reflectable) | (FStar_Parser_AST.Reifiable) | (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Irreducible) | (FStar_Parser_AST.Noeq) | (FStar_Parser_AST.Unopteq) | (FStar_Parser_AST.Visible) | (FStar_Parser_AST.Unfold_for_unification_and_vcgen) | (FStar_Parser_AST.NoExtract) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("The noextract qualifier is supported only with the --universes option"), (r)))))
end
| FStar_Parser_AST.Inline_for_extraction -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("This qualifier is supported only with the --universes option"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _64_29 -> (match (_64_29) with
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
| FStar_Parser_AST.Fsdoc (_64_2863) -> begin
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
| FStar_Parser_AST.Include (_64_2874) -> begin
(failwith "include not supported by legacy desugaring")
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _163_1039 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in ((_163_1039), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = if is_effect then begin
(FStar_Parser_AST.Effect)::d.FStar_Parser_AST.quals
end else begin
d.FStar_Parser_AST.quals
end
in (

let tcs = (FStar_List.map (fun _64_2888 -> (match (_64_2888) with
| (x, _64_2887) -> begin
x
end)) tcs)
in (let _163_1041 = (trans_quals quals)
in (desugar_tycon env d.FStar_Parser_AST.drange _163_1041 tcs))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (match ((let _163_1043 = (let _163_1042 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _163_1042))
in _163_1043.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _64_2897) -> begin
(

let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _64_2904 -> begin
(failwith "impossible")
end))))
in (

let quals = (match (quals) with
| (_64_2909)::_64_2907 -> begin
(trans_quals quals)
end
| _64_2912 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _64_30 -> (match (_64_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_64_2921); FStar_Absyn_Syntax.lbtyp = _64_2919; FStar_Absyn_Syntax.lbeff = _64_2917; FStar_Absyn_Syntax.lbdef = _64_2915} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _64_2929; FStar_Absyn_Syntax.lbeff = _64_2927; FStar_Absyn_Syntax.lbdef = _64_2925} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (

let s = FStar_Absyn_Syntax.Sig_let (((lbs), (d.FStar_Parser_AST.drange), (lids), (quals)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in ((env), ((s)::[]))))))
end
| _64_2937 -> begin
(failwith "Desugaring a let did not produce a let")
end))
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_exp env t)
in (

let se = FStar_Absyn_Syntax.Sig_main (((e), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (id, t) -> begin
(

let f = (desugar_formula env t)
in (let _163_1049 = (let _163_1048 = (let _163_1047 = (let _163_1046 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_163_1046), (f), ((FStar_Absyn_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_assume (_163_1047))
in (_163_1048)::[])
in ((env), (_163_1049))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t = (let _163_1050 = (close_fun env t)
in (desugar_typ env _163_1050))
in (

let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _163_1051 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_163_1051)
end else begin
(trans_quals quals)
end
in (

let se = (let _163_1053 = (let _163_1052 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_163_1052), (t), (quals), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_val_decl (_163_1053))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[])))))))
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

let t = (let _163_1058 = (let _163_1057 = (let _163_1054 = (FStar_Absyn_Syntax.null_v_binder t)
in (_163_1054)::[])
in (let _163_1056 = (let _163_1055 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _163_1055))
in ((_163_1057), (_163_1056))))
in (FStar_Absyn_Syntax.mk_Typ_fun _163_1058 None d.FStar_Parser_AST.drange))
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

let _64_2989 = (desugar_binders env binders)
in (match (_64_2989) with
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
| FStar_Parser_AST.NewEffectForFree (_64_2995) -> begin
(failwith "effects for free only supported in conjunction with --universes")
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let env0 = env
in (

let _64_3007 = (desugar_binders env eff_binders)
in (match (_64_3007) with
| (env, binders) -> begin
(

let defn = (desugar_typ env defn)
in (

let _64_3011 = (FStar_Absyn_Util.head_and_args defn)
in (match (_64_3011) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _163_1063 = (let _163_1062 = (let _163_1061 = (let _163_1060 = (let _163_1059 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat _163_1059 " not found"))
in (Prims.strcat "Effect " _163_1060))
in ((_163_1061), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_163_1062))
in (Prims.raise _163_1063))
end
| Some (ed) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (

let sub = (FStar_Absyn_Util.subst_typ subst)
in (

let ed = (let _163_1081 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _163_1080 = (trans_quals quals)
in (let _163_1079 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _163_1078 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _163_1077 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _163_1076 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _163_1075 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _163_1074 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _163_1073 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _163_1072 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _163_1071 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _163_1070 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _163_1069 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _163_1068 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _163_1067 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _163_1066 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _163_1065 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _163_1081; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _163_1080; FStar_Absyn_Syntax.signature = _163_1079; FStar_Absyn_Syntax.ret = _163_1078; FStar_Absyn_Syntax.bind_wp = _163_1077; FStar_Absyn_Syntax.bind_wlp = _163_1076; FStar_Absyn_Syntax.if_then_else = _163_1075; FStar_Absyn_Syntax.ite_wp = _163_1074; FStar_Absyn_Syntax.ite_wlp = _163_1073; FStar_Absyn_Syntax.wp_binop = _163_1072; FStar_Absyn_Syntax.wp_as_type = _163_1071; FStar_Absyn_Syntax.close_wp = _163_1070; FStar_Absyn_Syntax.close_wp_t = _163_1069; FStar_Absyn_Syntax.assert_p = _163_1068; FStar_Absyn_Syntax.assume_p = _163_1067; FStar_Absyn_Syntax.null_wp = _163_1066; FStar_Absyn_Syntax.trivial = _163_1065})))))))))))))))))
in (

let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)
end
| _64_3023 -> begin
(let _163_1085 = (let _163_1084 = (let _163_1083 = (let _163_1082 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _163_1082 " is not an effect"))
in ((_163_1083), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_163_1084))
in (Prims.raise _163_1085))
end)
end)))
end))))
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, _actions)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let env0 = env
in (

let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (

let _64_3037 = (desugar_binders env eff_binders)
in (match (_64_3037) with
| (env, binders) -> begin
(

let eff_k = (desugar_kind env eff_kind)
in (

let _64_3048 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _64_3041 decl -> (match (_64_3041) with
| (env, out) -> begin
(

let _64_3045 = (desugar_decl env decl)
in (match (_64_3045) with
| (env, ses) -> begin
(let _163_1089 = (let _163_1088 = (FStar_List.hd ses)
in (_163_1088)::out)
in ((env), (_163_1089)))
end))
end)) ((env), ([]))))
in (match (_64_3048) with
| (env, decls) -> begin
(

let decls = (FStar_List.rev decls)
in (

let lookup = (fun s -> (match ((let _163_1093 = (let _163_1092 = (FStar_Absyn_Syntax.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.qualify env _163_1092))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _163_1093))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Monad " (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat " expects definition of " s)))), (d.FStar_Parser_AST.drange)))))
end
| Some (t) -> begin
t
end))
in (

let ed = (let _163_1109 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _163_1108 = (trans_quals quals)
in (let _163_1107 = (lookup "return")
in (let _163_1106 = (lookup "bind_wp")
in (let _163_1105 = (lookup "bind_wlp")
in (let _163_1104 = (lookup "if_then_else")
in (let _163_1103 = (lookup "ite_wp")
in (let _163_1102 = (lookup "ite_wlp")
in (let _163_1101 = (lookup "wp_binop")
in (let _163_1100 = (lookup "wp_as_type")
in (let _163_1099 = (lookup "close_wp")
in (let _163_1098 = (lookup "close_wp_t")
in (let _163_1097 = (lookup "assert_p")
in (let _163_1096 = (lookup "assume_p")
in (let _163_1095 = (lookup "null_wp")
in (let _163_1094 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _163_1109; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _163_1108; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _163_1107; FStar_Absyn_Syntax.bind_wp = _163_1106; FStar_Absyn_Syntax.bind_wlp = _163_1105; FStar_Absyn_Syntax.if_then_else = _163_1104; FStar_Absyn_Syntax.ite_wp = _163_1103; FStar_Absyn_Syntax.ite_wlp = _163_1102; FStar_Absyn_Syntax.wp_binop = _163_1101; FStar_Absyn_Syntax.wp_as_type = _163_1100; FStar_Absyn_Syntax.close_wp = _163_1099; FStar_Absyn_Syntax.close_wp_t = _163_1098; FStar_Absyn_Syntax.assert_p = _163_1097; FStar_Absyn_Syntax.assume_p = _163_1096; FStar_Absyn_Syntax.null_wp = _163_1095; FStar_Absyn_Syntax.trivial = _163_1094}))))))))))))))))
in (

let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)))
end)))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _163_1116 = (let _163_1115 = (let _163_1114 = (let _163_1113 = (let _163_1112 = (FStar_Absyn_Print.sli l)
in (Prims.strcat _163_1112 " not found"))
in (Prims.strcat "Effect name " _163_1113))
in ((_163_1114), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_163_1115))
in (Prims.raise _163_1116))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let non_reifiable = (fun _64_31 -> (match (_64_31) with
| FStar_Parser_AST.NonReifiableLift (f) -> begin
f
end
| _64_3071 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected reifiable sub-effect"), (d.FStar_Parser_AST.drange)))))
end))
in (

let lift = (let _163_1119 = (non_reifiable l.FStar_Parser_AST.lift_op)
in (desugar_typ env _163_1119))
in (

let se = FStar_Absyn_Syntax.Sig_sub_effect ((({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))))))
end)))


let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _64_3079 d -> (match (_64_3079) with
| (env, sigelts) -> begin
(

let _64_3083 = (desugar_decl env d)
in (match (_64_3083) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]


let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let open_ns = (fun mname d -> (

let d = if ((FStar_List.length mname.FStar_Ident.ns) <> (Prims.parse_int "0")) then begin
(let _163_1144 = (let _163_1143 = (let _163_1141 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_163_1141))
in (let _163_1142 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _163_1143 _163_1142 [])))
in (_163_1144)::d)
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

let _64_3110 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _163_1146 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _163_1145 = (open_ns mname decls)
in ((_163_1146), (mname), (_163_1145), (true))))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _163_1148 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _163_1147 = (open_ns mname decls)
in ((_163_1148), (mname), (_163_1147), (false))))
end)
in (match (_64_3110) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _64_3113 = (desugar_decls env decls)
in (match (_64_3113) with
| (env, sigelts) -> begin
(

let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in ((env), (modul), (pop_when_done)))
end))
end)))))


let desugar_partial_modul : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun curmod env m -> (

let m = if false then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, _64_3124, _64_3126) -> begin
(failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _64_3134 = (desugar_modul_common curmod env m)
in (match (_64_3134) with
| (x, y, _64_3133) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (

let _64_3140 = (desugar_modul_common None env m)
in (match (_64_3140) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (

let _64_3142 = if (FStar_Options.dump_module modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _163_1159 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _163_1159))
end else begin
()
end
in (let _163_1160 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in ((_163_1160), (modul)))))
end)))


let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (

let _64_3155 = (FStar_List.fold_left (fun _64_3148 m -> (match (_64_3148) with
| (env, mods) -> begin
(

let _64_3152 = (desugar_modul env m)
in (match (_64_3152) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_64_3155) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (

let _64_3160 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_64_3160) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (

let _64_3161 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _64_3161.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _64_3161.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _64_3161.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _64_3161.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _64_3161.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _64_3161.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _64_3161.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _64_3161.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _64_3161.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _64_3161.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _64_3161.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))





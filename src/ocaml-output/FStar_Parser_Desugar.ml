
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


let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _157_17 = (let _157_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_157_16))
in (FStar_Parser_AST.mk_term _157_17 r FStar_Parser_AST.Kind)))


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
(let _157_28 = (let _157_26 = (FStar_Util.char_at s i)
in (name_of_char _157_26))
in (let _157_27 = (aux (i + (Prims.parse_int "1")))
in (_157_28)::_157_27))
end)
in (let _157_30 = (let _157_29 = (aux (Prims.parse_int "0"))
in (FStar_String.concat "_" _157_29))
in (Prims.strcat "op_" _157_30)))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _157_40 = (let _157_39 = (let _157_38 = (let _157_37 = (compile_op n s)
in ((_157_37), (r)))
in (FStar_Absyn_Syntax.mk_ident _157_38))
in (_157_39)::[])
in (FStar_All.pipe_right _157_40 FStar_Absyn_Syntax.lid_of_ids)))


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
in (match ((let _157_53 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _157_53))) with
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
(match ((let _157_64 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _157_64))) with
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
(match ((let _157_71 = (unparen t)
in _157_71.FStar_Parser_AST.tm)) with
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
(let _157_76 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _157_76 Prims.fst))
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
(match ((let _157_79 = (unparen t)
in _157_79.FStar_Parser_AST.tm)) with
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


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _157_90 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _157_90)))


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
(let _157_97 = (free_type_vars env term)
in ((env), (_157_97)))
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
(let _157_98 = (free_type_vars env t)
in ((env), (_157_98)))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _157_101 = (unparen t)
in _157_101.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _62_497 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_62_542, ts) -> begin
(FStar_List.collect (fun _62_549 -> (match (_62_549) with
| (t, _62_548) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_62_551, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _62_558) -> begin
(let _157_104 = (free_type_vars env t1)
in (let _157_103 = (free_type_vars env t2)
in (FStar_List.append _157_104 _157_103)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _62_567 = (free_type_vars_b env b)
in (match (_62_567) with
| (env, f) -> begin
(let _157_105 = (free_type_vars env t)
in (FStar_List.append f _157_105))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _62_583 = (FStar_List.fold_left (fun _62_576 binder -> (match (_62_576) with
| (env, free) -> begin
(

let _62_580 = (free_type_vars_b env binder)
in (match (_62_580) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_62_583) with
| (env, free) -> begin
(let _157_108 = (free_type_vars env body)
in (FStar_List.append free _157_108))
end))
end
| FStar_Parser_AST.Project (t, _62_586) -> begin
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

let rec aux = (fun args t -> (match ((let _157_115 = (unparen t)
in _157_115.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _62_638 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _157_120 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _157_120))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _157_124 = (let _157_123 = (let _157_122 = (kind_star x.FStar_Ident.idRange)
in ((x), (_157_122)))
in FStar_Parser_AST.TAnnotated (_157_123))
in (FStar_Parser_AST.mk_binder _157_124 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _157_129 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _157_129))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _157_133 = (let _157_132 = (let _157_131 = (kind_star x.FStar_Ident.idRange)
in ((x), (_157_131)))
in FStar_Parser_AST.TAnnotated (_157_132))
in (FStar_Parser_AST.mk_binder _157_133 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _157_134 = (unlabel t)
in _157_134.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_62_651) -> begin
t
end
| _62_654 -> begin
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
| _62_664 -> begin
((bs), (t))
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _62_668) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_62_674); FStar_Parser_AST.prange = _62_672}, _62_678) -> begin
true
end
| _62_682 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _62_694 = (destruct_app_pattern env is_top_level p)
in (match (_62_694) with
| (name, args, _62_693) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _62_699); FStar_Parser_AST.prange = _62_696}, args) when is_top_level -> begin
(let _157_148 = (let _157_147 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_157_147))
in ((_157_148), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _62_710); FStar_Parser_AST.prange = _62_707}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _62_718 -> begin
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
| TBinder (_62_721) -> begin
_62_721
end))


let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_62_724) -> begin
_62_724
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_62_727) -> begin
_62_727
end))


let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _62_3 -> (match (_62_3) with
| TBinder (a, k, aq) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), (aq))
end
| VBinder (x, t, aq) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (aq))
end
| _62_740 -> begin
(FStar_All.failwith "Impossible")
end))


let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _62_4 -> (match (_62_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _62_747 -> begin
None
end))


let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either  ->  (FStar_Absyn_Syntax.binder * FStar_Parser_DesugarEnv.env) = (fun env imp _62_5 -> (match (_62_5) with
| FStar_Util.Inl (None, k) -> begin
(let _157_201 = (FStar_Absyn_Syntax.null_t_binder k)
in ((_157_201), (env)))
end
| FStar_Util.Inr (None, t) -> begin
(let _157_202 = (FStar_Absyn_Syntax.null_v_binder t)
in ((_157_202), (env)))
end
| FStar_Util.Inl (Some (a), k) -> begin
(

let _62_766 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_62_766) with
| (env, a) -> begin
((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual imp)))), (env))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _62_774 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_774) with
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
| _62_784 -> begin
(let _157_213 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _157_213))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (((f), (msg), (polarity)))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (

let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _157_217 = (let _157_216 = (aux g)
in FStar_Parser_AST.Paren (_157_216))
in (FStar_Parser_AST.mk_term _157_217 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", (f1)::(f2)::[]) -> begin
(let _157_223 = (let _157_222 = (let _157_221 = (let _157_220 = (aux f1)
in (let _157_219 = (let _157_218 = (aux f2)
in (_157_218)::[])
in (_157_220)::_157_219))
in (("/\\"), (_157_221)))
in FStar_Parser_AST.Op (_157_222))
in (FStar_Parser_AST.mk_term _157_223 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _157_227 = (let _157_226 = (let _157_225 = (aux f2)
in (let _157_224 = (aux f3)
in ((f1), (_157_225), (_157_224))))
in FStar_Parser_AST.If (_157_226))
in (FStar_Parser_AST.mk_term _157_227 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _157_230 = (let _157_229 = (let _157_228 = (aux g)
in ((binders), (_157_228)))
in FStar_Parser_AST.Abs (_157_229))
in (FStar_Parser_AST.mk_term _157_230 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _62_806 -> begin
(label f)
end))
in (aux f))))


let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _62_810 -> (match (_62_810) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))


let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _62_6 -> (match (_62_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _62_821 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
((l), (e), (y))
end
| _62_826 -> begin
(

let _62_829 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_62_829) with
| (e, x) -> begin
(((FStar_Util.Inr (x))::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _62_7 -> (match (_62_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _62_838 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
((l), (e), (b))
end
| _62_843 -> begin
(

let _62_846 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_62_846) with
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
| FStar_Parser_AST.PatOp (_62_857) -> begin
(FStar_All.failwith "let op not supported in stratified")
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _62_871 = (aux loc env p)
in (match (_62_871) with
| (loc, env, var, p, _62_870) -> begin
(

let _62_888 = (FStar_List.fold_left (fun _62_875 p -> (match (_62_875) with
| (loc, env, ps) -> begin
(

let _62_884 = (aux loc env p)
in (match (_62_884) with
| (loc, env, _62_880, p, _62_883) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_62_888) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (

let _62_890 = (let _157_307 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _157_307))
in ((loc), (env), (var), (pat), (false))))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_62_897) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(

let _62_903 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (((x), (imp))); FStar_Parser_AST.prange = _62_903.FStar_Parser_AST.prange})
end
| _62_906 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
p
end
in (

let _62_913 = (aux loc env p)
in (match (_62_913) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_62_915) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _62_919, aq) -> begin
(let _157_309 = (let _157_308 = (desugar_kind env t)
in ((x), (_157_308), (aq)))
in TBinder (_157_309))
end
| VBinder (x, _62_925, aq) -> begin
(

let t = (close_fun env t)
in (let _157_311 = (let _157_310 = (desugar_typ env t)
in ((x), (_157_310), (aq)))
in VBinder (_157_311)))
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
in (let _157_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((a), (FStar_Absyn_Syntax.kun), (aq)))), (_157_312), (imp))))
end else begin
(

let _62_941 = (resolvea loc env a)
in (match (_62_941) with
| (loc, env, abvd) -> begin
(let _157_313 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((abvd), (FStar_Absyn_Syntax.kun), (aq)))), (_157_313), (imp)))
end))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (

let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _157_314 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_157_314), (false)))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _157_315 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_157_315), (false))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _62_957 = (resolvex loc env x)
in (match (_62_957) with
| (loc, env, xbvd) -> begin
(let _157_316 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((xbvd), (FStar_Absyn_Syntax.tun), (aq)))), (_157_316), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _157_317 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), ([])))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_157_317), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _62_963}, args) -> begin
(

let _62_985 = (FStar_List.fold_right (fun arg _62_974 -> (match (_62_974) with
| (loc, env, args) -> begin
(

let _62_981 = (aux loc env arg)
in (match (_62_981) with
| (loc, env, _62_978, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_62_985) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _157_320 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_157_320), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_62_989) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _62_1009 = (FStar_List.fold_right (fun pat _62_997 -> (match (_62_997) with
| (loc, env, pats) -> begin
(

let _62_1005 = (aux loc env pat)
in (match (_62_1005) with
| (loc, env, _62_1001, pat, _62_1004) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_62_1009) with
| (loc, env, pats) -> begin
(

let pat = (let _157_327 = (let _157_326 = (let _157_325 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _157_325))
in (FStar_All.pipe_left _157_326 (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ([]))))))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((hd), (false)))::(((tl), (false)))::[]))))))) pats _157_327))
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _62_1035 = (FStar_List.fold_left (fun _62_1022 p -> (match (_62_1022) with
| (loc, env, pats) -> begin
(

let _62_1031 = (aux loc env p)
in (match (_62_1031) with
| (loc, env, _62_1027, pat, _62_1030) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_62_1035) with
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
| FStar_Absyn_Syntax.Exp_fvar (v, _62_1041) -> begin
v
end
| _62_1045 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _157_330 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_157_330), (false))))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _62_1055 = (FStar_List.hd fields)
in (match (_62_1055) with
| (f, _62_1054) -> begin
(

let _62_1059 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_62_1059) with
| (record, _62_1058) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _62_1062 -> (match (_62_1062) with
| (f, p) -> begin
(let _157_332 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in ((_157_332), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _62_1067 -> (match (_62_1067) with
| (f, _62_1066) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _62_1071 -> (match (_62_1071) with
| (g, _62_1070) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_62_1074, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _62_1086 = (aux loc env app)
in (match (_62_1086) with
| (env, e, b, p, _62_1085) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _62_1089, args) -> begin
(let _157_340 = (let _157_339 = (let _157_338 = (let _157_337 = (let _157_336 = (let _157_335 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_157_335)))
in FStar_Absyn_Syntax.Record_ctor (_157_336))
in Some (_157_337))
in ((fv), (_157_338), (args)))
in FStar_Absyn_Syntax.Pat_cons (_157_339))
in (FStar_All.pipe_left pos _157_340))
end
| _62_1094 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _62_1103 = (aux [] env p)
in (match (_62_1103) with
| (_62_1097, env, b, p, _62_1102) -> begin
((env), (b), (p))
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _62_1109) -> begin
(let _157_346 = (let _157_345 = (let _157_344 = (FStar_Parser_DesugarEnv.qualify env x)
in ((_157_344), (FStar_Absyn_Syntax.tun)))
in LetBinder (_157_345))
in ((env), (_157_346), (None)))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _62_1116); FStar_Parser_AST.prange = _62_1113}, t) -> begin
(let _157_350 = (let _157_349 = (let _157_348 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _157_347 = (desugar_typ env t)
in ((_157_348), (_157_347))))
in LetBinder (_157_349))
in ((env), (_157_350), (None)))
end
| _62_1124 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _62_1128 = (desugar_data_pat env p)
in (match (_62_1128) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _62_1139 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _62_1143 env pat -> (

let _62_1151 = (desugar_data_pat env pat)
in (match (_62_1151) with
| (env, _62_1149, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _157_360 = (desugar_typ env t)
in FStar_Util.Inl (_157_360))
end else begin
(let _157_361 = (desugar_exp env t)
in FStar_Util.Inr (_157_361))
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
(let _157_370 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _157_370))
end)
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (

let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _62_1171 = e
in {FStar_Absyn_Syntax.n = _62_1171.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_1171.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _62_1171.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_1171.FStar_Absyn_Syntax.uvs}))
in (match ((let _157_388 = (unparen top)
in _157_388.FStar_Parser_AST.tm)) with
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

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _157_392 = (desugar_typ_or_exp env t)
in ((_157_392), (None))))))
in (let _157_393 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _157_393))))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(desugar_name setpos env l)
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let dt = (let _157_398 = (let _157_397 = (let _157_396 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in ((_157_396), (Some (FStar_Absyn_Syntax.Data_ctor))))
in (FStar_Absyn_Syntax.mk_Exp_fvar _157_397))
in (FStar_All.pipe_left pos _157_398))
in (match (args) with
| [] -> begin
dt
end
| _62_1195 -> begin
(

let args = (FStar_List.map (fun _62_1198 -> (match (_62_1198) with
| (t, imp) -> begin
(

let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _157_403 = (let _157_402 = (let _157_401 = (let _157_400 = (FStar_Absyn_Util.mk_exp_app dt args)
in ((_157_400), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_157_401))
in (FStar_Absyn_Syntax.mk_Exp_meta _157_402))
in (FStar_All.pipe_left setpos _157_403)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _62_1235 = (FStar_List.fold_left (fun _62_1207 pat -> (match (_62_1207) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _62_1210}, t) -> begin
(

let ftvs = (let _157_406 = (free_type_vars env t)
in (FStar_List.append _157_406 ftvs))
in (let _157_408 = (let _157_407 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _157_407))
in ((_157_408), (ftvs))))
end
| FStar_Parser_AST.PatTvar (a, _62_1222) -> begin
(let _157_410 = (let _157_409 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _157_409))
in ((_157_410), (ftvs)))
end
| FStar_Parser_AST.PatAscribed (_62_1226, t) -> begin
(let _157_412 = (let _157_411 = (free_type_vars env t)
in (FStar_List.append _157_411 ftvs))
in ((env), (_157_412)))
end
| _62_1231 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_62_1235) with
| (_62_1233, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _157_414 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _157_414 binders))
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

let _62_1258 = (desugar_binding_pat env p)
in (match (_62_1258) with
| (env, b, pat) -> begin
(

let _62_1318 = (match (b) with
| LetBinder (_62_1260) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _157_423 = (binder_of_bnd b)
in ((_157_423), (sc_pat_opt)))
end
| VBinder (x, t, aq) -> begin
(

let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _62_1275) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _157_425 = (let _157_424 = (FStar_Absyn_Util.bvar_to_exp b)
in ((_157_424), (p)))
in Some (_157_425))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Absyn_Syntax.n), (p'.FStar_Absyn_Syntax.v))) with
| (FStar_Absyn_Syntax.Exp_bvar (_62_1289), _62_1292) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (

let sc = (let _157_432 = (let _157_431 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _157_430 = (let _157_429 = (FStar_Absyn_Syntax.varg sc)
in (let _157_428 = (let _157_427 = (let _157_426 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _157_426))
in (_157_427)::[])
in (_157_429)::_157_428))
in ((_157_431), (_157_430))))
in (FStar_Absyn_Syntax.mk_Exp_app _157_432 None top.FStar_Parser_AST.range))
in (

let p = (let _157_433 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((p'), (false)))::(((p), (false)))::[])))) None _157_433))
in Some (((sc), (p))))))
end
| (FStar_Absyn_Syntax.Exp_app (_62_1298, args), FStar_Absyn_Syntax.Pat_cons (_62_1303, _62_1305, pats)) -> begin
(

let tup = (FStar_Absyn_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (

let sc = (let _157_439 = (let _157_438 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _157_437 = (let _157_436 = (let _157_435 = (let _157_434 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _157_434))
in (_157_435)::[])
in (FStar_List.append args _157_436))
in ((_157_438), (_157_437))))
in (FStar_Absyn_Syntax.mk_Exp_app _157_439 None top.FStar_Parser_AST.range))
in (

let p = (let _157_440 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((FStar_List.append pats ((((p), (false)))::[])))))) None _157_440))
in Some (((sc), (p))))))
end
| _62_1314 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((FStar_Util.Inr (b)), (aq))), (sc_pat_opt))))
end)
in (match (_62_1318) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _62_1322; FStar_Parser_AST.level = _62_1320}, arg, _62_1328) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env arg)
in (let _157_450 = (let _157_449 = (let _157_448 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _157_447 = (let _157_446 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _157_445 = (let _157_444 = (let _157_443 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _157_443))
in (_157_444)::[])
in (_157_446)::_157_445))
in ((_157_448), (_157_447))))
in (FStar_Absyn_Syntax.mk_Exp_app _157_449))
in (FStar_All.pipe_left pos _157_450)))
end
| FStar_Parser_AST.App (_62_1333) -> begin
(

let rec aux = (fun args e -> (match ((let _157_455 = (unparen e)
in _157_455.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _157_456 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _157_456))
in (aux ((arg)::args) e))
end
| _62_1345 -> begin
(

let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app ((head), (args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _157_462 = (let _157_461 = (let _157_460 = (let _157_459 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_157_459), (FStar_Absyn_Syntax.Sequence)))
in FStar_Absyn_Syntax.Meta_desugared (_157_460))
in (FStar_Absyn_Syntax.mk_Exp_meta _157_461))
in (FStar_All.pipe_left setpos _157_462))
end
| FStar_Parser_AST.LetOpen (_62_1352) -> begin
(FStar_All.failwith "let open in universes")
end
| FStar_Parser_AST.Let (is_rec, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (is_rec = FStar_Parser_AST.Rec)
in (

let ds_let_rec = (fun _62_1365 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _62_1369 -> (match (_62_1369) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _157_466 = (destruct_app_pattern env top_level p)
in ((_157_466), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _157_467 = (destruct_app_pattern env top_level p)
in ((_157_467), (def)))
end
| _62_1375 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _62_1380); FStar_Parser_AST.prange = _62_1377}, t) -> begin
if top_level then begin
(let _157_470 = (let _157_469 = (let _157_468 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_157_468))
in ((_157_469), ([]), (Some (t))))
in ((_157_470), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _62_1389) -> begin
if top_level then begin
(let _157_473 = (let _157_472 = (let _157_471 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_157_471))
in ((_157_472), ([]), (None)))
in ((_157_473), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _62_1393 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _62_1419 = (FStar_List.fold_left (fun _62_1397 _62_1406 -> (match (((_62_1397), (_62_1406))) with
| ((env, fnames), ((f, _62_1400, _62_1402), _62_1405)) -> begin
(

let _62_1416 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _62_1411 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_1411) with
| (env, xx) -> begin
((env), (FStar_Util.Inl (xx)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _157_476 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in ((_157_476), (FStar_Util.Inr (l))))
end)
in (match (_62_1416) with
| (env, lbname) -> begin
((env), ((lbname)::fnames))
end))
end)) ((env), ([])) funs)
in (match (_62_1419) with
| (env', fnames) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _62_1430 -> (match (_62_1430) with
| ((_62_1425, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _157_483 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _157_483 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _62_1437 -> begin
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

let _62_1450 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_62_1450) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_62_1452) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(

let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]))), (body)))))
end
| VBinder (x, t, _62_1462) -> begin
(

let body = (desugar_exp env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _157_495 = (let _157_494 = (FStar_Absyn_Util.bvd_to_exp x t)
in ((_157_494), ((((pat), (None), (body)))::[])))
in (FStar_Absyn_Syntax.mk_Exp_match _157_495 None body.FStar_Absyn_Syntax.pos))
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
(let _157_508 = (let _157_507 = (let _157_506 = (desugar_exp env t1)
in (let _157_505 = (let _157_504 = (let _157_500 = (desugar_exp env t2)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range)), (None), (_157_500)))
in (let _157_503 = (let _157_502 = (let _157_501 = (desugar_exp env t3)
in (((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range)), (None), (_157_501)))
in (_157_502)::[])
in (_157_504)::_157_503))
in ((_157_506), (_157_505))))
in (FStar_Absyn_Syntax.mk_Exp_match _157_507))
in (FStar_All.pipe_left pos _157_508))
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

let desugar_branch = (fun _62_1501 -> (match (_62_1501) with
| (pat, wopt, b) -> begin
(

let _62_1504 = (desugar_match_pat env pat)
in (match (_62_1504) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _157_511 = (desugar_exp env e)
in Some (_157_511))
end)
in (

let b = (desugar_exp env b)
in ((pat), (wopt), (b))))
end))
end))
in (let _157_517 = (let _157_516 = (let _157_515 = (desugar_exp env e)
in (let _157_514 = (FStar_List.map desugar_branch branches)
in ((_157_515), (_157_514))))
in (FStar_Absyn_Syntax.mk_Exp_match _157_516))
in (FStar_All.pipe_left pos _157_517)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _157_523 = (let _157_522 = (let _157_521 = (desugar_exp env e)
in (let _157_520 = (desugar_typ env t)
in ((_157_521), (_157_520), (None))))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _157_522))
in (FStar_All.pipe_left pos _157_523))
end
| FStar_Parser_AST.Record (_62_1515, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _62_1526 = (FStar_List.hd fields)
in (match (_62_1526) with
| (f, _62_1525) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _62_1532 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_62_1532) with
| (record, _62_1531) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _62_1540 -> (match (_62_1540) with
| (g, _62_1539) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_62_1544, e) -> begin
(let _157_531 = (qfn fn)
in ((_157_531), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _157_534 = (let _157_533 = (let _157_532 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_157_532), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_157_533))
in (Prims.raise _157_534))
end
| Some (x) -> begin
(let _157_535 = (qfn fn)
in ((_157_535), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _157_540 = (let _157_539 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _62_1556 -> (match (_62_1556) with
| (f, _62_1555) -> begin
(let _157_538 = (let _157_537 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _157_537))
in ((_157_538), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_DesugarEnv.constrname), (_157_539)))
in FStar_Parser_AST.Construct (_157_540))
end
| Some (e) -> begin
(

let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (

let xterm = (let _157_542 = (let _157_541 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_157_541))
in (FStar_Parser_AST.mk_term _157_542 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _157_545 = (let _157_544 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _62_1564 -> (match (_62_1564) with
| (f, _62_1563) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_157_544)))
in FStar_Parser_AST.Record (_157_545))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _62_1587); FStar_Absyn_Syntax.tk = _62_1584; FStar_Absyn_Syntax.pos = _62_1582; FStar_Absyn_Syntax.fvs = _62_1580; FStar_Absyn_Syntax.uvs = _62_1578}, args); FStar_Absyn_Syntax.tk = _62_1576; FStar_Absyn_Syntax.pos = _62_1574; FStar_Absyn_Syntax.fvs = _62_1572; FStar_Absyn_Syntax.uvs = _62_1570}, FStar_Absyn_Syntax.Data_app)) -> begin
(

let e = (let _157_555 = (let _157_554 = (let _157_553 = (let _157_552 = (let _157_551 = (let _157_550 = (let _157_549 = (let _157_548 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_157_548)))
in FStar_Absyn_Syntax.Record_ctor (_157_549))
in Some (_157_550))
in ((fv), (_157_551)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _157_552 None e.FStar_Absyn_Syntax.pos))
in ((_157_553), (args)))
in (FStar_Absyn_Syntax.mk_Exp_app _157_554))
in (FStar_All.pipe_left pos _157_555))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((e), (FStar_Absyn_Syntax.Data_app))))))
end
| _62_1601 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _62_1608 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_62_1608) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_exp env e)
in (

let fn = (

let _62_1613 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_62_1613) with
| (ns, _62_1612) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _157_562 = (let _157_561 = (let _157_560 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (let _157_559 = (let _157_558 = (FStar_Absyn_Syntax.varg e)
in (_157_558)::[])
in ((_157_560), (_157_559))))
in (FStar_Absyn_Syntax.mk_Exp_app _157_561))
in (FStar_All.pipe_left pos _157_562)))))
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
| _62_1627 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (

let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _62_1634 = t
in {FStar_Absyn_Syntax.n = _62_1634.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_1634.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _62_1634.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_1634.FStar_Absyn_Syntax.uvs}))
in (

let top = (unparen top)
in (

let head_and_args = (fun t -> (

let rec aux = (fun args t -> (match ((let _157_585 = (unparen t)
in _157_585.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _62_1652 -> begin
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
(let _157_586 = (desugar_exp env t)
in (FStar_All.pipe_right _157_586 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _157_587 = (desugar_exp env t)
in (FStar_All.pipe_right _157_587 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", (t1)::(_62_1666)::[]) -> begin
if (is_type env t1) then begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _157_590 = (flatten t1)
in (FStar_List.append _157_590 ((t2)::[])))
end
| _62_1680 -> begin
(t)::[]
end))
in (

let targs = (let _157_593 = (flatten top)
in (FStar_All.pipe_right _157_593 (FStar_List.map (fun t -> (let _157_592 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _157_592))))))
in (

let tup = (let _157_594 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _157_594))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))))
end else begin
(let _157_600 = (let _157_599 = (let _157_598 = (let _157_597 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _157_597))
in ((_157_598), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_157_599))
in (Prims.raise _157_600))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _157_601 = (desugar_exp env top)
in (FStar_All.pipe_right _157_601 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(

let args = (FStar_List.map (fun t -> (let _157_603 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _157_603))) args)
in (let _157_604 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _157_604 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _157_605 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _157_605))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = (Prims.parse_int "0")) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _157_606 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _157_606))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _157_607 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _157_607)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let t = (let _157_608 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _157_608))
in (

let args = (FStar_List.map (fun _62_1716 -> (match (_62_1716) with
| (t, imp) -> begin
(let _157_610 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _157_610))
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

let _62_1734 = (desugar_binding_pat env hd)
in (match (_62_1734) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _157_622 = (let _157_621 = (let _157_620 = (let _157_619 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _157_619))
in ((_157_620), (hd.FStar_Parser_AST.prange)))
in FStar_Absyn_Syntax.Error (_157_621))
in (Prims.raise _157_622))
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
| FStar_Parser_AST.App (_62_1740) -> begin
(

let rec aux = (fun args e -> (match ((let _157_627 = (unparen e)
in _157_627.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(

let arg = (let _157_628 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _157_628))
in (aux ((arg)::args) e))
end
| _62_1752 -> begin
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

let _62_1764 = (uncurry binders t)
in (match (_62_1764) with
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

let _62_1778 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_62_1778) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _62_1785) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _62_1799 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _62_1791), env) -> begin
((x), (env))
end
| _62_1796 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_62_1799) with
| (b, env) -> begin
(

let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _157_639 = (desugar_exp env f)
in (FStar_All.pipe_right _157_639 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine ((b), (f)))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _157_647 = (let _157_646 = (let _157_645 = (desugar_typ env t)
in (let _157_644 = (desugar_kind env k)
in ((_157_645), (_157_644))))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _157_646))
in (FStar_All.pipe_left wpos _157_647))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _62_1833 = (FStar_List.fold_left (fun _62_1818 b -> (match (_62_1818) with
| (env, tparams, typs) -> begin
(

let _62_1822 = (desugar_exp_binder env b)
in (match (_62_1822) with
| (xopt, t) -> begin
(

let _62_1828 = (match (xopt) with
| None -> begin
(let _157_650 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in ((env), (_157_650)))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_62_1828) with
| (env, x) -> begin
(let _157_654 = (let _157_653 = (let _157_652 = (let _157_651 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _157_651))
in (_157_652)::[])
in (FStar_List.append typs _157_653))
in ((env), ((FStar_List.append tparams ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (None)))::[]))), (_157_654)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_62_1833) with
| (env, _62_1831, targs) -> begin
(

let tup = (let _157_655 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _157_655))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))
end))
end
| FStar_Parser_AST.Record (_62_1836) -> begin
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
| _62_1855 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _62_1857 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r))))))
in (

let pre_process_comp_typ = (fun t -> (

let _62_1868 = (head_and_args t)
in (match (_62_1868) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let _62_1894 = (FStar_All.pipe_right args (FStar_List.partition (fun _62_1876 -> (match (_62_1876) with
| (arg, _62_1875) -> begin
(match ((let _157_667 = (unparen arg)
in _157_667.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _62_1880; FStar_Parser_AST.level = _62_1878}, _62_1885, _62_1887) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _62_1891 -> begin
false
end)
end))))
in (match (_62_1894) with
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
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _157_668 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _157_668 FStar_Absyn_Const.prims_lid))) -> begin
(

let args = (FStar_List.map (fun _62_1909 -> (match (_62_1909) with
| (t, imp) -> begin
(let _157_670 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _157_670))
end)) args)
in (let _157_671 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _157_671 args)))
end
| _62_1912 -> begin
(desugar_typ env t)
end)
end)))
in (

let t = (pre_process_comp_typ t)
in (

let _62_1916 = (FStar_Absyn_Util.head_and_args t)
in (match (_62_1916) with
| (head, args) -> begin
(match ((let _157_673 = (let _157_672 = (FStar_Absyn_Util.compress_typ head)
in _157_672.FStar_Absyn_Syntax.n)
in ((_157_673), (args)))) with
| (FStar_Absyn_Syntax.Typ_const (eff), ((FStar_Util.Inl (result_typ), _62_1923))::rest) -> begin
(

let _62_1963 = (FStar_All.pipe_right rest (FStar_List.partition (fun _62_11 -> (match (_62_11) with
| (FStar_Util.Inr (_62_1929), _62_1932) -> begin
false
end
| (FStar_Util.Inl (t), _62_1937) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _62_1946; FStar_Absyn_Syntax.pos = _62_1944; FStar_Absyn_Syntax.fvs = _62_1942; FStar_Absyn_Syntax.uvs = _62_1940}, ((FStar_Util.Inr (_62_1951), _62_1954))::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _62_1960 -> begin
false
end)
end))))
in (match (_62_1963) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _62_12 -> (match (_62_12) with
| (FStar_Util.Inl (t), _62_1968) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_62_1971, ((FStar_Util.Inr (arg), _62_1975))::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _62_1981 -> begin
(FStar_All.failwith "impos")
end)
end
| _62_1983 -> begin
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
(let _157_680 = (let _157_679 = (let _157_678 = (let _157_677 = (let _157_676 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((pat), (FStar_Absyn_Syntax.Meta_smt_pat)))))
in FStar_Util.Inr (_157_676))
in ((_157_677), (aq)))
in (_157_678)::[])
in (ens)::_157_679)
in (req)::_157_680)
end
| _62_1994 -> begin
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
(let _157_682 = (let _157_681 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _157_681))
in (fail _157_682))
end
end)
end))
end
| _62_1997 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _157_684 = (let _157_683 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _157_683))
in (fail _157_684))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (

let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (

let setpos = (fun kk -> (

let _62_2004 = kk
in {FStar_Absyn_Syntax.n = _62_2004.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_2004.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _62_2004.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_2004.FStar_Absyn_Syntax.uvs}))
in (

let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _62_2013; FStar_Ident.ident = _62_2011; FStar_Ident.nsstr = _62_2009; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _62_2022; FStar_Ident.ident = _62_2020; FStar_Ident.nsstr = _62_2018; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _157_696 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _157_696))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), ([]))), (FStar_Absyn_Syntax.mk_Kind_unknown))))
end
| _62_2030 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(

let _62_2038 = (uncurry bs k)
in (match (_62_2038) with
| (bs, k) -> begin
(

let rec aux = (fun env bs _62_13 -> (match (_62_13) with
| [] -> begin
(let _157_707 = (let _157_706 = (let _157_705 = (desugar_kind env k)
in (((FStar_List.rev bs)), (_157_705)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _157_706))
in (FStar_All.pipe_left pos _157_707))
end
| (hd)::tl -> begin
(

let _62_2049 = (let _157_709 = (let _157_708 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _157_708 hd))
in (FStar_All.pipe_right _157_709 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_62_2049) with
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

let args = (FStar_List.map (fun _62_2059 -> (match (_62_2059) with
| (t, b) -> begin
(

let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _157_711 = (desugar_typ_or_exp env t)
in ((_157_711), (qual))))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (FStar_Absyn_Syntax.mk_Kind_unknown)))))
end)
end
| _62_2063 -> begin
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
| _62_2074 -> begin
None
end))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _62_2079 = t
in {FStar_Absyn_Syntax.n = _62_2079.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_2079.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _62_2079.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_2079.FStar_Absyn_Syntax.uvs}))
in (

let desugar_quant = (fun q qt b pats body -> (

let tk = (desugar_binder env (

let _62_2087 = b
in {FStar_Parser_AST.b = _62_2087.FStar_Parser_AST.b; FStar_Parser_AST.brange = _62_2087.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _62_2087.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _157_747 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _157_747)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _62_2102 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_62_2102) with
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
| _62_2107 -> begin
(let _157_748 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
in (FStar_All.pipe_left setpos _157_748))
end)
in (

let body = (let _157_754 = (let _157_753 = (let _157_752 = (let _157_751 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_157_751)::[])
in ((_157_752), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _157_753))
in (FStar_All.pipe_left pos _157_754))
in (let _157_758 = (let _157_757 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange) FStar_Absyn_Syntax.kun)
in (let _157_756 = (let _157_755 = (FStar_Absyn_Syntax.targ body)
in (_157_755)::[])
in (FStar_Absyn_Util.mk_typ_app _157_757 _157_756)))
in (FStar_All.pipe_left setpos _157_758))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _62_2117 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_2117) with
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
| _62_2122 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
end)
in (

let body = (let _157_764 = (let _157_763 = (let _157_762 = (let _157_761 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_157_761)::[])
in ((_157_762), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _157_763))
in (FStar_All.pipe_left pos _157_764))
in (let _157_768 = (let _157_767 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) FStar_Absyn_Syntax.kun)
in (let _157_766 = (let _157_765 = (FStar_Absyn_Syntax.targ body)
in (_157_765)::[])
in (FStar_Absyn_Util.mk_typ_app _157_767 _157_766)))
in (FStar_All.pipe_left setpos _157_768))))))
end))
end
| _62_2126 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _157_783 = (q ((rest), (pats), (body)))
in (let _157_782 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _157_783 _157_782 FStar_Parser_AST.Formula)))
in (let _157_784 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _157_784 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _62_2140 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _157_785 = (unparen f)
in _157_785.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (l), (FStar_Absyn_Syntax.dummyRange), (p))))))
end
| FStar_Parser_AST.Op ("==", (hd)::_args) -> begin
(

let args = (hd)::_args
in (

let args = (FStar_List.map (fun t -> (let _157_787 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _157_787))) args)
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
| (Some (conn), (_62_2166)::(_62_2164)::[]) -> begin
(let _157_791 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range) FStar_Absyn_Syntax.kun)
in (let _157_790 = (FStar_List.map (fun x -> (let _157_789 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _157_789))) args)
in (FStar_Absyn_Util.mk_typ_app _157_791 _157_790)))
end
| _62_2171 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _157_792 = (desugar_exp env f)
in (FStar_All.pipe_right _157_792 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _157_796 = (FStar_Absyn_Util.ftv (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range) FStar_Absyn_Syntax.kun)
in (let _157_795 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _157_794 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _157_794))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _157_796 _157_795)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _157_798 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _157_798)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _157_800 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _157_800)))
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
| _62_2233 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _157_801 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _157_801))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (

let _62_2236 = env
in {FStar_Parser_DesugarEnv.curmodule = _62_2236.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _62_2236.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _62_2236.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _62_2236.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _62_2236.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _62_2236.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _62_2236.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _62_2236.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _62_2236.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _62_2236.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _62_2236.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _157_806 = (desugar_type_binder env b)
in FStar_Util.Inl (_157_806))
end else begin
(let _157_807 = (desugar_exp_binder env b)
in FStar_Util.Inr (_157_807))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _62_2269 = (FStar_List.fold_left (fun _62_2244 b -> (match (_62_2244) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _62_2246 = b
in {FStar_Parser_AST.b = _62_2246.FStar_Parser_AST.b; FStar_Parser_AST.brange = _62_2246.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _62_2246.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _62_2256 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_62_2256) with
| (env, a) -> begin
((env), ((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _62_2264 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_2264) with
| (env, x) -> begin
((env), ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| _62_2266 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_62_2269) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _157_814 = (desugar_typ env t)
in ((Some (x)), (_157_814)))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _157_815 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in ((None), (_157_815)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _157_816 = (desugar_typ env t)
in ((None), (_157_816)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Absyn_Syntax.tun))
end
| _62_2283 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a type)"), (b.FStar_Parser_AST.brange)))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (

let fail = (fun _62_2287 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a kind)"), (b.FStar_Parser_AST.brange)))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _157_821 = (desugar_kind env t)
in ((Some (x)), (_157_821)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _157_822 = (desugar_kind env t)
in ((None), (_157_822)))
end
| FStar_Parser_AST.TVariable (x) -> begin
((Some (x)), ((

let _62_2298 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _62_2298.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _62_2298.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _62_2298.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _62_2298.FStar_Absyn_Syntax.uvs})))
end
| _62_2301 -> begin
(fail ())
end)))


let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (

let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_62_2312, k) -> begin
(aux bs k)
end
| _62_2317 -> begin
bs
end))
in (let _157_831 = (aux tps k)
in (FStar_All.pipe_right _157_831 FStar_Absyn_Util.name_binders))))


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

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _62_2331 -> (match (_62_2331) with
| (x, _62_2330) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (let _157_852 = (let _157_851 = (let _157_850 = (let _157_849 = (let _157_848 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _157_847 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_157_848), (_157_847))))
in (FStar_Absyn_Syntax.mk_Typ_app' _157_849 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _157_850))
in (_157_851)::[])
in (FStar_List.append imp_binders _157_852))
in (

let disc_type = (let _157_855 = (let _157_854 = (let _157_853 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _157_853 p))
in ((binders), (_157_854)))
in (FStar_Absyn_Syntax.mk_Typ_fun _157_855 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _157_858 = (let _157_857 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in ((disc_name), (disc_type), (_157_857), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Absyn_Syntax.Sig_val_decl (_157_858)))))))))))))


let mk_indexed_projectors = (fun fvq refine_domain env _62_2343 lid formals t -> (match (_62_2343) with
| (tc, tps, k) -> begin
(

let binders = (gather_tc_binders tps k)
in (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (

let projectee = (let _157_869 = (FStar_Absyn_Syntax.mk_ident (("projectee"), (p)))
in (let _157_868 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _157_869; FStar_Absyn_Syntax.realname = _157_868}))
in (

let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (

let arg_binder = (

let arg_typ = (let _157_872 = (let _157_871 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _157_870 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_157_871), (_157_870))))
in (FStar_Absyn_Syntax.mk_Typ_app' _157_872 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(

let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (

let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _157_882 = (let _157_881 = (let _157_880 = (let _157_879 = (let _157_878 = (let _157_877 = (let _157_876 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _157_875 = (let _157_874 = (let _157_873 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _157_873))
in (_157_874)::[])
in ((_157_876), (_157_875))))
in (FStar_Absyn_Syntax.mk_Exp_app _157_877 None p))
in (FStar_Absyn_Util.b2t _157_878))
in ((x), (_157_879)))
in (FStar_Absyn_Syntax.mk_Typ_refine _157_880 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _157_881))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _157_882))))
end)
in (

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _62_2360 -> (match (_62_2360) with
| (x, _62_2359) -> begin
((x), (Some (imp_tag)))
end))))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (let _157_890 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(

let _62_2371 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_62_2371) with
| (field_name, _62_2370) -> begin
(

let proj = (let _157_887 = (let _157_886 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in ((_157_886), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Typ_app _157_887 None p))
in (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _62_2378 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_62_2378) with
| (field_name, _62_2377) -> begin
(

let proj = (let _157_889 = (let _157_888 = (FStar_Absyn_Util.fvar None field_name p)
in ((_157_888), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Exp_app _157_889 None p))
in (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end))))
in (FStar_All.pipe_right _157_890 FStar_List.flatten))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _157_892 = (FStar_All.pipe_right tps (FStar_List.map (fun _62_2385 -> (match (_62_2385) with
| (b, _62_2384) -> begin
((b), (Some (imp_tag)))
end))))
in (FStar_List.append _157_892 formals))
in (let _157_922 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(

let _62_2394 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_62_2394) with
| (field_name, _62_2393) -> begin
(

let kk = (let _157_896 = (let _157_895 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in ((binders), (_157_895)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _157_896 p))
in (FStar_Absyn_Syntax.Sig_tycon (((field_name), ([]), (kk), ([]), ([]), ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inl (a.FStar_Absyn_Syntax.v)))))::[]), ((FStar_Ident.range_of_lid field_name)))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(

let _62_2401 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_62_2401) with
| (field_name, _62_2400) -> begin
(

let t = (let _157_899 = (let _157_898 = (let _157_897 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _157_897 p))
in ((binders), (_157_898)))
in (FStar_Absyn_Syntax.mk_Typ_fun _157_899 None p))
in (

let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (

let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inr (x.FStar_Absyn_Syntax.v)))))::[]))
in (

let impl = if (((let _157_902 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _157_902)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _157_904 = (let _157_903 = (FStar_Parser_DesugarEnv.current_module env)
in _157_903.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _157_904))) then begin
[]
end else begin
(

let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (

let as_imp = (fun _62_14 -> (match (_62_14) with
| Some (FStar_Absyn_Syntax.Implicit (_62_2409)) -> begin
true
end
| _62_2413 -> begin
false
end))
in (

let arg_pats = (let _157_919 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_62_2418), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _157_912 = (let _157_911 = (let _157_910 = (let _157_909 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_157_909))
in (pos _157_910))
in ((_157_911), ((as_imp imp))))
in (_157_912)::[])
end
end
| (FStar_Util.Inr (_62_2423), imp) -> begin
if ((i + ntps) = j) then begin
(let _157_914 = (let _157_913 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in ((_157_913), ((as_imp imp))))
in (_157_914)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _157_918 = (let _157_917 = (let _157_916 = (let _157_915 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_157_915))
in (pos _157_916))
in ((_157_917), ((as_imp imp))))
in (_157_918)::[])
end
end
end))))
in (FStar_All.pipe_right _157_919 FStar_List.flatten))
in (

let pat = (let _157_921 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv lid)), (Some (fvq)), (arg_pats)))) pos)
in (let _157_920 = (FStar_Absyn_Util.bvar_to_exp projection)
in ((_157_921), (None), (_157_920))))
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
in (FStar_All.pipe_right _157_922 FStar_List.flatten))))))))))))))
end))


let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _62_17 -> (match (_62_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _62_2440, _62_2442) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_15 -> (match (_62_15) with
| FStar_Absyn_Syntax.RecordConstructor (_62_2447) -> begin
true
end
| _62_2450 -> begin
false
end)))) then begin
false
end else begin
(

let _62_2456 = tycon
in (match (_62_2456) with
| (l, _62_2453, _62_2455) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > (Prims.parse_int "1"))
end
| _62_2460 -> begin
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
| _62_2471 -> begin
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
| _62_2477 -> begin
[]
end))
end
| _62_2479 -> begin
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
(let _157_942 = (let _157_941 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_157_941))
in (FStar_Parser_AST.mk_term _157_942 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _62_2544 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _157_955 = (let _157_954 = (let _157_953 = (binder_to_term b)
in ((out), (_157_953), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_157_954))
in (FStar_Parser_AST.mk_term _157_955 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _62_19 -> (match (_62_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _62_2559 -> (match (_62_2559) with
| (x, t, _62_2558) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Absyn_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _157_961 = (let _157_960 = (let _157_959 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_157_959))
in (FStar_Parser_AST.mk_term _157_960 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _157_961 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _157_963 = (FStar_All.pipe_right fields (FStar_List.map (fun _62_2568 -> (match (_62_2568) with
| (x, _62_2565, _62_2567) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_157_963)))))))
end
| _62_2570 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _62_20 -> (match (_62_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _62_2584 = (typars_of_binders _env binders)
in (match (_62_2584) with
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

let tconstr = (let _157_974 = (let _157_973 = (let _157_972 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_157_972))
in (FStar_Parser_AST.mk_term _157_973 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _157_974 binders))
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
| _62_2595 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparam = (fun env _62_21 -> (match (_62_21) with
| (FStar_Util.Inr (x), _62_2602) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _62_2607) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (

let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (_62_2611))::[] -> begin
(

let tc = (FStar_List.hd tcs)
in (

let _62_2622 = (desugar_abstract_tc quals env [] tc)
in (match (_62_2622) with
| (_62_2616, _62_2618, se, _62_2621) -> begin
(

let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(

let _62_2623 = (let _157_984 = (FStar_Range.string_of_range rng)
in (let _157_983 = (let _157_982 = (let _157_981 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _157_981 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _157_982 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _157_984 _157_983)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))
end)))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _62_2636 = (typars_of_binders env binders)
in (match (_62_2636) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _62_22 -> (match (_62_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _62_2641 -> begin
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
| _62_2649 -> begin
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
in (let _157_990 = (let _157_989 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _157_988 = (FStar_All.pipe_right quals (FStar_List.filter (fun _62_24 -> (match (_62_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _62_2655 -> begin
true
end))))
in ((_157_989), (typars), (c), (_157_988), (rng))))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_157_990)))
end else begin
(

let t = (desugar_typ env' t)
in (let _157_992 = (let _157_991 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_157_991), (typars), (k), (t), (quals), (rng)))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_157_992)))
end
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_62_2660))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _62_2666 = (tycon_record_as_variant trec)
in (match (_62_2666) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_62_2670)::_62_2668 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _62_2681 = et
in (match (_62_2681) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_62_2683) -> begin
(

let trec = tc
in (

let _62_2688 = (tycon_record_as_variant trec)
in (match (_62_2688) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _62_2700 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_62_2700) with
| (env, _62_2697, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _62_2712 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_62_2712) with
| (env, _62_2709, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _62_2714 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _62_2717 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_62_2717) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _62_26 -> (match (_62_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _62_2724, _62_2726, _62_2728, _62_2730), t, quals) -> begin
(

let env_tps = (push_tparams env tpars)
in (

let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev (((id), (tpars), (k), (t), ([]), (rng))))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _62_2744, tags, _62_2747), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let env_tps = (push_tparams env tpars)
in (

let _62_2780 = (let _157_1008 = (FStar_All.pipe_right constrs (FStar_List.map (fun _62_2762 -> (match (_62_2762) with
| (id, topt, _62_2760, of_notation) -> begin
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

let t = (let _157_1003 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _157_1002 = (close env_tps t)
in (desugar_typ _157_1003 _157_1002)))
in (

let name = (FStar_Parser_DesugarEnv.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _62_25 -> (match (_62_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _62_2776 -> begin
[]
end))))
in (let _157_1007 = (let _157_1006 = (let _157_1005 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in ((name), (_157_1005), (tycon), (quals), (mutuals), (rng)))
in FStar_Absyn_Syntax.Sig_datacon (_157_1006))
in ((name), (_157_1007)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _157_1008))
in (match (_62_2780) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon (((tname), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))::constrs
end))))
end
| _62_2782 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let bundle = (let _157_1010 = (let _157_1009 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_157_1009), (rng)))
in FStar_Absyn_Syntax.Sig_bundle (_157_1010))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _62_27 -> (match (_62_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _62_2792, constrs, quals, _62_2796) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _62_2800 -> begin
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

let _62_2831 = (FStar_List.fold_left (fun _62_2809 b -> (match (_62_2809) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(

let _62_2818 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_62_2818) with
| (env, a) -> begin
(let _157_1019 = (let _157_1018 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_157_1018)::binders)
in ((env), (_157_1019)))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(

let _62_2826 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_62_2826) with
| (env, x) -> begin
(let _157_1021 = (let _157_1020 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_157_1020)::binders)
in ((env), (_157_1021)))
end))
end
| _62_2828 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_62_2831) with
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
| (FStar_Parser_AST.Reflectable) | (FStar_Parser_AST.Reifiable) | (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Irreducible) | (FStar_Parser_AST.Noeq) | (FStar_Parser_AST.Unopteq) | (FStar_Parser_AST.Visible) | (FStar_Parser_AST.Unfold_for_unification_and_vcgen) | (FStar_Parser_AST.NoExtract) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("The noextract qualifier is supported only with the --universes option"), (r)))))
end
| FStar_Parser_AST.Inline_for_extraction -> begin
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
| FStar_Parser_AST.Fsdoc (_62_2863) -> begin
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
| FStar_Parser_AST.Include (_62_2874) -> begin
(FStar_All.failwith "include not supported by legacy desugaring")
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _157_1039 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in ((_157_1039), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(

let tcs = (FStar_List.map (fun _62_2887 -> (match (_62_2887) with
| (x, _62_2886) -> begin
x
end)) tcs)
in (let _157_1041 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _157_1041 tcs)))
end
| FStar_Parser_AST.TopLevelLet (quals, isrec, lets) -> begin
(match ((let _157_1043 = (let _157_1042 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _157_1042))
in _157_1043.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _62_2896) -> begin
(

let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _62_2903 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let quals = (match (quals) with
| (_62_2908)::_62_2906 -> begin
(trans_quals quals)
end
| _62_2911 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _62_30 -> (match (_62_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_62_2920); FStar_Absyn_Syntax.lbtyp = _62_2918; FStar_Absyn_Syntax.lbeff = _62_2916; FStar_Absyn_Syntax.lbdef = _62_2914} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _62_2928; FStar_Absyn_Syntax.lbeff = _62_2926; FStar_Absyn_Syntax.lbdef = _62_2924} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (

let s = FStar_Absyn_Syntax.Sig_let (((lbs), (d.FStar_Parser_AST.drange), (lids), (quals)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in ((env), ((s)::[]))))))
end
| _62_2936 -> begin
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
in (let _157_1049 = (let _157_1048 = (let _157_1047 = (let _157_1046 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_157_1046), (f), ((FStar_Absyn_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_assume (_157_1047))
in (_157_1048)::[])
in ((env), (_157_1049))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _157_1050 = (close_fun env t)
in (desugar_typ env _157_1050))
in (

let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _157_1051 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_157_1051)
end else begin
(trans_quals quals)
end
in (

let se = (let _157_1053 = (let _157_1052 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_157_1052), (t), (quals), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_val_decl (_157_1053))
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

let t = (let _157_1058 = (let _157_1057 = (let _157_1054 = (FStar_Absyn_Syntax.null_v_binder t)
in (_157_1054)::[])
in (let _157_1056 = (let _157_1055 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _157_1055))
in ((_157_1057), (_157_1056))))
in (FStar_Absyn_Syntax.mk_Typ_fun _157_1058 None d.FStar_Parser_AST.drange))
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

let _62_2989 = (desugar_binders env binders)
in (match (_62_2989) with
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
| FStar_Parser_AST.NewEffectForFree (_62_2995) -> begin
(FStar_All.failwith "effects for free only supported in conjunction with --universes")
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let env0 = env
in (

let _62_3008 = (desugar_binders env eff_binders)
in (match (_62_3008) with
| (env, binders) -> begin
(

let defn = (desugar_typ env defn)
in (

let _62_3012 = (FStar_Absyn_Util.head_and_args defn)
in (match (_62_3012) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _157_1063 = (let _157_1062 = (let _157_1061 = (let _157_1060 = (let _157_1059 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat _157_1059 " not found"))
in (Prims.strcat "Effect " _157_1060))
in ((_157_1061), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_157_1062))
in (Prims.raise _157_1063))
end
| Some (ed) -> begin
(

let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (

let sub = (FStar_Absyn_Util.subst_typ subst)
in (

let ed = (let _157_1081 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _157_1080 = (trans_quals quals)
in (let _157_1079 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _157_1078 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _157_1077 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _157_1076 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _157_1075 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _157_1074 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _157_1073 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _157_1072 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _157_1071 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _157_1070 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _157_1069 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _157_1068 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _157_1067 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _157_1066 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _157_1065 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _157_1081; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _157_1080; FStar_Absyn_Syntax.signature = _157_1079; FStar_Absyn_Syntax.ret = _157_1078; FStar_Absyn_Syntax.bind_wp = _157_1077; FStar_Absyn_Syntax.bind_wlp = _157_1076; FStar_Absyn_Syntax.if_then_else = _157_1075; FStar_Absyn_Syntax.ite_wp = _157_1074; FStar_Absyn_Syntax.ite_wlp = _157_1073; FStar_Absyn_Syntax.wp_binop = _157_1072; FStar_Absyn_Syntax.wp_as_type = _157_1071; FStar_Absyn_Syntax.close_wp = _157_1070; FStar_Absyn_Syntax.close_wp_t = _157_1069; FStar_Absyn_Syntax.assert_p = _157_1068; FStar_Absyn_Syntax.assume_p = _157_1067; FStar_Absyn_Syntax.null_wp = _157_1066; FStar_Absyn_Syntax.trivial = _157_1065})))))))))))))))))
in (

let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)
end
| _62_3024 -> begin
(let _157_1085 = (let _157_1084 = (let _157_1083 = (let _157_1082 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _157_1082 " is not an effect"))
in ((_157_1083), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_157_1084))
in (Prims.raise _157_1085))
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

let _62_3039 = (desugar_binders env eff_binders)
in (match (_62_3039) with
| (env, binders) -> begin
(

let eff_k = (desugar_kind env eff_kind)
in (

let _62_3050 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _62_3043 decl -> (match (_62_3043) with
| (env, out) -> begin
(

let _62_3047 = (desugar_decl env decl)
in (match (_62_3047) with
| (env, ses) -> begin
(let _157_1089 = (let _157_1088 = (FStar_List.hd ses)
in (_157_1088)::out)
in ((env), (_157_1089)))
end))
end)) ((env), ([]))))
in (match (_62_3050) with
| (env, decls) -> begin
(

let decls = (FStar_List.rev decls)
in (

let lookup = (fun s -> (match ((let _157_1093 = (let _157_1092 = (FStar_Absyn_Syntax.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.qualify env _157_1092))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _157_1093))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Monad " (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat " expects definition of " s)))), (d.FStar_Parser_AST.drange)))))
end
| Some (t) -> begin
t
end))
in (

let ed = (let _157_1109 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _157_1108 = (trans_quals quals)
in (let _157_1107 = (lookup "return")
in (let _157_1106 = (lookup "bind_wp")
in (let _157_1105 = (lookup "bind_wlp")
in (let _157_1104 = (lookup "if_then_else")
in (let _157_1103 = (lookup "ite_wp")
in (let _157_1102 = (lookup "ite_wlp")
in (let _157_1101 = (lookup "wp_binop")
in (let _157_1100 = (lookup "wp_as_type")
in (let _157_1099 = (lookup "close_wp")
in (let _157_1098 = (lookup "close_wp_t")
in (let _157_1097 = (lookup "assert_p")
in (let _157_1096 = (lookup "assume_p")
in (let _157_1095 = (lookup "null_wp")
in (let _157_1094 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _157_1109; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _157_1108; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _157_1107; FStar_Absyn_Syntax.bind_wp = _157_1106; FStar_Absyn_Syntax.bind_wlp = _157_1105; FStar_Absyn_Syntax.if_then_else = _157_1104; FStar_Absyn_Syntax.ite_wp = _157_1103; FStar_Absyn_Syntax.ite_wlp = _157_1102; FStar_Absyn_Syntax.wp_binop = _157_1101; FStar_Absyn_Syntax.wp_as_type = _157_1100; FStar_Absyn_Syntax.close_wp = _157_1099; FStar_Absyn_Syntax.close_wp_t = _157_1098; FStar_Absyn_Syntax.assert_p = _157_1097; FStar_Absyn_Syntax.assume_p = _157_1096; FStar_Absyn_Syntax.null_wp = _157_1095; FStar_Absyn_Syntax.trivial = _157_1094}))))))))))))))))
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
(let _157_1116 = (let _157_1115 = (let _157_1114 = (let _157_1113 = (let _157_1112 = (FStar_Absyn_Print.sli l)
in (Prims.strcat _157_1112 " not found"))
in (Prims.strcat "Effect name " _157_1113))
in ((_157_1114), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_157_1115))
in (Prims.raise _157_1116))
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
| _62_3073 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected reifiable sub-effect"), (d.FStar_Parser_AST.drange)))))
end))
in (

let lift = (let _157_1119 = (non_reifiable l.FStar_Parser_AST.lift_op)
in (desugar_typ env _157_1119))
in (

let se = FStar_Absyn_Syntax.Sig_sub_effect ((({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))))))
end)))


let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _62_3081 d -> (match (_62_3081) with
| (env, sigelts) -> begin
(

let _62_3085 = (desugar_decl env d)
in (match (_62_3085) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.fsdoc Prims.option  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]


let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let open_ns = (fun mname d -> (

let d = if ((FStar_List.length mname.FStar_Ident.ns) <> (Prims.parse_int "0")) then begin
(let _157_1144 = (let _157_1143 = (let _157_1141 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_157_1141))
in (let _157_1142 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _157_1143 _157_1142 None)))
in (_157_1144)::d)
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

let _62_3112 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _157_1146 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _157_1145 = (open_ns mname decls)
in ((_157_1146), (mname), (_157_1145), (true))))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _157_1148 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _157_1147 = (open_ns mname decls)
in ((_157_1148), (mname), (_157_1147), (false))))
end)
in (match (_62_3112) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _62_3115 = (desugar_decls env decls)
in (match (_62_3115) with
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
| FStar_Parser_AST.Interface (mname, _62_3126, _62_3128) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _62_3136 = (desugar_modul_common curmod env m)
in (match (_62_3136) with
| (x, y, _62_3135) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (

let _62_3142 = (desugar_modul_common None env m)
in (match (_62_3142) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (

let _62_3144 = if (FStar_Options.dump_module modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _157_1159 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _157_1159))
end else begin
()
end
in (let _157_1160 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in ((_157_1160), (modul)))))
end)))


let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (

let _62_3157 = (FStar_List.fold_left (fun _62_3150 m -> (match (_62_3150) with
| (env, mods) -> begin
(

let _62_3154 = (desugar_modul env m)
in (match (_62_3154) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_62_3157) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (

let _62_3162 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_62_3162) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (

let _62_3163 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _62_3163.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _62_3163.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _62_3163.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _62_3163.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _62_3163.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _62_3163.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _62_3163.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _62_3163.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _62_3163.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _62_3163.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _62_3163.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (

let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))






open Prims
# 30 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let imp_tag : FStar_Absyn_Syntax.arg_qualifier = FStar_Absyn_Syntax.Implicit (false)

# 31 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _63_1 -> (match (_63_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (imp_tag)
end
| _63_35 -> begin
None
end))

# 35 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 37 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (imp_tag))
end
| _63_42 -> begin
(t, None)
end))

# 42 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_63_46) -> begin
true
end
| _63_49 -> begin
false
end)))))

# 47 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _63_54 -> begin
t
end))

# 50 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec unlabel : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _63_60, _63_62) -> begin
(unlabel t)
end
| _63_66 -> begin
t
end))

# 55 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _165_17 = (let _165_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_165_16))
in (FStar_Parser_AST.mk_term _165_17 r FStar_Parser_AST.Kind)))

# 58 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (let name_of_char = (fun _63_2 -> (match (_63_2) with
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
| _63_89 -> begin
"UNKNOWN"
end))
in (let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _165_28 = (let _165_26 = (FStar_Util.char_at s i)
in (name_of_char _165_26))
in (let _165_27 = (aux (i + 1))
in (_165_28)::_165_27))
end)
in (let _165_30 = (let _165_29 = (aux 0)
in (FStar_String.concat "_" _165_29))
in (Prims.strcat "op_" _165_30)))))

# 84 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _165_40 = (let _165_39 = (let _165_38 = (let _165_37 = (compile_op n s)
in (_165_37, r))
in (FStar_Absyn_Syntax.mk_ident _165_38))
in (_165_39)::[])
in (FStar_All.pipe_right _165_40 FStar_Absyn_Syntax.lid_of_ids)))

# 86 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (let r = (fun l -> (let _165_51 = (FStar_Ident.set_lid_range l rng)
in Some (_165_51)))
in (let fallback = (fun _63_103 -> (match (()) with
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
| _63_125 -> begin
None
end)
end))
in (match ((let _165_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _165_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _63_136); FStar_Absyn_Syntax.tk = _63_133; FStar_Absyn_Syntax.pos = _63_131; FStar_Absyn_Syntax.fvs = _63_129; FStar_Absyn_Syntax.uvs = _63_127}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _63_142 -> begin
(fallback ())
end))))

# 116 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (let r = (fun l -> (let _165_65 = (FStar_Ident.set_lid_range l rng)
in Some (_165_65)))
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
(match ((let _165_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _165_66))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _63_165; FStar_Absyn_Syntax.pos = _63_163; FStar_Absyn_Syntax.fvs = _63_161; FStar_Absyn_Syntax.uvs = _63_159}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _63_171 -> begin
None
end)
end)))

# 133 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec is_type : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _165_73 = (unparen t)
in _165_73.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_63_176) -> begin
true
end
| FStar_Parser_AST.Op ("*", hd::_63_180) -> begin
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
| _63_231 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_63_254) -> begin
true
end
| _63_257 -> begin
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
| FStar_Parser_AST.Product (_63_298, t) -> begin
(not ((is_kind env t)))
end
| FStar_Parser_AST.If (t, t1, t2) -> begin
(((is_type env t) || (is_type env t1)) || (is_type env t2))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let rec aux = (fun env pats -> (match (pats) with
| [] -> begin
(is_type env t)
end
| hd::pats -> begin
(match (hd.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatVar (_)) -> begin
(aux env pats)
end
| FStar_Parser_AST.PatTvar (id, _63_324) -> begin
(let _63_330 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_63_330) with
| (env, _63_329) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _165_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _165_78 Prims.fst))
end
| _63_345 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _63_348 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_63_353); FStar_Parser_AST.prange = _63_351}, _63_357)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_63_369); FStar_Parser_AST.prange = _63_367}, _63_373); FStar_Parser_AST.prange = _63_365}, _63_378)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_63_388); FStar_Parser_AST.prange = _63_386}, _63_392)::[], t) -> begin
(is_type env t)
end
| _63_399 -> begin
false
end)
end)
and is_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _165_81 = (unparen t)
in _165_81.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_408; FStar_Ident.ident = _63_406; FStar_Ident.nsstr = _63_404; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_63_412, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _63_425 -> begin
false
end)
end)

# 210 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec is_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  Prims.bool = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_63_429) -> begin
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
| FStar_Parser_AST.Variable (_63_444) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.FStar_Parser_AST.brange))))
end
| FStar_Parser_AST.TVariable (_63_447) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_63_450) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)

# 225 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _165_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _165_92)))

# 229 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_63_466) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _63_473 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_63_473) with
| (env, _63_472) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_63_475, term) -> begin
(let _165_99 = (free_type_vars env term)
in (env, _165_99))
end
| FStar_Parser_AST.TAnnotated (id, _63_481) -> begin
(let _63_487 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_63_487) with
| (env, _63_486) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _165_100 = (free_type_vars env t)
in (env, _165_100))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _165_103 = (unparen t)
in _165_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _63_496 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_63_532, ts) -> begin
(FStar_List.collect (fun _63_539 -> (match (_63_539) with
| (t, _63_538) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_63_541, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _63_548) -> begin
(let _165_106 = (free_type_vars env t1)
in (let _165_105 = (free_type_vars env t2)
in (FStar_List.append _165_106 _165_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(let _63_557 = (free_type_vars_b env b)
in (match (_63_557) with
| (env, f) -> begin
(let _165_107 = (free_type_vars env t)
in (FStar_List.append f _165_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(let _63_573 = (FStar_List.fold_left (fun _63_566 binder -> (match (_63_566) with
| (env, free) -> begin
(let _63_570 = (free_type_vars_b env binder)
in (match (_63_570) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_63_573) with
| (env, free) -> begin
(let _165_110 = (free_type_vars env body)
in (FStar_List.append free _165_110))
end))
end
| FStar_Parser_AST.Project (t, _63_576) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 289 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (let rec aux = (fun args t -> (match ((let _165_117 = (unparen t)
in _165_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _63_620 -> begin
(t, args)
end))
in (aux [] t)))

# 296 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (let ftv = (let _165_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _165_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _165_126 = (let _165_125 = (let _165_124 = (kind_star x.FStar_Ident.idRange)
in (x, _165_124))
in FStar_Parser_AST.TAnnotated (_165_125))
in (FStar_Parser_AST.mk_binder _165_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 304 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (let ftv = (let _165_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _165_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _165_135 = (let _165_134 = (let _165_133 = (kind_star x.FStar_Ident.idRange)
in (x, _165_133))
in FStar_Parser_AST.TAnnotated (_165_134))
in (FStar_Parser_AST.mk_binder _165_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (let t = (match ((let _165_136 = (unlabel t)
in _165_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_63_633) -> begin
t
end
| _63_636 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 315 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _63_646 -> begin
(bs, t)
end))

# 319 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _63_650) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_63_656); FStar_Parser_AST.prange = _63_654}, _63_660) -> begin
true
end
| _63_664 -> begin
false
end))

# 324 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _63_676 = (destruct_app_pattern env is_top_level p)
in (match (_63_676) with
| (name, args, _63_675) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_681); FStar_Parser_AST.prange = _63_678}, args) when is_top_level -> begin
(let _165_150 = (let _165_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_165_149))
in (_165_150, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_692); FStar_Parser_AST.prange = _63_689}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _63_700 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 335 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

type bnd =
| TBinder of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual)
| VBinder of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)

# 336 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let is_TBinder = (fun _discr_ -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 337 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let is_VBinder = (fun _discr_ -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 338 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 336 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let ___TBinder____0 : bnd  ->  (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual) = (fun projectee -> (match (projectee) with
| TBinder (_63_703) -> begin
_63_703
end))

# 337 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let ___VBinder____0 : bnd  ->  (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual) = (fun projectee -> (match (projectee) with
| VBinder (_63_706) -> begin
_63_706
end))

# 338 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let ___LetBinder____0 : bnd  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| LetBinder (_63_709) -> begin
_63_709
end))

# 339 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _63_3 -> (match (_63_3) with
| TBinder (a, k, aq) -> begin
(FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder (x, t, aq) -> begin
(FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _63_722 -> begin
(FStar_All.failwith "Impossible")
end))

# 343 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _63_4 -> (match (_63_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _63_729 -> begin
None
end))

# 347 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax), (FStar_Ident.ident Prims.option * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) * FStar_Parser_DesugarEnv.env) = (fun env imp _63_5 -> (match (_63_5) with
| FStar_Util.Inl (None, k) -> begin
((FStar_Absyn_Syntax.null_t_binder k), env)
end
| FStar_Util.Inr (None, t) -> begin
((FStar_Absyn_Syntax.null_v_binder t), env)
end
| FStar_Util.Inl (Some (a), k) -> begin
(let _63_748 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_63_748) with
| (env, a) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual imp)), env)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _63_756 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_63_756) with
| (env, x) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual imp)), env)
end))
end))

# 357 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

type env_t =
FStar_Parser_DesugarEnv.env

# 358 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list

# 360 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let label_conjuncts : Prims.string  ->  Prims.bool  ->  Prims.string Prims.option  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun tag polarity label_opt f -> (let label = (fun f -> (let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _63_766 -> begin
(let _165_213 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _165_213))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled ((f, msg, polarity))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _165_217 = (let _165_216 = (aux g)
in FStar_Parser_AST.Paren (_165_216))
in (FStar_Parser_AST.mk_term _165_217 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", f1::f2::[]) -> begin
(let _165_223 = (let _165_222 = (let _165_221 = (let _165_220 = (aux f1)
in (let _165_219 = (let _165_218 = (aux f2)
in (_165_218)::[])
in (_165_220)::_165_219))
in ("/\\", _165_221))
in FStar_Parser_AST.Op (_165_222))
in (FStar_Parser_AST.mk_term _165_223 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _165_227 = (let _165_226 = (let _165_225 = (aux f2)
in (let _165_224 = (aux f3)
in (f1, _165_225, _165_224)))
in FStar_Parser_AST.If (_165_226))
in (FStar_Parser_AST.mk_term _165_227 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _165_230 = (let _165_229 = (let _165_228 = (aux g)
in (binders, _165_228))
in FStar_Parser_AST.Abs (_165_229))
in (FStar_Parser_AST.mk_term _165_230 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _63_788 -> begin
(label f)
end))
in (aux f))))

# 386 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _63_792 -> (match (_63_792) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))

# 388 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _63_6 -> (match (_63_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _63_803 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
(l, e, y)
end
| _63_808 -> begin
(let _63_811 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_63_811) with
| (e, x) -> begin
((FStar_Util.Inr (x))::l, e, x)
end))
end))
in (let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _63_7 -> (match (_63_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _63_820 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
(l, e, b)
end
| _63_825 -> begin
(let _63_828 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_63_828) with
| (e, a) -> begin
((FStar_Util.Inl (a))::l, e, a)
end))
end))
in (let rec aux = (fun loc env p -> (let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p.FStar_Parser_AST.prange))
in (let pos_r = (fun r q -> (FStar_Absyn_Syntax.withinfo q None r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(let _63_850 = (aux loc env p)
in (match (_63_850) with
| (loc, env, var, p, _63_849) -> begin
(let _63_867 = (FStar_List.fold_left (fun _63_854 p -> (match (_63_854) with
| (loc, env, ps) -> begin
(let _63_863 = (aux loc env p)
in (match (_63_863) with
| (loc, env, _63_859, p, _63_862) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_63_867) with
| (loc, env, ps) -> begin
(let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (let _63_869 = (let _165_302 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _165_302))
in (loc, env, var, pat, false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_63_876) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(let _63_882 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar ((x, imp)); FStar_Parser_AST.prange = _63_882.FStar_Parser_AST.prange})
end
| _63_885 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end)
end else begin
p
end
in (let _63_892 = (aux loc env p)
in (match (_63_892) with
| (loc, env', binder, p, imp) -> begin
(let binder = (match (binder) with
| LetBinder (_63_894) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _63_898, aq) -> begin
(let _165_304 = (let _165_303 = (desugar_kind env t)
in (x, _165_303, aq))
in TBinder (_165_304))
end
| VBinder (x, _63_904, aq) -> begin
(let t = (close_fun env t)
in (let _165_306 = (let _165_305 = (desugar_typ env t)
in (x, _165_305, aq))
in VBinder (_165_306)))
end)
in (loc, env', binder, p, imp))
end)))
end
| FStar_Parser_AST.PatTvar (a, imp) -> begin
(let aq = if imp then begin
Some (imp_tag)
end else begin
None
end
in if (a.FStar_Ident.idText = "\'_") then begin
(let a = (FStar_All.pipe_left FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _165_307 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, FStar_Absyn_Syntax.kun, aq)), _165_307, imp)))
end else begin
(let _63_919 = (resolvea loc env a)
in (match (_63_919) with
| (loc, env, abvd) -> begin
(let _165_308 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, FStar_Absyn_Syntax.kun, aq)), _165_308, imp))
end))
end)
end
| FStar_Parser_AST.PatWild -> begin
(let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _165_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _165_309, false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _165_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _165_310, false)))
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(let aq = if imp then begin
Some (imp_tag)
end else begin
None
end
in (let _63_934 = (resolvex loc env x)
in (match (_63_934) with
| (loc, env, xbvd) -> begin
(let _165_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, FStar_Absyn_Syntax.tun, aq)), _165_311, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _165_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _165_312, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _63_940}, args) -> begin
(let _63_962 = (FStar_List.fold_right (fun arg _63_951 -> (match (_63_951) with
| (loc, env, args) -> begin
(let _63_958 = (aux loc env arg)
in (match (_63_958) with
| (loc, env, _63_955, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_63_962) with
| (loc, env, args) -> begin
(let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _165_315 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _165_315, false))))
end))
end
| FStar_Parser_AST.PatApp (_63_966) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(let _63_986 = (FStar_List.fold_right (fun pat _63_974 -> (match (_63_974) with
| (loc, env, pats) -> begin
(let _63_982 = (aux loc env pat)
in (match (_63_982) with
| (loc, env, _63_978, pat, _63_981) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_63_986) with
| (loc, env, pats) -> begin
(let pat = (let _165_322 = (let _165_321 = (let _165_320 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _165_320))
in (FStar_All.pipe_left _165_321 (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid), Some (FStar_Absyn_Syntax.Data_ctor), [])))))
in (FStar_List.fold_right (fun hd tl -> (let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid), Some (FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[])))))) pats _165_322))
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(let _63_1012 = (FStar_List.fold_left (fun _63_999 p -> (match (_63_999) with
| (loc, env, pats) -> begin
(let _63_1008 = (aux loc env p)
in (match (_63_1008) with
| (loc, env, _63_1004, pat, _63_1007) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_63_1012) with
| (loc, env, args) -> begin
(let args = (FStar_List.rev args)
in (let l = if dep then begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _63_1018) -> begin
v
end
| _63_1022 -> begin
(FStar_All.failwith "impossible")
end)
in (let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _165_325 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _165_325, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(let _63_1032 = (FStar_List.hd fields)
in (match (_63_1032) with
| (f, _63_1031) -> begin
(let _63_1036 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_63_1036) with
| (record, _63_1035) -> begin
(let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _63_1039 -> (match (_63_1039) with
| (f, p) -> begin
(let _165_327 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_165_327, p))
end))))
in (let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _63_1044 -> (match (_63_1044) with
| (f, _63_1043) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _63_1048 -> (match (_63_1048) with
| (g, _63_1047) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_63_1051, p) -> begin
p
end)
end))))
in (let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (let _63_1063 = (aux loc env app)
in (match (_63_1063) with
| (env, e, b, p, _63_1062) -> begin
(let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _63_1066, args) -> begin
(let _165_335 = (let _165_334 = (let _165_333 = (let _165_332 = (let _165_331 = (let _165_330 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _165_330))
in FStar_Absyn_Syntax.Record_ctor (_165_331))
in Some (_165_332))
in (fv, _165_333, args))
in FStar_Absyn_Syntax.Pat_cons (_165_334))
in (FStar_All.pipe_left pos _165_335))
end
| _63_1071 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (let _63_1080 = (aux [] env p)
in (match (_63_1080) with
| (_63_1074, env, b, p, _63_1079) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _63_1086) -> begin
(let _165_341 = (let _165_340 = (let _165_339 = (FStar_Parser_DesugarEnv.qualify env x)
in (_165_339, FStar_Absyn_Syntax.tun))
in LetBinder (_165_340))
in (env, _165_341, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _63_1093); FStar_Parser_AST.prange = _63_1090}, t) -> begin
(let _165_345 = (let _165_344 = (let _165_343 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _165_342 = (desugar_typ env t)
in (_165_343, _165_342)))
in LetBinder (_165_344))
in (env, _165_345, None))
end
| _63_1101 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(let _63_1105 = (desugar_data_pat env p)
in (match (_63_1105) with
| (env, binder, p) -> begin
(let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _63_1116 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _63_1120 env pat -> (let _63_1128 = (desugar_data_pat env pat)
in (match (_63_1128) with
| (env, _63_1126, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _165_355 = (desugar_typ env t)
in FStar_Util.Inl (_165_355))
end else begin
(let _165_356 = (desugar_exp env t)
in FStar_Util.Inr (_165_356))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (let setpos = (fun e -> (let _63_1142 = e
in {FStar_Absyn_Syntax.n = _63_1142.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _63_1142.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _63_1142.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _63_1142.FStar_Absyn_Syntax.uvs}))
in (match ((let _165_376 = (unparen top)
in _165_376.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (c) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_constant c))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_vlid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (l) -> begin
(let op = (FStar_Absyn_Util.fvar None l (FStar_Ident.range_of_lid l))
in (let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _165_380 = (desugar_typ_or_exp env t)
in (_165_380, None)))))
in (let _165_381 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _165_381))))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
if (l.FStar_Ident.str = "ref") then begin
(match ((FStar_Parser_DesugarEnv.try_lookup_lid env FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Identifier \'ref\' not found; include lib/FStar.ST.fst in your path", (FStar_Ident.range_of_lid l)))))
end
| Some (e) -> begin
(setpos e)
end)
end else begin
(let _165_382 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _165_382))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let dt = (let _165_387 = (let _165_386 = (let _165_385 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_165_385, Some (FStar_Absyn_Syntax.Data_ctor)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _165_386))
in (FStar_All.pipe_left pos _165_387))
in (match (args) with
| [] -> begin
dt
end
| _63_1169 -> begin
(let args = (FStar_List.map (fun _63_1172 -> (match (_63_1172) with
| (t, imp) -> begin
(let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _165_392 = (let _165_391 = (let _165_390 = (let _165_389 = (FStar_Absyn_Util.mk_exp_app dt args)
in (_165_389, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_165_390))
in (FStar_Absyn_Syntax.mk_Exp_meta _165_391))
in (FStar_All.pipe_left setpos _165_392)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let _63_1209 = (FStar_List.fold_left (fun _63_1181 pat -> (match (_63_1181) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _63_1184}, t) -> begin
(let ftvs = (let _165_395 = (free_type_vars env t)
in (FStar_List.append _165_395 ftvs))
in (let _165_397 = (let _165_396 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _165_396))
in (_165_397, ftvs)))
end
| FStar_Parser_AST.PatTvar (a, _63_1196) -> begin
(let _165_399 = (let _165_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _165_398))
in (_165_399, ftvs))
end
| FStar_Parser_AST.PatAscribed (_63_1200, t) -> begin
(let _165_401 = (let _165_400 = (free_type_vars env t)
in (FStar_List.append _165_400 ftvs))
in (env, _165_401))
end
| _63_1205 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_63_1209) with
| (_63_1207, ftv) -> begin
(let ftv = (sort_ftv ftv)
in (let binders = (let _165_403 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _165_403 binders))
in (let rec aux = (fun env bs sc_pat_opt _63_8 -> (match (_63_8) with
| [] -> begin
(let body = (desugar_exp env body)
in (let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(FStar_Absyn_Syntax.mk_Exp_match (sc, ((pat, None, body))::[]) None body.FStar_Absyn_Syntax.pos)
end
| None -> begin
body
end)
in (FStar_Absyn_Syntax.mk_Exp_abs' ((FStar_List.rev bs), body) None top.FStar_Parser_AST.range)))
end
| p::rest -> begin
(let _63_1232 = (desugar_binding_pat env p)
in (match (_63_1232) with
| (env, b, pat) -> begin
(let _63_1292 = (match (b) with
| LetBinder (_63_1234) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _165_412 = (binder_of_bnd b)
in (_165_412, sc_pat_opt))
end
| VBinder (x, t, aq) -> begin
(let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _63_1249) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _165_414 = (let _165_413 = (FStar_Absyn_Util.bvar_to_exp b)
in (_165_413, p))
in Some (_165_414))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Absyn_Syntax.n, p'.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Exp_bvar (_63_1263), _63_1266) -> begin
(let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (let sc = (let _165_420 = (let _165_419 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _165_418 = (let _165_417 = (let _165_416 = (let _165_415 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _165_415))
in (_165_416)::[])
in ((FStar_Absyn_Syntax.varg sc))::_165_417)
in (_165_419, _165_418)))
in (FStar_Absyn_Syntax.mk_Exp_app _165_420 None top.FStar_Parser_AST.range))
in (let p = (let _165_421 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))) None _165_421))
in Some ((sc, p)))))
end
| (FStar_Absyn_Syntax.Exp_app (_63_1272, args), FStar_Absyn_Syntax.Pat_cons (_63_1277, _63_1279, pats)) -> begin
(let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (let sc = (let _165_427 = (let _165_426 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _165_425 = (let _165_424 = (let _165_423 = (let _165_422 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _165_422))
in (_165_423)::[])
in (FStar_List.append args _165_424))
in (_165_426, _165_425)))
in (FStar_Absyn_Syntax.mk_Exp_app _165_427 None top.FStar_Parser_AST.range))
in (let p = (let _165_428 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), (FStar_List.append pats (((p, false))::[]))))) None _165_428))
in Some ((sc, p)))))
end
| _63_1288 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((FStar_Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_63_1292) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _63_1296; FStar_Parser_AST.level = _63_1294}, arg, _63_1302) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(let phi = (desugar_formula env arg)
in (let _165_438 = (let _165_437 = (let _165_436 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _165_435 = (let _165_434 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _165_433 = (let _165_432 = (let _165_431 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _165_431))
in (_165_432)::[])
in (_165_434)::_165_433))
in (_165_436, _165_435)))
in (FStar_Absyn_Syntax.mk_Exp_app _165_437))
in (FStar_All.pipe_left pos _165_438)))
end
| FStar_Parser_AST.App (_63_1307) -> begin
(let rec aux = (fun args e -> (match ((let _165_443 = (unparen e)
in _165_443.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(let arg = (let _165_444 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _165_444))
in (aux ((arg)::args) e))
end
| _63_1319 -> begin
(let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _165_450 = (let _165_449 = (let _165_448 = (let _165_447 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_165_447, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_165_448))
in (FStar_Absyn_Syntax.mk_Exp_meta _165_449))
in (FStar_All.pipe_left setpos _165_450))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(let ds_let_rec = (fun _63_1335 -> (match (()) with
| () -> begin
(let bindings = ((pat, _snd))::_tl
in (let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _63_1339 -> (match (_63_1339) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _165_454 = (destruct_app_pattern env top_level p)
in (_165_454, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _165_455 = (destruct_app_pattern env top_level p)
in (_165_455, def))
end
| _63_1345 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_1350); FStar_Parser_AST.prange = _63_1347}, t) -> begin
if top_level then begin
(let _165_458 = (let _165_457 = (let _165_456 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_165_456))
in (_165_457, [], Some (t)))
in (_165_458, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _63_1359) -> begin
if top_level then begin
(let _165_461 = (let _165_460 = (let _165_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_165_459))
in (_165_460, [], None))
in (_165_461, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _63_1363 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (let _63_1389 = (FStar_List.fold_left (fun _63_1367 _63_1376 -> (match ((_63_1367, _63_1376)) with
| ((env, fnames), ((f, _63_1370, _63_1372), _63_1375)) -> begin
(let _63_1386 = (match (f) with
| FStar_Util.Inl (x) -> begin
(let _63_1381 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_63_1381) with
| (env, xx) -> begin
(env, FStar_Util.Inl (xx))
end))
end
| FStar_Util.Inr (l) -> begin
(let _165_464 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in (_165_464, FStar_Util.Inr (l)))
end)
in (match (_63_1386) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_63_1389) with
| (env', fnames) -> begin
(let fnames = (FStar_List.rev fnames)
in (let desugar_one_def = (fun env lbname _63_1400 -> (match (_63_1400) with
| ((_63_1395, args, result_t), def) -> begin
(let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _165_471 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _165_471 FStar_Parser_AST.Expr))
end)
in (let def = (match (args) with
| [] -> begin
def
end
| _63_1407 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (let body = (desugar_exp env def)
in (mk_lb (lbname, FStar_Absyn_Syntax.tun, body)))))
end))
in (let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (let body = (desugar_exp env' body)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (let ds_non_rec = (fun pat t1 t2 -> (let t1 = (desugar_exp env t1)
in (let _63_1420 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_63_1420) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_63_1422) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder (x, t, _63_1432) -> begin
(let body = (desugar_exp env t2)
in (let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _165_483 = (let _165_482 = (FStar_Absyn_Util.bvd_to_exp x t)
in (_165_482, ((pat, None, body))::[]))
in (FStar_Absyn_Syntax.mk_Exp_match _165_483 None body.FStar_Absyn_Syntax.pos))
end)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ((mk_lb (FStar_Util.Inl (x), t, t1)))::[]), body)))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec ())
end else begin
(ds_non_rec pat _snd body)
end))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _165_496 = (let _165_495 = (let _165_494 = (desugar_exp env t1)
in (let _165_493 = (let _165_492 = (let _165_488 = (desugar_exp env t2)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range), None, _165_488))
in (let _165_491 = (let _165_490 = (let _165_489 = (desugar_exp env t3)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range), None, _165_489))
in (_165_490)::[])
in (_165_492)::_165_491))
in (_165_494, _165_493)))
in (FStar_Absyn_Syntax.mk_Exp_match _165_495))
in (FStar_All.pipe_left pos _165_496))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(let r = top.FStar_Parser_AST.range
in (let handler = (FStar_Parser_AST.mk_function branches r r)
in (let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Absyn_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(let desugar_branch = (fun _63_1471 -> (match (_63_1471) with
| (pat, wopt, b) -> begin
(let _63_1474 = (desugar_match_pat env pat)
in (match (_63_1474) with
| (env, pat) -> begin
(let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _165_499 = (desugar_exp env e)
in Some (_165_499))
end)
in (let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _165_505 = (let _165_504 = (let _165_503 = (desugar_exp env e)
in (let _165_502 = (FStar_List.map desugar_branch branches)
in (_165_503, _165_502)))
in (FStar_Absyn_Syntax.mk_Exp_match _165_504))
in (FStar_All.pipe_left pos _165_505)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _165_511 = (let _165_510 = (let _165_509 = (desugar_exp env e)
in (let _165_508 = (desugar_typ env t)
in (_165_509, _165_508, None)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _165_510))
in (FStar_All.pipe_left pos _165_511))
end
| FStar_Parser_AST.Record (_63_1485, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(let _63_1496 = (FStar_List.hd fields)
in (match (_63_1496) with
| (f, _63_1495) -> begin
(let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (let _63_1502 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_63_1502) with
| (record, _63_1501) -> begin
(let get_field = (fun xopt f -> (let fn = f.FStar_Ident.ident
in (let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _63_1510 -> (match (_63_1510) with
| (g, _63_1509) -> begin
(let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_63_1514, e) -> begin
(let _165_519 = (qfn fn)
in (_165_519, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _165_522 = (let _165_521 = (let _165_520 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_165_520, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_165_521))
in (Prims.raise _165_522))
end
| Some (x) -> begin
(let _165_523 = (qfn fn)
in (_165_523, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (let recterm = (match (eopt) with
| None -> begin
(let _165_528 = (let _165_527 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _63_1526 -> (match (_63_1526) with
| (f, _63_1525) -> begin
(let _165_526 = (let _165_525 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _165_525))
in (_165_526, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_DesugarEnv.constrname, _165_527))
in FStar_Parser_AST.Construct (_165_528))
end
| Some (e) -> begin
(let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (let xterm = (let _165_530 = (let _165_529 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_165_529))
in (FStar_Parser_AST.mk_term _165_530 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (let record = (let _165_533 = (let _165_532 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _63_1534 -> (match (_63_1534) with
| (f, _63_1533) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _165_532))
in FStar_Parser_AST.Record (_165_533))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _63_1557); FStar_Absyn_Syntax.tk = _63_1554; FStar_Absyn_Syntax.pos = _63_1552; FStar_Absyn_Syntax.fvs = _63_1550; FStar_Absyn_Syntax.uvs = _63_1548}, args); FStar_Absyn_Syntax.tk = _63_1546; FStar_Absyn_Syntax.pos = _63_1544; FStar_Absyn_Syntax.fvs = _63_1542; FStar_Absyn_Syntax.uvs = _63_1540}, FStar_Absyn_Syntax.Data_app)) -> begin
(let e = (let _165_543 = (let _165_542 = (let _165_541 = (let _165_540 = (let _165_539 = (let _165_538 = (let _165_537 = (let _165_536 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _165_536))
in FStar_Absyn_Syntax.Record_ctor (_165_537))
in Some (_165_538))
in (fv, _165_539))
in (FStar_Absyn_Syntax.mk_Exp_fvar _165_540 None e.FStar_Absyn_Syntax.pos))
in (_165_541, args))
in (FStar_Absyn_Syntax.mk_Exp_app _165_542))
in (FStar_All.pipe_left pos _165_543))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Data_app)))))
end
| _63_1571 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(let _63_1578 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_63_1578) with
| (fieldname, is_rec) -> begin
(let e = (desugar_exp env e)
in (let fn = (let _63_1583 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_63_1583) with
| (ns, _63_1582) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _165_548 = (let _165_547 = (let _165_546 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (_165_546, ((FStar_Absyn_Syntax.varg e))::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _165_547))
in (FStar_All.pipe_left pos _165_548)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _63_1589 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _63_1596 = t
in {FStar_Absyn_Syntax.n = _63_1596.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _63_1596.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _63_1596.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _63_1596.FStar_Absyn_Syntax.uvs}))
in (let top = (unparen top)
in (let head_and_args = (fun t -> (let rec aux = (fun args t -> (match ((let _165_571 = (unparen t)
in _165_571.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _63_1614 -> begin
(t, args)
end))
in (aux [] t)))
in (match (top.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.tun)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(let t = (label_conjuncts "pre-condition" true lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _165_572 = (desugar_exp env t)
in (FStar_All.pipe_right _165_572 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _165_573 = (desugar_exp env t)
in (FStar_All.pipe_right _165_573 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", t1::_63_1628::[]) -> begin
if (is_type env t1) then begin
(let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(let rest = (flatten t2)
in (t1)::rest)
end
| _63_1643 -> begin
(t)::[]
end))
in (let targs = (let _165_578 = (flatten top)
in (FStar_All.pipe_right _165_578 (FStar_List.map (fun t -> (let _165_577 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _165_577))))))
in (let tup = (let _165_579 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _165_579))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end else begin
(let _165_585 = (let _165_584 = (let _165_583 = (let _165_582 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _165_582))
in (_165_583, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_165_584))
in (Prims.raise _165_585))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _165_586 = (desugar_exp env top)
in (FStar_All.pipe_right _165_586 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(let args = (FStar_List.map (fun t -> (let _165_588 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _165_588))) args)
in (let _165_589 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _165_589 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _165_590 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _165_590))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _165_591 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _165_591))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _165_592 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _165_592)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let t = (let _165_593 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _165_593))
in (let args = (FStar_List.map (fun _63_1679 -> (match (_63_1679) with
| (t, imp) -> begin
(let _165_595 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _165_595))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(let rec aux = (fun env bs _63_9 -> (match (_63_9) with
| [] -> begin
(let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.rev bs), body))))
end
| hd::tl -> begin
(let _63_1697 = (desugar_binding_pat env hd)
in (match (_63_1697) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _165_607 = (let _165_606 = (let _165_605 = (let _165_604 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _165_604))
in (_165_605, hd.FStar_Parser_AST.prange))
in FStar_Absyn_Syntax.Error (_165_606))
in (Prims.raise _165_607))
end
| None -> begin
(let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_63_1703) -> begin
(let rec aux = (fun args e -> (match ((let _165_612 = (unparen e)
in _165_612.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(let arg = (let _165_613 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _165_613))
in (aux ((arg)::args) e))
end
| _63_1715 -> begin
(let head = (desugar_typ env e)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Product ([], t) -> begin
(FStar_All.failwith "Impossible: product with no binders")
end
| FStar_Parser_AST.Product (binders, t) -> begin
(let _63_1727 = (uncurry binders t)
in (match (_63_1727) with
| (bs, t) -> begin
(let rec aux = (fun env bs _63_10 -> (match (_63_10) with
| [] -> begin
(let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.rev bs), cod))))
end
| hd::tl -> begin
(let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (let bb = (desugar_binder mlenv hd)
in (let _63_1741 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_63_1741) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _63_1748) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(let _63_1762 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _63_1754), env) -> begin
(x, env)
end
| _63_1759 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_63_1762) with
| (b, env) -> begin
(let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _165_624 = (desugar_exp env f)
in (FStar_All.pipe_right _165_624 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _165_632 = (let _165_631 = (let _165_630 = (desugar_typ env t)
in (let _165_629 = (desugar_kind env k)
in (_165_630, _165_629)))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _165_631))
in (FStar_All.pipe_left wpos _165_632))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(let _63_1796 = (FStar_List.fold_left (fun _63_1781 b -> (match (_63_1781) with
| (env, tparams, typs) -> begin
(let _63_1785 = (desugar_exp_binder env b)
in (match (_63_1785) with
| (xopt, t) -> begin
(let _63_1791 = (match (xopt) with
| None -> begin
(let _165_635 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in (env, _165_635))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_63_1791) with
| (env, x) -> begin
(let _165_639 = (let _165_638 = (let _165_637 = (let _165_636 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _165_636))
in (_165_637)::[])
in (FStar_List.append typs _165_638))
in (env, (FStar_List.append tparams (((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _165_639))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_63_1796) with
| (env, _63_1794, targs) -> begin
(let tup = (let _165_640 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _165_640))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| FStar_Parser_AST.Record (_63_1799) -> begin
(FStar_All.failwith "Unexpected record type")
end
| FStar_Parser_AST.Let (false, (x, v)::[], t) -> begin
(let let_v = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.let_in_typ)) top.FStar_Parser_AST.range top.FStar_Parser_AST.level), v, FStar_Parser_AST.Nothing))) v.FStar_Parser_AST.range v.FStar_Parser_AST.level)
in (let t' = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((let_v, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs (((x)::[], t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), FStar_Parser_AST.Nothing))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_typ env t')))
end
| (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _63_1818 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _63_1820 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error ((msg, r)))))
in (let pre_process_comp_typ = (fun t -> (let _63_1831 = (head_and_args t)
in (match (_63_1831) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(let unit = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (let _63_1857 = (FStar_All.pipe_right args (FStar_List.partition (fun _63_1839 -> (match (_63_1839) with
| (arg, _63_1838) -> begin
(match ((let _165_652 = (unparen arg)
in _165_652.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _63_1843; FStar_Parser_AST.level = _63_1841}, _63_1848, _63_1850) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _63_1854 -> begin
false
end)
end))))
in (match (_63_1857) with
| (decreases_clause, args) -> begin
(let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (unit)::(req_true)::(ens)::(nil_pat)::[])
end
| req::ens::[] -> begin
(unit)::(req)::(ens)::(nil_pat)::[]
end
| more -> begin
(unit)::more
end)
in (let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct ((lemma, (FStar_List.append args decreases_clause)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _165_653 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _165_653 FStar_Absyn_Const.prims_lid))) -> begin
(let args = (FStar_List.map (fun _63_1872 -> (match (_63_1872) with
| (t, imp) -> begin
(let _165_655 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _165_655))
end)) args)
in (let _165_656 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _165_656 args)))
end
| _63_1875 -> begin
(desugar_typ env t)
end)
end)))
in (let t = (pre_process_comp_typ t)
in (let _63_1879 = (FStar_Absyn_Util.head_and_args t)
in (match (_63_1879) with
| (head, args) -> begin
(match ((let _165_658 = (let _165_657 = (FStar_Absyn_Util.compress_typ head)
in _165_657.FStar_Absyn_Syntax.n)
in (_165_658, args))) with
| (FStar_Absyn_Syntax.Typ_const (eff), (FStar_Util.Inl (result_typ), _63_1886)::rest) -> begin
(let _63_1926 = (FStar_All.pipe_right rest (FStar_List.partition (fun _63_11 -> (match (_63_11) with
| (FStar_Util.Inr (_63_1892), _63_1895) -> begin
false
end
| (FStar_Util.Inl (t), _63_1900) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _63_1909; FStar_Absyn_Syntax.pos = _63_1907; FStar_Absyn_Syntax.fvs = _63_1905; FStar_Absyn_Syntax.uvs = _63_1903}, (FStar_Util.Inr (_63_1914), _63_1917)::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _63_1923 -> begin
false
end)
end))))
in (match (_63_1926) with
| (dec, rest) -> begin
(let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _63_12 -> (match (_63_12) with
| (FStar_Util.Inl (t), _63_1931) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_63_1934, (FStar_Util.Inr (arg), _63_1938)::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _63_1944 -> begin
(FStar_All.failwith "impos")
end)
end
| _63_1946 -> begin
(FStar_All.failwith "impos")
end))))
in if ((FStar_Parser_DesugarEnv.is_effect_name env eff.FStar_Absyn_Syntax.v) || (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid)) then begin
if ((FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Absyn_Syntax.mk_Total result_typ)
end else begin
(let flags = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
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
in (let rest = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(FStar_Util.Inr (pat), aq)::[] -> begin
(let _165_665 = (let _165_664 = (let _165_663 = (let _165_662 = (let _165_661 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((pat, FStar_Absyn_Syntax.Meta_smt_pat))))
in FStar_Util.Inr (_165_661))
in (_165_662, aq))
in (_165_663)::[])
in (ens)::_165_664)
in (req)::_165_665)
end
| _63_1957 -> begin
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
(let _165_667 = (let _165_666 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _165_666))
in (fail _165_667))
end
end)
end))
end
| _63_1960 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _165_669 = (let _165_668 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _165_668))
in (fail _165_669))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (let setpos = (fun kk -> (let _63_1967 = kk
in {FStar_Absyn_Syntax.n = _63_1967.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _63_1967.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _63_1967.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _63_1967.FStar_Absyn_Syntax.uvs}))
in (let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_1976; FStar_Ident.ident = _63_1974; FStar_Ident.nsstr = _63_1972; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_1985; FStar_Ident.ident = _63_1983; FStar_Ident.nsstr = _63_1981; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _165_681 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _165_681))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _63_1993 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(let _63_2001 = (uncurry bs k)
in (match (_63_2001) with
| (bs, k) -> begin
(let rec aux = (fun env bs _63_13 -> (match (_63_13) with
| [] -> begin
(let _165_692 = (let _165_691 = (let _165_690 = (desugar_kind env k)
in ((FStar_List.rev bs), _165_690))
in (FStar_Absyn_Syntax.mk_Kind_arrow _165_691))
in (FStar_All.pipe_left pos _165_692))
end
| hd::tl -> begin
(let _63_2012 = (let _165_693 = (desugar_binder (FStar_Parser_DesugarEnv.default_ml env) hd)
in (FStar_All.pipe_right _165_693 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_63_2012) with
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
(let args = (FStar_List.map (fun _63_2022 -> (match (_63_2022) with
| (t, b) -> begin
(let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _165_695 = (desugar_typ_or_exp env t)
in (_165_695, qual)))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _63_2026 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env f -> (let connective = (fun s -> (match (s) with
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
| _63_2037 -> begin
None
end))
in (let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (let setpos = (fun t -> (let _63_2042 = t
in {FStar_Absyn_Syntax.n = _63_2042.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _63_2042.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _63_2042.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _63_2042.FStar_Absyn_Syntax.uvs}))
in (let desugar_quant = (fun q qt b pats body -> (let tk = (desugar_binder env (let _63_2050 = b
in {FStar_Parser_AST.b = _63_2050.FStar_Parser_AST.b; FStar_Parser_AST.brange = _63_2050.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _63_2050.FStar_Parser_AST.aqual}))
in (let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _165_731 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _165_731)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _63_2065 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_63_2065) with
| (env, a) -> begin
(let pats = (desugar_pats env pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _63_2070 -> begin
(let _165_732 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (FStar_All.pipe_left setpos _165_732))
end)
in (let body = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k)))::[], body)))
in (let _165_737 = (let _165_736 = (let _165_735 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _165_735 FStar_Absyn_Syntax.kun))
in (FStar_Absyn_Util.mk_typ_app _165_736 (((FStar_Absyn_Syntax.targ body))::[])))
in (FStar_All.pipe_left setpos _165_737))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _63_2080 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_63_2080) with
| (env, x) -> begin
(let pats = (desugar_pats env pats)
in (let body = (desugar_formula env body)
in (let body = (match (pats) with
| [] -> begin
body
end
| _63_2085 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (let body = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::[], body)))
in (let _165_742 = (let _165_741 = (let _165_740 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _165_740 FStar_Absyn_Syntax.kun))
in (FStar_Absyn_Util.mk_typ_app _165_741 (((FStar_Absyn_Syntax.targ body))::[])))
in (FStar_All.pipe_left setpos _165_742))))))
end))
end
| _63_2089 -> begin
(FStar_All.failwith "impossible")
end))))
in (let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(let rest = (b')::_rest
in (let body = (let _165_757 = (q (rest, pats, body))
in (let _165_756 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _165_757 _165_756 FStar_Parser_AST.Formula)))
in (let _165_758 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _165_758 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _63_2103 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _165_759 = (unparen f)
in _165_759.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, l, FStar_Absyn_Syntax.dummyRange, p)))))
end
| FStar_Parser_AST.Op ("==", hd::_args) -> begin
(let args = (hd)::_args
in (let args = (FStar_List.map (fun t -> (let _165_761 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _165_761))) args)
in (let eq = if (is_type env hd) then begin
(let _165_762 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _165_762 FStar_Absyn_Syntax.kun))
end else begin
(let _165_763 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _165_763 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match (((connective s), args)) with
| (Some (conn), _63_2129::_63_2127::[]) -> begin
(let _165_768 = (let _165_764 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _165_764 FStar_Absyn_Syntax.kun))
in (let _165_767 = (FStar_List.map (fun x -> (let _165_766 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _165_766))) args)
in (FStar_Absyn_Util.mk_typ_app _165_768 _165_767)))
end
| _63_2134 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _165_769 = (desugar_exp env f)
in (FStar_All.pipe_right _165_769 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _165_774 = (let _165_770 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _165_770 FStar_Absyn_Syntax.kun))
in (let _165_773 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _165_772 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _165_772))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _165_774 _165_773)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _165_776 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _165_776)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(let binders = (_1)::(_2)::_3
in (let _165_778 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _165_778)))
end
| FStar_Parser_AST.QForall (b::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.forall_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.QExists (b::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.exists_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _63_2196 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _165_779 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _165_779))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (desugar_formula' (let _63_2199 = env
in {FStar_Parser_DesugarEnv.curmodule = _63_2199.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _63_2199.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _63_2199.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _63_2199.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _63_2199.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _63_2199.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _63_2199.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _63_2199.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _63_2199.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _63_2199.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _63_2199.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax), (FStar_Ident.ident Prims.option * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _165_784 = (desugar_type_binder env b)
in FStar_Util.Inl (_165_784))
end else begin
(let _165_785 = (desugar_exp_binder env b)
in FStar_Util.Inr (_165_785))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (let _63_2232 = (FStar_List.fold_left (fun _63_2207 b -> (match (_63_2207) with
| (env, out) -> begin
(let tk = (desugar_binder env (let _63_2209 = b
in {FStar_Parser_AST.b = _63_2209.FStar_Parser_AST.b; FStar_Parser_AST.brange = _63_2209.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _63_2209.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _63_2219 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_63_2219) with
| (env, a) -> begin
(env, ((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _63_2227 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_63_2227) with
| (env, x) -> begin
(env, ((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| _63_2229 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_63_2232) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _165_792 = (desugar_typ env t)
in (Some (x), _165_792))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _165_793 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _165_793))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _165_794 = (desugar_typ env t)
in (None, _165_794))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Absyn_Syntax.tun)
end
| _63_2246 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.FStar_Parser_AST.brange))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun env b -> (let fail = (fun _63_2250 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.FStar_Parser_AST.brange))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _165_799 = (desugar_kind env t)
in (Some (x), _165_799))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _165_800 = (desugar_kind env t)
in (None, _165_800))
end
| FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (let _63_2261 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _63_2261.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _63_2261.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _63_2261.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _63_2261.FStar_Absyn_Syntax.uvs}))
end
| _63_2264 -> begin
(fail ())
end)))

# 1197 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_63_2275, k) -> begin
(aux bs k)
end
| _63_2280 -> begin
bs
end))
in (let _165_809 = (aux tps k)
in (FStar_All.pipe_right _165_809 FStar_Absyn_Util.name_binders))))

# 1205 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let mk_data_discriminators : FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Ident.lid  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (let binders = (gather_tc_binders tps k)
in (let p = (FStar_Ident.range_of_lid t)
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _63_2294 -> (match (_63_2294) with
| (x, _63_2293) -> begin
(x, Some (imp_tag))
end))))
in (let binders = (let _165_830 = (let _165_829 = (let _165_828 = (let _165_827 = (let _165_826 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _165_825 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_165_826, _165_825)))
in (FStar_Absyn_Syntax.mk_Typ_app' _165_827 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _165_828))
in (_165_829)::[])
in (FStar_List.append imp_binders _165_830))
in (let disc_type = (let _165_833 = (let _165_832 = (let _165_831 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _165_831 p))
in (binders, _165_832))
in (FStar_Absyn_Syntax.mk_Typ_fun _165_833 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _165_836 = (let _165_835 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in (disc_name, disc_type, _165_835, (FStar_Ident.range_of_lid disc_name)))
in FStar_Absyn_Syntax.Sig_val_decl (_165_836)))))))))))))

# 1218 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let mk_indexed_projectors = (fun fvq refine_domain env _63_2306 lid formals t -> (match (_63_2306) with
| (tc, tps, k) -> begin
(let binders = (gather_tc_binders tps k)
in (let p = (FStar_Ident.range_of_lid lid)
in (let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (let projectee = (let _165_846 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = (FStar_Absyn_Syntax.mk_ident ("projectee", p)); FStar_Absyn_Syntax.realname = _165_846})
in (let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (let arg_binder = (let arg_typ = (let _165_849 = (let _165_848 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _165_847 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_165_848, _165_847)))
in (FStar_Absyn_Syntax.mk_Typ_app' _165_849 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _165_859 = (let _165_858 = (let _165_857 = (let _165_856 = (let _165_855 = (let _165_854 = (let _165_853 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _165_852 = (let _165_851 = (let _165_850 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _165_850))
in (_165_851)::[])
in (_165_853, _165_852)))
in (FStar_Absyn_Syntax.mk_Exp_app _165_854 None p))
in (FStar_Absyn_Util.b2t _165_855))
in (x, _165_856))
in (FStar_Absyn_Syntax.mk_Typ_refine _165_857 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _165_858))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _165_859))))
end)
in (let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _63_2323 -> (match (_63_2323) with
| (x, _63_2322) -> begin
(x, Some (imp_tag))
end))))
in (let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (let subst = (let _165_867 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(let _63_2334 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_63_2334) with
| (field_name, _63_2333) -> begin
(let proj = (let _165_864 = (let _165_863 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in (_165_863, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _165_864 None p))
in (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, proj)))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(let _63_2341 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_63_2341) with
| (field_name, _63_2340) -> begin
(let proj = (let _165_866 = (let _165_865 = (FStar_Absyn_Util.fvar None field_name p)
in (_165_865, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _165_866 None p))
in (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, proj)))::[])
end))
end))))
in (FStar_All.pipe_right _165_867 FStar_List.flatten))
in (let ntps = (FStar_List.length tps)
in (let all_params = (let _165_869 = (FStar_All.pipe_right tps (FStar_List.map (fun _63_2348 -> (match (_63_2348) with
| (b, _63_2347) -> begin
(b, Some (imp_tag))
end))))
in (FStar_List.append _165_869 formals))
in (let _165_897 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(let _63_2357 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_63_2357) with
| (field_name, _63_2356) -> begin
(let kk = (let _165_873 = (let _165_872 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (binders, _165_872))
in (FStar_Absyn_Syntax.mk_Kind_arrow _165_873 p))
in (FStar_Absyn_Syntax.Sig_tycon ((field_name, [], kk, [], [], (FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inl (a.FStar_Absyn_Syntax.v))))::[], (FStar_Ident.range_of_lid field_name))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(let _63_2364 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_63_2364) with
| (field_name, _63_2363) -> begin
(let t = (let _165_876 = (let _165_875 = (let _165_874 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _165_874 p))
in (binders, _165_875))
in (FStar_Absyn_Syntax.mk_Typ_fun _165_876 None p))
in (let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inr (x.FStar_Absyn_Syntax.v))))::[]))
in (let impl = if (((let _165_879 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _165_879)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _165_881 = (let _165_880 = (FStar_Parser_DesugarEnv.current_module env)
in _165_880.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _165_881))) then begin
[]
end else begin
(let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (let as_imp = (fun _63_14 -> (match (_63_14) with
| Some (FStar_Absyn_Syntax.Implicit (_63_2372)) -> begin
true
end
| _63_2376 -> begin
false
end))
in (let arg_pats = (let _165_894 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_63_2381), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _165_889 = (let _165_888 = (let _165_887 = (let _165_886 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_165_886))
in (pos _165_887))
in (_165_888, (as_imp imp)))
in (_165_889)::[])
end
end
| (FStar_Util.Inr (_63_2386), imp) -> begin
if ((i + ntps) = j) then begin
(((pos (FStar_Absyn_Syntax.Pat_var (projection))), (as_imp imp)))::[]
end else begin
(let _165_893 = (let _165_892 = (let _165_891 = (let _165_890 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_165_890))
in (pos _165_891))
in (_165_892, (as_imp imp)))
in (_165_893)::[])
end
end))))
in (FStar_All.pipe_right _165_894 FStar_List.flatten))
in (let pat = (let _165_896 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv lid), Some (fvq), arg_pats))) pos)
in (let _165_895 = (FStar_Absyn_Util.bvar_to_exp projection)
in (_165_896, None, _165_895)))
in (let body = (FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (let imp = (FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None (FStar_Ident.range_of_lid field_name))
in (let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end
in (FStar_Absyn_Syntax.Sig_val_decl ((field_name, t, quals, (FStar_Ident.range_of_lid field_name))))::impl))))
end))
end))))
in (FStar_All.pipe_right _165_897 FStar_List.flatten))))))))))))))
end))

# 1288 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _63_17 -> (match (_63_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _63_2403, _63_2405) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_15 -> (match (_63_15) with
| FStar_Absyn_Syntax.RecordConstructor (_63_2410) -> begin
true
end
| _63_2413 -> begin
false
end)))) then begin
false
end else begin
(let _63_2419 = tycon
in (match (_63_2419) with
| (l, _63_2416, _63_2418) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _63_2423 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(let cod = (FStar_Absyn_Util.comp_result cod)
in (let qual = (match ((FStar_Util.find_map quals (fun _63_16 -> (match (_63_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((lid, fns)))
end
| _63_2434 -> begin
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
| _63_2440 -> begin
[]
end))
end
| _63_2442 -> begin
[]
end))

# 1311 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (let tycon_id = (fun _63_18 -> (match (_63_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _165_917 = (let _165_916 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_165_916))
in (FStar_Parser_AST.mk_term _165_917 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (let apply_binders = (fun t binders -> (let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _63_2507 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _165_930 = (let _165_929 = (let _165_928 = (binder_to_term b)
in (out, _165_928, (imp_of_aqual b)))
in FStar_Parser_AST.App (_165_929))
in (FStar_Parser_AST.mk_term _165_930 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (let tycon_record_as_variant = (fun _63_19 -> (match (_63_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (let mfields = (FStar_List.map (fun _63_2520 -> (match (_63_2520) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Absyn_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (let result = (let _165_936 = (let _165_935 = (let _165_934 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_165_934))
in (FStar_Parser_AST.mk_term _165_935 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _165_936 parms))
in (let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _165_938 = (FStar_All.pipe_right fields (FStar_List.map (fun _63_2527 -> (match (_63_2527) with
| (x, _63_2526) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _165_938))))))
end
| _63_2529 -> begin
(FStar_All.failwith "impossible")
end))
in (let desugar_abstract_tc = (fun quals _env mutuals _63_20 -> (match (_63_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(let _63_2543 = (typars_of_binders _env binders)
in (match (_63_2543) with
| (_env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (let tconstr = (let _165_949 = (let _165_948 = (let _165_947 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_165_947))
in (FStar_Parser_AST.mk_term _165_948 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _165_949 binders))
in (let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (let se = FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, _env2, se, tconstr)))))))
end))
end
| _63_2554 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (let push_tparam = (fun env _63_21 -> (match (_63_21) with
| (FStar_Util.Inr (x), _63_2561) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _63_2566) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_63_2570)::[] -> begin
(let tc = (FStar_List.hd tcs)
in (let _63_2581 = (desugar_abstract_tc quals env [] tc)
in (match (_63_2581) with
| (_63_2575, _63_2577, se, _63_2580) -> begin
(let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(let _63_2592 = (typars_of_binders env binders)
in (match (_63_2592) with
| (env', typars) -> begin
(let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _63_22 -> (match (_63_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _63_2597 -> begin
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
in (let t0 = t
in (let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_23 -> (match (_63_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _63_2605 -> begin
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
in (let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Effect)) then begin
(let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let _165_961 = (let _165_960 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _165_959 = (FStar_All.pipe_right quals (FStar_List.filter (fun _63_24 -> (match (_63_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _63_2611 -> begin
true
end))))
in (_165_960, typars, c, _165_959, rng)))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_165_961)))
end else begin
(let t = (desugar_typ env' t)
in (let _165_963 = (let _165_962 = (FStar_Parser_DesugarEnv.qualify env id)
in (_165_962, typars, k, t, quals, rng))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_165_963)))
end
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_63_2616)::[] -> begin
(let trec = (FStar_List.hd tcs)
in (let _63_2622 = (tycon_record_as_variant trec)
in (match (_63_2622) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _63_2626::_63_2624 -> begin
(let env0 = env
in (let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (let rec collect_tcs = (fun quals et tc -> (let _63_2637 = et
in (match (_63_2637) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_63_2639) -> begin
(let trec = tc
in (let _63_2644 = (tycon_record_as_variant trec)
in (match (_63_2644) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(let _63_2656 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_63_2656) with
| (env, _63_2653, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(let _63_2668 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_63_2668) with
| (env, _63_2665, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _63_2670 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (let _63_2673 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_63_2673) with
| (env, tcs) -> begin
(let tcs = (FStar_List.rev tcs)
in (let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _63_26 -> (match (_63_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _63_2680, _63_2682, _63_2684, _63_2686), t, quals) -> begin
(let env_tps = (push_tparams env tpars)
in (let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _63_2700, tags, _63_2703), constrs, tconstr, quals) -> begin
(let tycon = (tname, tpars, k)
in (let env_tps = (push_tparams env tpars)
in (let _63_2734 = (let _165_978 = (FStar_All.pipe_right constrs (FStar_List.map (fun _63_2716 -> (match (_63_2716) with
| (id, topt, of_notation) -> begin
(let t = if of_notation then begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[], tconstr))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
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
in (let t = (let _165_973 = (close env_tps t)
in (desugar_typ (FStar_Parser_DesugarEnv.default_total env_tps) _165_973))
in (let name = (FStar_Parser_DesugarEnv.qualify env id)
in (let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _63_25 -> (match (_63_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _63_2730 -> begin
[]
end))))
in (let _165_977 = (let _165_976 = (let _165_975 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in (name, _165_975, tycon, quals, mutuals, rng))
in FStar_Absyn_Syntax.Sig_datacon (_165_976))
in (name, _165_977))))))
end))))
in (FStar_All.pipe_left FStar_List.split _165_978))
in (match (_63_2734) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _63_2736 -> begin
(FStar_All.failwith "impossible")
end))))
in (let bundle = (let _165_980 = (let _165_979 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _165_979, rng))
in FStar_Absyn_Syntax.Sig_bundle (_165_980))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _63_27 -> (match (_63_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _63_2746, constrs, quals, _63_2750) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _63_2754 -> begin
[]
end))))
in (let ops = (FStar_List.append discs data_ops)
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end)))))))))))

# 1452 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let desugar_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((FStar_Absyn_Syntax.btvar, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env binders -> (let _63_2785 = (FStar_List.fold_left (fun _63_2763 b -> (match (_63_2763) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(let _63_2772 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_63_2772) with
| (env, a) -> begin
(env, ((FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k)))::binders)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(let _63_2780 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_63_2780) with
| (env, x) -> begin
(env, ((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::binders)
end))
end
| _63_2782 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_63_2785) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1466 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Absyn_Syntax.qualifier = (fun r _63_28 -> (match (_63_28) with
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
| FStar_Parser_AST.TotalEffect -> begin
FStar_Absyn_Syntax.TotalEffect
end
| FStar_Parser_AST.DefaultEffect -> begin
FStar_Absyn_Syntax.DefaultEffect (None)
end
| FStar_Parser_AST.Effect -> begin
FStar_Absyn_Syntax.Effect
end
| (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Irreducible) | (FStar_Parser_AST.New) | (FStar_Parser_AST.Unfoldable) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("This qualifier is supported only with the --universes option", r))))
end))

# 1480 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _63_29 -> (match (_63_29) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Absyn_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Absyn_Syntax.ResetOptions
end))

# 1484 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let trans_quals : FStar_Range.range  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun r -> (FStar_List.map (trans_qual r)))

# 1486 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env d -> (let trans_quals = (trans_quals d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(let se = FStar_Absyn_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.TopLevelModule (_63_2812) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _165_1005 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in (_165_1005, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _165_1006 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _165_1006 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _165_1008 = (let _165_1007 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _165_1007))
in _165_1008.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _63_2832) -> begin
(let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _63_2839 -> begin
(FStar_All.failwith "impossible")
end))))
in (let quals = (match (quals) with
| _63_2844::_63_2842 -> begin
(trans_quals quals)
end
| _63_2847 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _63_30 -> (match (_63_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_63_2856); FStar_Absyn_Syntax.lbtyp = _63_2854; FStar_Absyn_Syntax.lbeff = _63_2852; FStar_Absyn_Syntax.lbdef = _63_2850} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _63_2864; FStar_Absyn_Syntax.lbeff = _63_2862; FStar_Absyn_Syntax.lbdef = _63_2860} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (let s = FStar_Absyn_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _63_2872 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(let e = (desugar_exp env t)
in (let se = FStar_Absyn_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(let f = (desugar_formula env t)
in (let _165_1014 = (let _165_1013 = (let _165_1012 = (let _165_1011 = (FStar_Parser_DesugarEnv.qualify env id)
in (_165_1011, f, (FStar_Absyn_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_assume (_165_1012))
in (_165_1013)::[])
in (env, _165_1014)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(let t = (let _165_1015 = (close_fun env t)
in (desugar_typ env _165_1015))
in (let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _165_1016 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_165_1016)
end else begin
(trans_quals quals)
end
in (let se = (let _165_1018 = (let _165_1017 = (FStar_Parser_DesugarEnv.qualify env id)
in (_165_1017, t, quals, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_val_decl (_165_1018))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(let t = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (let l = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(let t = (desugar_typ env term)
in (let t = (let _165_1021 = (let _165_1020 = (let _165_1019 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _165_1019))
in (((FStar_Absyn_Syntax.null_v_binder t))::[], _165_1020))
in (FStar_Absyn_Syntax.mk_Typ_fun _165_1021 None d.FStar_Parser_AST.drange))
in (let l = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (let data_ops = (mk_data_projectors env se)
in (let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(let _63_2925 = (desugar_binders env binders)
in (match (_63_2925) with
| (env_k, binders) -> begin
(let k = (desugar_kind env_k k)
in (let name = (FStar_Parser_DesugarEnv.qualify env id)
in (let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((name, binders, k, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(let env0 = env
in (let _63_2941 = (desugar_binders env eff_binders)
in (match (_63_2941) with
| (env, binders) -> begin
(let defn = (desugar_typ env defn)
in (let _63_2945 = (FStar_Absyn_Util.head_and_args defn)
in (match (_63_2945) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _165_1026 = (let _165_1025 = (let _165_1024 = (let _165_1023 = (let _165_1022 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat "Effect " _165_1022))
in (Prims.strcat _165_1023 " not found"))
in (_165_1024, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_165_1025))
in (Prims.raise _165_1026))
end
| Some (ed) -> begin
(let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (let sub = (FStar_Absyn_Util.subst_typ subst)
in (let ed = (let _165_1044 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _165_1043 = (trans_quals quals)
in (let _165_1042 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _165_1041 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _165_1040 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _165_1039 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _165_1038 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _165_1037 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _165_1036 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _165_1035 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _165_1034 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _165_1033 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _165_1032 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _165_1031 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _165_1030 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _165_1029 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _165_1028 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _165_1044; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _165_1043; FStar_Absyn_Syntax.signature = _165_1042; FStar_Absyn_Syntax.ret = _165_1041; FStar_Absyn_Syntax.bind_wp = _165_1040; FStar_Absyn_Syntax.bind_wlp = _165_1039; FStar_Absyn_Syntax.if_then_else = _165_1038; FStar_Absyn_Syntax.ite_wp = _165_1037; FStar_Absyn_Syntax.ite_wlp = _165_1036; FStar_Absyn_Syntax.wp_binop = _165_1035; FStar_Absyn_Syntax.wp_as_type = _165_1034; FStar_Absyn_Syntax.close_wp = _165_1033; FStar_Absyn_Syntax.close_wp_t = _165_1032; FStar_Absyn_Syntax.assert_p = _165_1031; FStar_Absyn_Syntax.assume_p = _165_1030; FStar_Absyn_Syntax.null_wp = _165_1029; FStar_Absyn_Syntax.trivial = _165_1028})))))))))))))))))
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _63_2957 -> begin
(let _165_1048 = (let _165_1047 = (let _165_1046 = (let _165_1045 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _165_1045 " is not an effect"))
in (_165_1046, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_165_1047))
in (Prims.raise _165_1048))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(let env0 = env
in (let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (let _63_2971 = (desugar_binders env eff_binders)
in (match (_63_2971) with
| (env, binders) -> begin
(let eff_k = (desugar_kind env eff_kind)
in (let _63_2982 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _63_2975 decl -> (match (_63_2975) with
| (env, out) -> begin
(let _63_2979 = (desugar_decl env decl)
in (match (_63_2979) with
| (env, ses) -> begin
(let _165_1052 = (let _165_1051 = (FStar_List.hd ses)
in (_165_1051)::out)
in (env, _165_1052))
end))
end)) (env, [])))
in (match (_63_2982) with
| (env, decls) -> begin
(let decls = (FStar_List.rev decls)
in (let lookup = (fun s -> (match ((let _165_1055 = (FStar_Parser_DesugarEnv.qualify env (FStar_Absyn_Syntax.mk_ident (s, d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _165_1055))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat (Prims.strcat "Monad " eff_name.FStar_Ident.idText) " expects definition of ") s), d.FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (let ed = (let _165_1071 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _165_1070 = (trans_quals quals)
in (let _165_1069 = (lookup "return")
in (let _165_1068 = (lookup "bind_wp")
in (let _165_1067 = (lookup "bind_wlp")
in (let _165_1066 = (lookup "if_then_else")
in (let _165_1065 = (lookup "ite_wp")
in (let _165_1064 = (lookup "ite_wlp")
in (let _165_1063 = (lookup "wp_binop")
in (let _165_1062 = (lookup "wp_as_type")
in (let _165_1061 = (lookup "close_wp")
in (let _165_1060 = (lookup "close_wp_t")
in (let _165_1059 = (lookup "assert_p")
in (let _165_1058 = (lookup "assume_p")
in (let _165_1057 = (lookup "null_wp")
in (let _165_1056 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _165_1071; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _165_1070; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _165_1069; FStar_Absyn_Syntax.bind_wp = _165_1068; FStar_Absyn_Syntax.bind_wlp = _165_1067; FStar_Absyn_Syntax.if_then_else = _165_1066; FStar_Absyn_Syntax.ite_wp = _165_1065; FStar_Absyn_Syntax.ite_wlp = _165_1064; FStar_Absyn_Syntax.wp_binop = _165_1063; FStar_Absyn_Syntax.wp_as_type = _165_1062; FStar_Absyn_Syntax.close_wp = _165_1061; FStar_Absyn_Syntax.close_wp_t = _165_1060; FStar_Absyn_Syntax.assert_p = _165_1059; FStar_Absyn_Syntax.assume_p = _165_1058; FStar_Absyn_Syntax.null_wp = _165_1057; FStar_Absyn_Syntax.trivial = _165_1056}))))))))))))))))
in (let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _165_1078 = (let _165_1077 = (let _165_1076 = (let _165_1075 = (let _165_1074 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Effect name " _165_1074))
in (Prims.strcat _165_1075 " not found"))
in (_165_1076, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_165_1077))
in (Prims.raise _165_1078))
end
| Some (l) -> begin
l
end))
in (let src = (lookup l.FStar_Parser_AST.msource)
in (let dst = (lookup l.FStar_Parser_AST.mdest)
in (let lift = (desugar_typ env l.FStar_Parser_AST.lift_op)
in (let se = FStar_Absyn_Syntax.Sig_sub_effect (({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))

# 1655 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelt Prims.list) = (fun env decls -> (FStar_List.fold_left (fun _63_3007 d -> (match (_63_3007) with
| (env, sigelts) -> begin
(let _63_3011 = (desugar_decl env d)
in (match (_63_3011) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1660 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]

# 1667 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (let open_ns = (fun mname d -> (let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _165_1097 = (let _165_1096 = (let _165_1095 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_165_1095))
in (FStar_Parser_AST.mk_decl _165_1096 (FStar_Absyn_Syntax.range_of_lid mname)))
in (_165_1097)::d)
end else begin
d
end
in d))
in (let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (let _63_3038 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _165_1099 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _165_1098 = (open_ns mname decls)
in (_165_1099, mname, _165_1098, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _165_1101 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _165_1100 = (open_ns mname decls)
in (_165_1101, mname, _165_1100, false)))
end)
in (match (_63_3038) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(let _63_3041 = (desugar_decls env decls)
in (match (_63_3041) with
| (env, sigelts) -> begin
(let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul, pop_when_done))
end))
end)))))

# 1691 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let desugar_partial_modul : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun curmod env m -> (let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _165_1111 = (let _165_1110 = (let _165_1109 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_Util.for_some (fun m -> (m = mname.FStar_Ident.str)) _165_1109))
in (mname, decls, _165_1110))
in FStar_Parser_AST.Interface (_165_1111))
end
| FStar_Parser_AST.Interface (mname, _63_3053, _63_3055) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (let _63_3063 = (desugar_modul_common curmod env m)
in (match (_63_3063) with
| (x, y, _63_3062) -> begin
(x, y)
end))))

# 1702 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (let _63_3069 = (desugar_modul_common None env m)
in (match (_63_3069) with
| (env, modul, pop_when_done) -> begin
(let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (let _63_3071 = if (FStar_Options.should_dump modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _165_1116 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _165_1116))
end else begin
()
end
in (let _165_1117 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in (_165_1117, modul))))
end)))

# 1708 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (let _63_3084 = (FStar_List.fold_left (fun _63_3077 m -> (match (_63_3077) with
| (env, mods) -> begin
(let _63_3081 = (desugar_modul env m)
in (match (_63_3081) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_63_3084) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1714 "D:\\workspace\\universes\\FStar\\src\\parser\\desugar.fs"

let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (let _63_3089 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_63_3089) with
| (en, pop_when_done) -> begin
(let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (let _63_3090 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _63_3090.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _63_3090.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _63_3090.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _63_3090.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _63_3090.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _63_3090.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _63_3090.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _63_3090.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _63_3090.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _63_3090.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _63_3090.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))





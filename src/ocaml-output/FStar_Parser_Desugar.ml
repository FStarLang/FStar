
open Prims
# 35 "FStar.Parser.Desugar.fst"
let imp_tag : FStar_Absyn_Syntax.arg_qualifier = FStar_Absyn_Syntax.Implicit (false)

# 36 "FStar.Parser.Desugar.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _50_1 -> (match (_50_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (imp_tag)
end
| _50_35 -> begin
None
end))

# 40 "FStar.Parser.Desugar.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 42 "FStar.Parser.Desugar.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (imp_tag))
end
| _50_42 -> begin
(t, None)
end))

# 47 "FStar.Parser.Desugar.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_50_46) -> begin
true
end
| _50_49 -> begin
false
end)))))

# 52 "FStar.Parser.Desugar.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _50_54 -> begin
t
end))

# 55 "FStar.Parser.Desugar.fst"
let rec unlabel : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _50_60, _50_62) -> begin
(unlabel t)
end
| _50_66 -> begin
t
end))

# 60 "FStar.Parser.Desugar.fst"
let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _129_17 = (let _129_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_129_16))
in (FStar_Parser_AST.mk_term _129_17 r FStar_Parser_AST.Kind)))

# 63 "FStar.Parser.Desugar.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 64 "FStar.Parser.Desugar.fst"
let name_of_char = (fun _50_2 -> (match (_50_2) with
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
| _50_89 -> begin
"UNKNOWN"
end))
in (
# 83 "FStar.Parser.Desugar.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _129_28 = (let _129_26 = (FStar_Util.char_at s i)
in (name_of_char _129_26))
in (let _129_27 = (aux (i + 1))
in (_129_28)::_129_27))
end)
in (let _129_30 = (let _129_29 = (aux 0)
in (FStar_String.concat "_" _129_29))
in (Prims.strcat "op_" _129_30)))))

# 89 "FStar.Parser.Desugar.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _129_40 = (let _129_39 = (let _129_38 = (let _129_37 = (compile_op n s)
in (_129_37, r))
in (FStar_Absyn_Syntax.mk_ident _129_38))
in (_129_39)::[])
in (FStar_All.pipe_right _129_40 FStar_Absyn_Syntax.lid_of_ids)))

# 91 "FStar.Parser.Desugar.fst"
let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 92 "FStar.Parser.Desugar.fst"
let r = (fun l -> (let _129_51 = (FStar_Ident.set_lid_range l rng)
in Some (_129_51)))
in (
# 93 "FStar.Parser.Desugar.fst"
let fallback = (fun _50_103 -> (match (()) with
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
| _50_125 -> begin
None
end)
end))
in (match ((let _129_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _129_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_136); FStar_Absyn_Syntax.tk = _50_133; FStar_Absyn_Syntax.pos = _50_131; FStar_Absyn_Syntax.fvs = _50_129; FStar_Absyn_Syntax.uvs = _50_127}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _50_142 -> begin
(fallback ())
end))))

# 121 "FStar.Parser.Desugar.fst"
let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 122 "FStar.Parser.Desugar.fst"
let r = (fun l -> (let _129_65 = (FStar_Ident.set_lid_range l rng)
in Some (_129_65)))
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
(match ((let _129_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _129_66))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _50_165; FStar_Absyn_Syntax.pos = _50_163; FStar_Absyn_Syntax.fvs = _50_161; FStar_Absyn_Syntax.uvs = _50_159}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _50_171 -> begin
None
end)
end)))

# 138 "FStar.Parser.Desugar.fst"
let rec is_type : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _129_73 = (unparen t)
in _129_73.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_50_176) -> begin
true
end
| FStar_Parser_AST.Op ("*", hd::_50_180) -> begin
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
| _50_231 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_50_254) -> begin
true
end
| _50_257 -> begin
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
| FStar_Parser_AST.Product (_50_298, t) -> begin
(not ((is_kind env t)))
end
| FStar_Parser_AST.If (t, t1, t2) -> begin
(((is_type env t) || (is_type env t1)) || (is_type env t2))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(
# 179 "FStar.Parser.Desugar.fst"
let rec aux = (fun env pats -> (match (pats) with
| [] -> begin
(is_type env t)
end
| hd::pats -> begin
(match (hd.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatVar (_)) -> begin
(aux env pats)
end
| FStar_Parser_AST.PatTvar (id, _50_324) -> begin
(
# 186 "FStar.Parser.Desugar.fst"
let _50_330 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_50_330) with
| (env, _50_329) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(
# 189 "FStar.Parser.Desugar.fst"
let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _129_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _129_78 Prims.fst))
end
| _50_345 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _50_348 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_50_353); FStar_Parser_AST.prange = _50_351}, _50_357)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_50_369); FStar_Parser_AST.prange = _50_367}, _50_373); FStar_Parser_AST.prange = _50_365}, _50_378)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_50_388); FStar_Parser_AST.prange = _50_386}, _50_392)::[], t) -> begin
(is_type env t)
end
| _50_399 -> begin
false
end)
end)
and is_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _129_81 = (unparen t)
in _129_81.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _50_408; FStar_Ident.ident = _50_406; FStar_Ident.nsstr = _50_404; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_50_412, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _50_425 -> begin
false
end)
end)

# 215 "FStar.Parser.Desugar.fst"
let rec is_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  Prims.bool = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_50_429) -> begin
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
| FStar_Parser_AST.Variable (_50_444) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.FStar_Parser_AST.brange))))
end
| FStar_Parser_AST.TVariable (_50_447) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_50_450) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)

# 230 "FStar.Parser.Desugar.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _129_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _129_92)))

# 234 "FStar.Parser.Desugar.fst"
let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_50_466) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 237 "FStar.Parser.Desugar.fst"
let _50_473 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_50_473) with
| (env, _50_472) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_50_475, term) -> begin
(let _129_99 = (free_type_vars env term)
in (env, _129_99))
end
| FStar_Parser_AST.TAnnotated (id, _50_481) -> begin
(
# 242 "FStar.Parser.Desugar.fst"
let _50_487 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_50_487) with
| (env, _50_486) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _129_100 = (free_type_vars env t)
in (env, _129_100))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _129_103 = (unparen t)
in _129_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _50_496 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_50_532, ts) -> begin
(FStar_List.collect (fun _50_539 -> (match (_50_539) with
| (t, _50_538) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_50_541, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _50_548) -> begin
(let _129_106 = (free_type_vars env t1)
in (let _129_105 = (free_type_vars env t2)
in (FStar_List.append _129_106 _129_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 271 "FStar.Parser.Desugar.fst"
let _50_557 = (free_type_vars_b env b)
in (match (_50_557) with
| (env, f) -> begin
(let _129_107 = (free_type_vars env t)
in (FStar_List.append f _129_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 276 "FStar.Parser.Desugar.fst"
let _50_573 = (FStar_List.fold_left (fun _50_566 binder -> (match (_50_566) with
| (env, free) -> begin
(
# 277 "FStar.Parser.Desugar.fst"
let _50_570 = (free_type_vars_b env binder)
in (match (_50_570) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_50_573) with
| (env, free) -> begin
(let _129_110 = (free_type_vars env body)
in (FStar_List.append free _129_110))
end))
end
| FStar_Parser_AST.Project (t, _50_576) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 294 "FStar.Parser.Desugar.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 295 "FStar.Parser.Desugar.fst"
let rec aux = (fun args t -> (match ((let _129_117 = (unparen t)
in _129_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _50_620 -> begin
(t, args)
end))
in (aux [] t)))

# 301 "FStar.Parser.Desugar.fst"
let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 302 "FStar.Parser.Desugar.fst"
let ftv = (let _129_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _129_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 305 "FStar.Parser.Desugar.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _129_126 = (let _129_125 = (let _129_124 = (kind_star x.FStar_Ident.idRange)
in (x, _129_124))
in FStar_Parser_AST.TAnnotated (_129_125))
in (FStar_Parser_AST.mk_binder _129_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 306 "FStar.Parser.Desugar.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 309 "FStar.Parser.Desugar.fst"
let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 310 "FStar.Parser.Desugar.fst"
let ftv = (let _129_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _129_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 313 "FStar.Parser.Desugar.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _129_135 = (let _129_134 = (let _129_133 = (kind_star x.FStar_Ident.idRange)
in (x, _129_133))
in FStar_Parser_AST.TAnnotated (_129_134))
in (FStar_Parser_AST.mk_binder _129_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 314 "FStar.Parser.Desugar.fst"
let t = (match ((let _129_136 = (unlabel t)
in _129_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_50_633) -> begin
t
end
| _50_636 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 317 "FStar.Parser.Desugar.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 320 "FStar.Parser.Desugar.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _50_646 -> begin
(bs, t)
end))

# 324 "FStar.Parser.Desugar.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _50_650) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_50_656); FStar_Parser_AST.prange = _50_654}, _50_660) -> begin
true
end
| _50_664 -> begin
false
end))

# 329 "FStar.Parser.Desugar.fst"
let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 331 "FStar.Parser.Desugar.fst"
let _50_676 = (destruct_app_pattern env is_top_level p)
in (match (_50_676) with
| (name, args, _50_675) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _50_681); FStar_Parser_AST.prange = _50_678}, args) when is_top_level -> begin
(let _129_150 = (let _129_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_129_149))
in (_129_150, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _50_692); FStar_Parser_AST.prange = _50_689}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _50_700 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 340 "FStar.Parser.Desugar.fst"
type bnd =
| TBinder of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual)
| VBinder of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)

# 341 "FStar.Parser.Desugar.fst"
let is_TBinder = (fun _discr_ -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 342 "FStar.Parser.Desugar.fst"
let is_VBinder = (fun _discr_ -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 343 "FStar.Parser.Desugar.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 341 "FStar.Parser.Desugar.fst"
let ___TBinder____0 : bnd  ->  (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual) = (fun projectee -> (match (projectee) with
| TBinder (_50_703) -> begin
_50_703
end))

# 342 "FStar.Parser.Desugar.fst"
let ___VBinder____0 : bnd  ->  (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual) = (fun projectee -> (match (projectee) with
| VBinder (_50_706) -> begin
_50_706
end))

# 343 "FStar.Parser.Desugar.fst"
let ___LetBinder____0 : bnd  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| LetBinder (_50_709) -> begin
_50_709
end))

# 344 "FStar.Parser.Desugar.fst"
let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _50_3 -> (match (_50_3) with
| TBinder (a, k, aq) -> begin
(FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder (x, t, aq) -> begin
(FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _50_722 -> begin
(FStar_All.failwith "Impossible")
end))

# 348 "FStar.Parser.Desugar.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _50_4 -> (match (_50_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _50_729 -> begin
None
end))

# 352 "FStar.Parser.Desugar.fst"
let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either  ->  (FStar_Absyn_Syntax.binder * FStar_Parser_DesugarEnv.env) = (fun env imp _50_5 -> (match (_50_5) with
| FStar_Util.Inl (None, k) -> begin
(let _129_203 = (FStar_Absyn_Syntax.null_t_binder k)
in (_129_203, env))
end
| FStar_Util.Inr (None, t) -> begin
(let _129_204 = (FStar_Absyn_Syntax.null_v_binder t)
in (_129_204, env))
end
| FStar_Util.Inl (Some (a), k) -> begin
(
# 356 "FStar.Parser.Desugar.fst"
let _50_748 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_50_748) with
| (env, a) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual imp)), env)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 359 "FStar.Parser.Desugar.fst"
let _50_756 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_50_756) with
| (env, x) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual imp)), env)
end))
end))

# 362 "FStar.Parser.Desugar.fst"
type env_t =
FStar_Parser_DesugarEnv.env

# 363 "FStar.Parser.Desugar.fst"
type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list

# 365 "FStar.Parser.Desugar.fst"
let label_conjuncts : Prims.string  ->  Prims.bool  ->  Prims.string Prims.option  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun tag polarity label_opt f -> (
# 366 "FStar.Parser.Desugar.fst"
let label = (fun f -> (
# 367 "FStar.Parser.Desugar.fst"
let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _50_766 -> begin
(let _129_215 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _129_215))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled ((f, msg, polarity))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (
# 373 "FStar.Parser.Desugar.fst"
let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _129_219 = (let _129_218 = (aux g)
in FStar_Parser_AST.Paren (_129_218))
in (FStar_Parser_AST.mk_term _129_219 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", f1::f2::[]) -> begin
(let _129_225 = (let _129_224 = (let _129_223 = (let _129_222 = (aux f1)
in (let _129_221 = (let _129_220 = (aux f2)
in (_129_220)::[])
in (_129_222)::_129_221))
in ("/\\", _129_223))
in FStar_Parser_AST.Op (_129_224))
in (FStar_Parser_AST.mk_term _129_225 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _129_229 = (let _129_228 = (let _129_227 = (aux f2)
in (let _129_226 = (aux f3)
in (f1, _129_227, _129_226)))
in FStar_Parser_AST.If (_129_228))
in (FStar_Parser_AST.mk_term _129_229 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _129_232 = (let _129_231 = (let _129_230 = (aux g)
in (binders, _129_230))
in FStar_Parser_AST.Abs (_129_231))
in (FStar_Parser_AST.mk_term _129_232 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _50_788 -> begin
(label f)
end))
in (aux f))))

# 391 "FStar.Parser.Desugar.fst"
let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _50_792 -> (match (_50_792) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))

# 393 "FStar.Parser.Desugar.fst"
let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (
# 394 "FStar.Parser.Desugar.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _50_6 -> (match (_50_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _50_803 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
(l, e, y)
end
| _50_808 -> begin
(
# 398 "FStar.Parser.Desugar.fst"
let _50_811 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_50_811) with
| (e, x) -> begin
((FStar_Util.Inr (x))::l, e, x)
end))
end))
in (
# 400 "FStar.Parser.Desugar.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _50_7 -> (match (_50_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _50_820 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
(l, e, b)
end
| _50_825 -> begin
(
# 404 "FStar.Parser.Desugar.fst"
let _50_828 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_50_828) with
| (e, a) -> begin
((FStar_Util.Inl (a))::l, e, a)
end))
end))
in (
# 406 "FStar.Parser.Desugar.fst"
let rec aux = (fun loc env p -> (
# 407 "FStar.Parser.Desugar.fst"
let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p.FStar_Parser_AST.prange))
in (
# 408 "FStar.Parser.Desugar.fst"
let pos_r = (fun r q -> (FStar_Absyn_Syntax.withinfo q None r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(
# 412 "FStar.Parser.Desugar.fst"
let _50_850 = (aux loc env p)
in (match (_50_850) with
| (loc, env, var, p, _50_849) -> begin
(
# 413 "FStar.Parser.Desugar.fst"
let _50_867 = (FStar_List.fold_left (fun _50_854 p -> (match (_50_854) with
| (loc, env, ps) -> begin
(
# 414 "FStar.Parser.Desugar.fst"
let _50_863 = (aux loc env p)
in (match (_50_863) with
| (loc, env, _50_859, p, _50_862) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_50_867) with
| (loc, env, ps) -> begin
(
# 416 "FStar.Parser.Desugar.fst"
let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (
# 417 "FStar.Parser.Desugar.fst"
let _50_869 = (let _129_304 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _129_304))
in (loc, env, var, pat, false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 421 "FStar.Parser.Desugar.fst"
let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_50_876) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(
# 424 "FStar.Parser.Desugar.fst"
let _50_882 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar ((x, imp)); FStar_Parser_AST.prange = _50_882.FStar_Parser_AST.prange})
end
| _50_885 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end)
end else begin
p
end
in (
# 427 "FStar.Parser.Desugar.fst"
let _50_892 = (aux loc env p)
in (match (_50_892) with
| (loc, env', binder, p, imp) -> begin
(
# 428 "FStar.Parser.Desugar.fst"
let binder = (match (binder) with
| LetBinder (_50_894) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _50_898, aq) -> begin
(let _129_306 = (let _129_305 = (desugar_kind env t)
in (x, _129_305, aq))
in TBinder (_129_306))
end
| VBinder (x, _50_904, aq) -> begin
(
# 432 "FStar.Parser.Desugar.fst"
let t = (close_fun env t)
in (let _129_308 = (let _129_307 = (desugar_typ env t)
in (x, _129_307, aq))
in VBinder (_129_308)))
end)
in (loc, env', binder, p, imp))
end)))
end
| FStar_Parser_AST.PatTvar (a, imp) -> begin
(
# 437 "FStar.Parser.Desugar.fst"
let aq = if imp then begin
Some (imp_tag)
end else begin
None
end
in if (a.FStar_Ident.idText = "\'_") then begin
(
# 439 "FStar.Parser.Desugar.fst"
let a = (FStar_All.pipe_left FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _129_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, FStar_Absyn_Syntax.kun, aq)), _129_309, imp)))
end else begin
(
# 441 "FStar.Parser.Desugar.fst"
let _50_919 = (resolvea loc env a)
in (match (_50_919) with
| (loc, env, abvd) -> begin
(let _129_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, FStar_Absyn_Syntax.kun, aq)), _129_310, imp))
end))
end)
end
| FStar_Parser_AST.PatWild -> begin
(
# 445 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (
# 446 "FStar.Parser.Desugar.fst"
let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _129_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _129_311, false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 450 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _129_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _129_312, false)))
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(
# 454 "FStar.Parser.Desugar.fst"
let aq = if imp then begin
Some (imp_tag)
end else begin
None
end
in (
# 455 "FStar.Parser.Desugar.fst"
let _50_934 = (resolvex loc env x)
in (match (_50_934) with
| (loc, env, xbvd) -> begin
(let _129_313 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, FStar_Absyn_Syntax.tun, aq)), _129_313, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 459 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (
# 460 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _129_314 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _129_314, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _50_940}, args) -> begin
(
# 464 "FStar.Parser.Desugar.fst"
let _50_962 = (FStar_List.fold_right (fun arg _50_951 -> (match (_50_951) with
| (loc, env, args) -> begin
(
# 465 "FStar.Parser.Desugar.fst"
let _50_958 = (aux loc env arg)
in (match (_50_958) with
| (loc, env, _50_955, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_50_962) with
| (loc, env, args) -> begin
(
# 467 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (
# 468 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _129_317 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _129_317, false))))
end))
end
| FStar_Parser_AST.PatApp (_50_966) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 474 "FStar.Parser.Desugar.fst"
let _50_986 = (FStar_List.fold_right (fun pat _50_974 -> (match (_50_974) with
| (loc, env, pats) -> begin
(
# 475 "FStar.Parser.Desugar.fst"
let _50_982 = (aux loc env pat)
in (match (_50_982) with
| (loc, env, _50_978, pat, _50_981) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_50_986) with
| (loc, env, pats) -> begin
(
# 477 "FStar.Parser.Desugar.fst"
let pat = (let _129_324 = (let _129_323 = (let _129_322 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _129_322))
in (FStar_All.pipe_left _129_323 (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid), Some (FStar_Absyn_Syntax.Data_ctor), [])))))
in (FStar_List.fold_right (fun hd tl -> (
# 478 "FStar.Parser.Desugar.fst"
let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid), Some (FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[])))))) pats _129_324))
in (
# 481 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 485 "FStar.Parser.Desugar.fst"
let _50_1012 = (FStar_List.fold_left (fun _50_999 p -> (match (_50_999) with
| (loc, env, pats) -> begin
(
# 486 "FStar.Parser.Desugar.fst"
let _50_1008 = (aux loc env p)
in (match (_50_1008) with
| (loc, env, _50_1004, pat, _50_1007) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_50_1012) with
| (loc, env, args) -> begin
(
# 488 "FStar.Parser.Desugar.fst"
let args = (FStar_List.rev args)
in (
# 489 "FStar.Parser.Desugar.fst"
let l = if dep then begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 491 "FStar.Parser.Desugar.fst"
let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (
# 492 "FStar.Parser.Desugar.fst"
let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _50_1018) -> begin
v
end
| _50_1022 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 495 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _129_327 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _129_327, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 502 "FStar.Parser.Desugar.fst"
let _50_1032 = (FStar_List.hd fields)
in (match (_50_1032) with
| (f, _50_1031) -> begin
(
# 503 "FStar.Parser.Desugar.fst"
let _50_1036 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_50_1036) with
| (record, _50_1035) -> begin
(
# 504 "FStar.Parser.Desugar.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _50_1039 -> (match (_50_1039) with
| (f, p) -> begin
(let _129_329 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_129_329, p))
end))))
in (
# 506 "FStar.Parser.Desugar.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _50_1044 -> (match (_50_1044) with
| (f, _50_1043) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _50_1048 -> (match (_50_1048) with
| (g, _50_1047) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_50_1051, p) -> begin
p
end)
end))))
in (
# 510 "FStar.Parser.Desugar.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 511 "FStar.Parser.Desugar.fst"
let _50_1063 = (aux loc env app)
in (match (_50_1063) with
| (env, e, b, p, _50_1062) -> begin
(
# 512 "FStar.Parser.Desugar.fst"
let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _50_1066, args) -> begin
(let _129_337 = (let _129_336 = (let _129_335 = (let _129_334 = (let _129_333 = (let _129_332 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _129_332))
in FStar_Absyn_Syntax.Record_ctor (_129_333))
in Some (_129_334))
in (fv, _129_335, args))
in FStar_Absyn_Syntax.Pat_cons (_129_336))
in (FStar_All.pipe_left pos _129_337))
end
| _50_1071 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 517 "FStar.Parser.Desugar.fst"
let _50_1080 = (aux [] env p)
in (match (_50_1080) with
| (_50_1074, env, b, p, _50_1079) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _50_1086) -> begin
(let _129_343 = (let _129_342 = (let _129_341 = (FStar_Parser_DesugarEnv.qualify env x)
in (_129_341, FStar_Absyn_Syntax.tun))
in LetBinder (_129_342))
in (env, _129_343, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _50_1093); FStar_Parser_AST.prange = _50_1090}, t) -> begin
(let _129_347 = (let _129_346 = (let _129_345 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _129_344 = (desugar_typ env t)
in (_129_345, _129_344)))
in LetBinder (_129_346))
in (env, _129_347, None))
end
| _50_1101 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 528 "FStar.Parser.Desugar.fst"
let _50_1105 = (desugar_data_pat env p)
in (match (_50_1105) with
| (env, binder, p) -> begin
(
# 529 "FStar.Parser.Desugar.fst"
let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _50_1116 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _50_1120 env pat -> (
# 539 "FStar.Parser.Desugar.fst"
let _50_1128 = (desugar_data_pat env pat)
in (match (_50_1128) with
| (env, _50_1126, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _129_357 = (desugar_typ env t)
in FStar_Util.Inl (_129_357))
end else begin
(let _129_358 = (desugar_exp env t)
in FStar_Util.Inr (_129_358))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (
# 552 "FStar.Parser.Desugar.fst"
let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (
# 553 "FStar.Parser.Desugar.fst"
let setpos = (fun e -> (
# 553 "FStar.Parser.Desugar.fst"
let _50_1142 = e
in {FStar_Absyn_Syntax.n = _50_1142.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _50_1142.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _50_1142.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _50_1142.FStar_Absyn_Syntax.uvs}))
in (match ((let _129_378 = (unparen top)
in _129_378.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (c) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_constant c))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_vlid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (l) -> begin
(
# 561 "FStar.Parser.Desugar.fst"
let op = (FStar_Absyn_Util.fvar None l (FStar_Ident.range_of_lid l))
in (
# 562 "FStar.Parser.Desugar.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _129_382 = (desugar_typ_or_exp env t)
in (_129_382, None)))))
in (let _129_383 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _129_383))))
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
(let _129_384 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _129_384))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 577 "FStar.Parser.Desugar.fst"
let dt = (let _129_389 = (let _129_388 = (let _129_387 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_129_387, Some (FStar_Absyn_Syntax.Data_ctor)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _129_388))
in (FStar_All.pipe_left pos _129_389))
in (match (args) with
| [] -> begin
dt
end
| _50_1169 -> begin
(
# 581 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _50_1172 -> (match (_50_1172) with
| (t, imp) -> begin
(
# 582 "FStar.Parser.Desugar.fst"
let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _129_394 = (let _129_393 = (let _129_392 = (let _129_391 = (FStar_Absyn_Util.mk_exp_app dt args)
in (_129_391, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_129_392))
in (FStar_Absyn_Syntax.mk_Exp_meta _129_393))
in (FStar_All.pipe_left setpos _129_394)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 588 "FStar.Parser.Desugar.fst"
let _50_1209 = (FStar_List.fold_left (fun _50_1181 pat -> (match (_50_1181) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _50_1184}, t) -> begin
(
# 591 "FStar.Parser.Desugar.fst"
let ftvs = (let _129_397 = (free_type_vars env t)
in (FStar_List.append _129_397 ftvs))
in (let _129_399 = (let _129_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _129_398))
in (_129_399, ftvs)))
end
| FStar_Parser_AST.PatTvar (a, _50_1196) -> begin
(let _129_401 = (let _129_400 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _129_400))
in (_129_401, ftvs))
end
| FStar_Parser_AST.PatAscribed (_50_1200, t) -> begin
(let _129_403 = (let _129_402 = (free_type_vars env t)
in (FStar_List.append _129_402 ftvs))
in (env, _129_403))
end
| _50_1205 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_50_1209) with
| (_50_1207, ftv) -> begin
(
# 596 "FStar.Parser.Desugar.fst"
let ftv = (sort_ftv ftv)
in (
# 597 "FStar.Parser.Desugar.fst"
let binders = (let _129_405 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _129_405 binders))
in (
# 599 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs sc_pat_opt _50_8 -> (match (_50_8) with
| [] -> begin
(
# 601 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env body)
in (
# 602 "FStar.Parser.Desugar.fst"
let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(FStar_Absyn_Syntax.mk_Exp_match (sc, ((pat, None, body))::[]) None body.FStar_Absyn_Syntax.pos)
end
| None -> begin
body
end)
in (FStar_Absyn_Syntax.mk_Exp_abs' ((FStar_List.rev bs), body) None top.FStar_Parser_AST.range)))
end
| p::rest -> begin
(
# 608 "FStar.Parser.Desugar.fst"
let _50_1232 = (desugar_binding_pat env p)
in (match (_50_1232) with
| (env, b, pat) -> begin
(
# 609 "FStar.Parser.Desugar.fst"
let _50_1292 = (match (b) with
| LetBinder (_50_1234) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _129_414 = (binder_of_bnd b)
in (_129_414, sc_pat_opt))
end
| VBinder (x, t, aq) -> begin
(
# 613 "FStar.Parser.Desugar.fst"
let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (
# 614 "FStar.Parser.Desugar.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _50_1249) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _129_416 = (let _129_415 = (FStar_Absyn_Util.bvar_to_exp b)
in (_129_415, p))
in Some (_129_416))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Absyn_Syntax.n, p'.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Exp_bvar (_50_1263), _50_1266) -> begin
(
# 620 "FStar.Parser.Desugar.fst"
let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (
# 621 "FStar.Parser.Desugar.fst"
let sc = (let _129_423 = (let _129_422 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _129_421 = (let _129_420 = (FStar_Absyn_Syntax.varg sc)
in (let _129_419 = (let _129_418 = (let _129_417 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _129_417))
in (_129_418)::[])
in (_129_420)::_129_419))
in (_129_422, _129_421)))
in (FStar_Absyn_Syntax.mk_Exp_app _129_423 None top.FStar_Parser_AST.range))
in (
# 622 "FStar.Parser.Desugar.fst"
let p = (let _129_424 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))) None _129_424))
in Some ((sc, p)))))
end
| (FStar_Absyn_Syntax.Exp_app (_50_1272, args), FStar_Absyn_Syntax.Pat_cons (_50_1277, _50_1279, pats)) -> begin
(
# 625 "FStar.Parser.Desugar.fst"
let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (
# 626 "FStar.Parser.Desugar.fst"
let sc = (let _129_430 = (let _129_429 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _129_428 = (let _129_427 = (let _129_426 = (let _129_425 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _129_425))
in (_129_426)::[])
in (FStar_List.append args _129_427))
in (_129_429, _129_428)))
in (FStar_Absyn_Syntax.mk_Exp_app _129_430 None top.FStar_Parser_AST.range))
in (
# 627 "FStar.Parser.Desugar.fst"
let p = (let _129_431 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), (FStar_List.append pats (((p, false))::[]))))) None _129_431))
in Some ((sc, p)))))
end
| _50_1288 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((FStar_Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_50_1292) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _50_1296; FStar_Parser_AST.level = _50_1294}, arg, _50_1302) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(
# 638 "FStar.Parser.Desugar.fst"
let phi = (desugar_formula env arg)
in (let _129_441 = (let _129_440 = (let _129_439 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _129_438 = (let _129_437 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _129_436 = (let _129_435 = (let _129_434 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _129_434))
in (_129_435)::[])
in (_129_437)::_129_436))
in (_129_439, _129_438)))
in (FStar_Absyn_Syntax.mk_Exp_app _129_440))
in (FStar_All.pipe_left pos _129_441)))
end
| FStar_Parser_AST.App (_50_1307) -> begin
(
# 644 "FStar.Parser.Desugar.fst"
let rec aux = (fun args e -> (match ((let _129_446 = (unparen e)
in _129_446.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 646 "FStar.Parser.Desugar.fst"
let arg = (let _129_447 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _129_447))
in (aux ((arg)::args) e))
end
| _50_1319 -> begin
(
# 649 "FStar.Parser.Desugar.fst"
let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _129_453 = (let _129_452 = (let _129_451 = (let _129_450 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_129_450, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_129_451))
in (FStar_Absyn_Syntax.mk_Exp_meta _129_452))
in (FStar_All.pipe_left setpos _129_453))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 658 "FStar.Parser.Desugar.fst"
let ds_let_rec = (fun _50_1335 -> (match (()) with
| () -> begin
(
# 659 "FStar.Parser.Desugar.fst"
let bindings = ((pat, _snd))::_tl
in (
# 660 "FStar.Parser.Desugar.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _50_1339 -> (match (_50_1339) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _129_457 = (destruct_app_pattern env top_level p)
in (_129_457, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _129_458 = (destruct_app_pattern env top_level p)
in (_129_458, def))
end
| _50_1345 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _50_1350); FStar_Parser_AST.prange = _50_1347}, t) -> begin
if top_level then begin
(let _129_461 = (let _129_460 = (let _129_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_129_459))
in (_129_460, [], Some (t)))
in (_129_461, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _50_1359) -> begin
if top_level then begin
(let _129_464 = (let _129_463 = (let _129_462 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_129_462))
in (_129_463, [], None))
in (_129_464, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _50_1363 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 676 "FStar.Parser.Desugar.fst"
let _50_1389 = (FStar_List.fold_left (fun _50_1367 _50_1376 -> (match ((_50_1367, _50_1376)) with
| ((env, fnames), ((f, _50_1370, _50_1372), _50_1375)) -> begin
(
# 678 "FStar.Parser.Desugar.fst"
let _50_1386 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 680 "FStar.Parser.Desugar.fst"
let _50_1381 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_50_1381) with
| (env, xx) -> begin
(env, FStar_Util.Inl (xx))
end))
end
| FStar_Util.Inr (l) -> begin
(let _129_467 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in (_129_467, FStar_Util.Inr (l)))
end)
in (match (_50_1386) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_50_1389) with
| (env', fnames) -> begin
(
# 685 "FStar.Parser.Desugar.fst"
let fnames = (FStar_List.rev fnames)
in (
# 686 "FStar.Parser.Desugar.fst"
let desugar_one_def = (fun env lbname _50_1400 -> (match (_50_1400) with
| ((_50_1395, args, result_t), def) -> begin
(
# 687 "FStar.Parser.Desugar.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _129_474 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _129_474 FStar_Parser_AST.Expr))
end)
in (
# 690 "FStar.Parser.Desugar.fst"
let def = (match (args) with
| [] -> begin
def
end
| _50_1407 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 693 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env def)
in (mk_lb (lbname, FStar_Absyn_Syntax.tun, body)))))
end))
in (
# 695 "FStar.Parser.Desugar.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 696 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env' body)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (
# 699 "FStar.Parser.Desugar.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 700 "FStar.Parser.Desugar.fst"
let t1 = (desugar_exp env t1)
in (
# 701 "FStar.Parser.Desugar.fst"
let _50_1420 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_50_1420) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_50_1422) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(
# 705 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder (x, t, _50_1432) -> begin
(
# 708 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env t2)
in (
# 709 "FStar.Parser.Desugar.fst"
let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _129_486 = (let _129_485 = (FStar_Absyn_Util.bvd_to_exp x t)
in (_129_485, ((pat, None, body))::[]))
in (FStar_Absyn_Syntax.mk_Exp_match _129_486 None body.FStar_Absyn_Syntax.pos))
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
(let _129_499 = (let _129_498 = (let _129_497 = (desugar_exp env t1)
in (let _129_496 = (let _129_495 = (let _129_491 = (desugar_exp env t2)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range), None, _129_491))
in (let _129_494 = (let _129_493 = (let _129_492 = (desugar_exp env t3)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range), None, _129_492))
in (_129_493)::[])
in (_129_495)::_129_494))
in (_129_497, _129_496)))
in (FStar_Absyn_Syntax.mk_Exp_match _129_498))
in (FStar_All.pipe_left pos _129_499))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(
# 726 "FStar.Parser.Desugar.fst"
let r = top.FStar_Parser_AST.range
in (
# 727 "FStar.Parser.Desugar.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 728 "FStar.Parser.Desugar.fst"
let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (
# 729 "FStar.Parser.Desugar.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Absyn_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (
# 730 "FStar.Parser.Desugar.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 734 "FStar.Parser.Desugar.fst"
let desugar_branch = (fun _50_1471 -> (match (_50_1471) with
| (pat, wopt, b) -> begin
(
# 735 "FStar.Parser.Desugar.fst"
let _50_1474 = (desugar_match_pat env pat)
in (match (_50_1474) with
| (env, pat) -> begin
(
# 736 "FStar.Parser.Desugar.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _129_502 = (desugar_exp env e)
in Some (_129_502))
end)
in (
# 739 "FStar.Parser.Desugar.fst"
let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _129_508 = (let _129_507 = (let _129_506 = (desugar_exp env e)
in (let _129_505 = (FStar_List.map desugar_branch branches)
in (_129_506, _129_505)))
in (FStar_Absyn_Syntax.mk_Exp_match _129_507))
in (FStar_All.pipe_left pos _129_508)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _129_514 = (let _129_513 = (let _129_512 = (desugar_exp env e)
in (let _129_511 = (desugar_typ env t)
in (_129_512, _129_511, None)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _129_513))
in (FStar_All.pipe_left pos _129_514))
end
| FStar_Parser_AST.Record (_50_1485, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 750 "FStar.Parser.Desugar.fst"
let _50_1496 = (FStar_List.hd fields)
in (match (_50_1496) with
| (f, _50_1495) -> begin
(
# 751 "FStar.Parser.Desugar.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 752 "FStar.Parser.Desugar.fst"
let _50_1502 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_50_1502) with
| (record, _50_1501) -> begin
(
# 753 "FStar.Parser.Desugar.fst"
let get_field = (fun xopt f -> (
# 754 "FStar.Parser.Desugar.fst"
let fn = f.FStar_Ident.ident
in (
# 755 "FStar.Parser.Desugar.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _50_1510 -> (match (_50_1510) with
| (g, _50_1509) -> begin
(
# 756 "FStar.Parser.Desugar.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_50_1514, e) -> begin
(let _129_522 = (qfn fn)
in (_129_522, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _129_525 = (let _129_524 = (let _129_523 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_129_523, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_129_524))
in (Prims.raise _129_525))
end
| Some (x) -> begin
(let _129_526 = (qfn fn)
in (_129_526, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 766 "FStar.Parser.Desugar.fst"
let recterm = (match (eopt) with
| None -> begin
(let _129_531 = (let _129_530 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _50_1526 -> (match (_50_1526) with
| (f, _50_1525) -> begin
(let _129_529 = (let _129_528 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _129_528))
in (_129_529, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_DesugarEnv.constrname, _129_530))
in FStar_Parser_AST.Construct (_129_531))
end
| Some (e) -> begin
(
# 773 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (
# 774 "FStar.Parser.Desugar.fst"
let xterm = (let _129_533 = (let _129_532 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_129_532))
in (FStar_Parser_AST.mk_term _129_533 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 775 "FStar.Parser.Desugar.fst"
let record = (let _129_536 = (let _129_535 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _50_1534 -> (match (_50_1534) with
| (f, _50_1533) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _129_535))
in FStar_Parser_AST.Record (_129_536))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 778 "FStar.Parser.Desugar.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 779 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1557); FStar_Absyn_Syntax.tk = _50_1554; FStar_Absyn_Syntax.pos = _50_1552; FStar_Absyn_Syntax.fvs = _50_1550; FStar_Absyn_Syntax.uvs = _50_1548}, args); FStar_Absyn_Syntax.tk = _50_1546; FStar_Absyn_Syntax.pos = _50_1544; FStar_Absyn_Syntax.fvs = _50_1542; FStar_Absyn_Syntax.uvs = _50_1540}, FStar_Absyn_Syntax.Data_app)) -> begin
(
# 782 "FStar.Parser.Desugar.fst"
let e = (let _129_546 = (let _129_545 = (let _129_544 = (let _129_543 = (let _129_542 = (let _129_541 = (let _129_540 = (let _129_539 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _129_539))
in FStar_Absyn_Syntax.Record_ctor (_129_540))
in Some (_129_541))
in (fv, _129_542))
in (FStar_Absyn_Syntax.mk_Exp_fvar _129_543 None e.FStar_Absyn_Syntax.pos))
in (_129_544, args))
in (FStar_Absyn_Syntax.mk_Exp_app _129_545))
in (FStar_All.pipe_left pos _129_546))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Data_app)))))
end
| _50_1571 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 790 "FStar.Parser.Desugar.fst"
let _50_1578 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_50_1578) with
| (fieldname, is_rec) -> begin
(
# 791 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env e)
in (
# 792 "FStar.Parser.Desugar.fst"
let fn = (
# 793 "FStar.Parser.Desugar.fst"
let _50_1583 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_50_1583) with
| (ns, _50_1582) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 795 "FStar.Parser.Desugar.fst"
let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _129_553 = (let _129_552 = (let _129_551 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (let _129_550 = (let _129_549 = (FStar_Absyn_Syntax.varg e)
in (_129_549)::[])
in (_129_551, _129_550)))
in (FStar_Absyn_Syntax.mk_Exp_app _129_552))
in (FStar_All.pipe_left pos _129_553)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _50_1589 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (
# 806 "FStar.Parser.Desugar.fst"
let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (
# 807 "FStar.Parser.Desugar.fst"
let setpos = (fun t -> (
# 807 "FStar.Parser.Desugar.fst"
let _50_1596 = t
in {FStar_Absyn_Syntax.n = _50_1596.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _50_1596.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _50_1596.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _50_1596.FStar_Absyn_Syntax.uvs}))
in (
# 808 "FStar.Parser.Desugar.fst"
let top = (unparen top)
in (
# 809 "FStar.Parser.Desugar.fst"
let head_and_args = (fun t -> (
# 810 "FStar.Parser.Desugar.fst"
let rec aux = (fun args t -> (match ((let _129_576 = (unparen t)
in _129_576.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _50_1614 -> begin
(t, args)
end))
in (aux [] t)))
in (match (top.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.tun)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(
# 819 "FStar.Parser.Desugar.fst"
let t = (label_conjuncts "pre-condition" true lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _129_577 = (desugar_exp env t)
in (FStar_All.pipe_right _129_577 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(
# 825 "FStar.Parser.Desugar.fst"
let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _129_578 = (desugar_exp env t)
in (FStar_All.pipe_right _129_578 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", t1::_50_1628::[]) -> begin
if (is_type env t1) then begin
(
# 831 "FStar.Parser.Desugar.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 833 "FStar.Parser.Desugar.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _50_1643 -> begin
(t)::[]
end))
in (
# 836 "FStar.Parser.Desugar.fst"
let targs = (let _129_583 = (flatten top)
in (FStar_All.pipe_right _129_583 (FStar_List.map (fun t -> (let _129_582 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _129_582))))))
in (
# 837 "FStar.Parser.Desugar.fst"
let tup = (let _129_584 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _129_584))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end else begin
(let _129_590 = (let _129_589 = (let _129_588 = (let _129_587 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _129_587))
in (_129_588, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_129_589))
in (Prims.raise _129_590))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _129_591 = (desugar_exp env top)
in (FStar_All.pipe_right _129_591 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(
# 848 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun t -> (let _129_593 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _129_593))) args)
in (let _129_594 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _129_594 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _129_595 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _129_595))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _129_596 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _129_596))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(
# 864 "FStar.Parser.Desugar.fst"
let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _129_597 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _129_597)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 868 "FStar.Parser.Desugar.fst"
let t = (let _129_598 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _129_598))
in (
# 869 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _50_1679 -> (match (_50_1679) with
| (t, imp) -> begin
(let _129_600 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _129_600))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 873 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _50_9 -> (match (_50_9) with
| [] -> begin
(
# 875 "FStar.Parser.Desugar.fst"
let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.rev bs), body))))
end
| hd::tl -> begin
(
# 878 "FStar.Parser.Desugar.fst"
let _50_1697 = (desugar_binding_pat env hd)
in (match (_50_1697) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _129_612 = (let _129_611 = (let _129_610 = (let _129_609 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _129_609))
in (_129_610, hd.FStar_Parser_AST.prange))
in FStar_Absyn_Syntax.Error (_129_611))
in (Prims.raise _129_612))
end
| None -> begin
(
# 882 "FStar.Parser.Desugar.fst"
let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_50_1703) -> begin
(
# 887 "FStar.Parser.Desugar.fst"
let rec aux = (fun args e -> (match ((let _129_617 = (unparen e)
in _129_617.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(
# 889 "FStar.Parser.Desugar.fst"
let arg = (let _129_618 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _129_618))
in (aux ((arg)::args) e))
end
| _50_1715 -> begin
(
# 892 "FStar.Parser.Desugar.fst"
let head = (desugar_typ env e)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Product ([], t) -> begin
(FStar_All.failwith "Impossible: product with no binders")
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 900 "FStar.Parser.Desugar.fst"
let _50_1727 = (uncurry binders t)
in (match (_50_1727) with
| (bs, t) -> begin
(
# 901 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _50_10 -> (match (_50_10) with
| [] -> begin
(
# 903 "FStar.Parser.Desugar.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.rev bs), cod))))
end
| hd::tl -> begin
(
# 906 "FStar.Parser.Desugar.fst"
let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (
# 907 "FStar.Parser.Desugar.fst"
let bb = (desugar_binder mlenv hd)
in (
# 908 "FStar.Parser.Desugar.fst"
let _50_1741 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_50_1741) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _50_1748) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 916 "FStar.Parser.Desugar.fst"
let _50_1762 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _50_1754), env) -> begin
(x, env)
end
| _50_1759 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_50_1762) with
| (b, env) -> begin
(
# 919 "FStar.Parser.Desugar.fst"
let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _129_629 = (desugar_exp env f)
in (FStar_All.pipe_right _129_629 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _129_637 = (let _129_636 = (let _129_635 = (desugar_typ env t)
in (let _129_634 = (desugar_kind env k)
in (_129_635, _129_634)))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _129_636))
in (FStar_All.pipe_left wpos _129_637))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(
# 931 "FStar.Parser.Desugar.fst"
let _50_1796 = (FStar_List.fold_left (fun _50_1781 b -> (match (_50_1781) with
| (env, tparams, typs) -> begin
(
# 932 "FStar.Parser.Desugar.fst"
let _50_1785 = (desugar_exp_binder env b)
in (match (_50_1785) with
| (xopt, t) -> begin
(
# 933 "FStar.Parser.Desugar.fst"
let _50_1791 = (match (xopt) with
| None -> begin
(let _129_640 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in (env, _129_640))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_50_1791) with
| (env, x) -> begin
(let _129_644 = (let _129_643 = (let _129_642 = (let _129_641 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _129_641))
in (_129_642)::[])
in (FStar_List.append typs _129_643))
in (env, (FStar_List.append tparams (((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _129_644))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_50_1796) with
| (env, _50_1794, targs) -> begin
(
# 938 "FStar.Parser.Desugar.fst"
let tup = (let _129_645 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _129_645))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| FStar_Parser_AST.Record (_50_1799) -> begin
(FStar_All.failwith "Unexpected record type")
end
| FStar_Parser_AST.Let (false, (x, v)::[], t) -> begin
(
# 945 "FStar.Parser.Desugar.fst"
let let_v = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.let_in_typ)) top.FStar_Parser_AST.range top.FStar_Parser_AST.level), v, FStar_Parser_AST.Nothing))) v.FStar_Parser_AST.range v.FStar_Parser_AST.level)
in (
# 946 "FStar.Parser.Desugar.fst"
let t' = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((let_v, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs (((x)::[], t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), FStar_Parser_AST.Nothing))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_typ env t')))
end
| (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _50_1818 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _50_1820 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (
# 956 "FStar.Parser.Desugar.fst"
let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error ((msg, r)))))
in (
# 957 "FStar.Parser.Desugar.fst"
let pre_process_comp_typ = (fun t -> (
# 958 "FStar.Parser.Desugar.fst"
let _50_1831 = (head_and_args t)
in (match (_50_1831) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 961 "FStar.Parser.Desugar.fst"
let unit = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 962 "FStar.Parser.Desugar.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 963 "FStar.Parser.Desugar.fst"
let _50_1857 = (FStar_All.pipe_right args (FStar_List.partition (fun _50_1839 -> (match (_50_1839) with
| (arg, _50_1838) -> begin
(match ((let _129_657 = (unparen arg)
in _129_657.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _50_1843; FStar_Parser_AST.level = _50_1841}, _50_1848, _50_1850) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _50_1854 -> begin
false
end)
end))))
in (match (_50_1857) with
| (decreases_clause, args) -> begin
(
# 967 "FStar.Parser.Desugar.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 970 "FStar.Parser.Desugar.fst"
let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (unit)::(req_true)::(ens)::(nil_pat)::[])
end
| req::ens::[] -> begin
(unit)::(req)::(ens)::(nil_pat)::[]
end
| more -> begin
(unit)::more
end)
in (
# 974 "FStar.Parser.Desugar.fst"
let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct ((lemma, (FStar_List.append args decreases_clause)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _129_658 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _129_658 FStar_Absyn_Const.prims_lid))) -> begin
(
# 981 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _50_1872 -> (match (_50_1872) with
| (t, imp) -> begin
(let _129_660 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _129_660))
end)) args)
in (let _129_661 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _129_661 args)))
end
| _50_1875 -> begin
(desugar_typ env t)
end)
end)))
in (
# 986 "FStar.Parser.Desugar.fst"
let t = (pre_process_comp_typ t)
in (
# 987 "FStar.Parser.Desugar.fst"
let _50_1879 = (FStar_Absyn_Util.head_and_args t)
in (match (_50_1879) with
| (head, args) -> begin
(match ((let _129_663 = (let _129_662 = (FStar_Absyn_Util.compress_typ head)
in _129_662.FStar_Absyn_Syntax.n)
in (_129_663, args))) with
| (FStar_Absyn_Syntax.Typ_const (eff), (FStar_Util.Inl (result_typ), _50_1886)::rest) -> begin
(
# 990 "FStar.Parser.Desugar.fst"
let _50_1926 = (FStar_All.pipe_right rest (FStar_List.partition (fun _50_11 -> (match (_50_11) with
| (FStar_Util.Inr (_50_1892), _50_1895) -> begin
false
end
| (FStar_Util.Inl (t), _50_1900) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _50_1909; FStar_Absyn_Syntax.pos = _50_1907; FStar_Absyn_Syntax.fvs = _50_1905; FStar_Absyn_Syntax.uvs = _50_1903}, (FStar_Util.Inr (_50_1914), _50_1917)::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _50_1923 -> begin
false
end)
end))))
in (match (_50_1926) with
| (dec, rest) -> begin
(
# 998 "FStar.Parser.Desugar.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _50_12 -> (match (_50_12) with
| (FStar_Util.Inl (t), _50_1931) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_50_1934, (FStar_Util.Inr (arg), _50_1938)::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _50_1944 -> begin
(FStar_All.failwith "impos")
end)
end
| _50_1946 -> begin
(FStar_All.failwith "impos")
end))))
in if ((FStar_Parser_DesugarEnv.is_effect_name env eff.FStar_Absyn_Syntax.v) || (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid)) then begin
if ((FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Absyn_Syntax.mk_Total result_typ)
end else begin
(
# 1009 "FStar.Parser.Desugar.fst"
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
# 1014 "FStar.Parser.Desugar.fst"
let rest = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(FStar_Util.Inr (pat), aq)::[] -> begin
(let _129_670 = (let _129_669 = (let _129_668 = (let _129_667 = (let _129_666 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((pat, FStar_Absyn_Syntax.Meta_smt_pat))))
in FStar_Util.Inr (_129_666))
in (_129_667, aq))
in (_129_668)::[])
in (ens)::_129_669)
in (req)::_129_670)
end
| _50_1957 -> begin
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
(let _129_672 = (let _129_671 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _129_671))
in (fail _129_672))
end
end)
end))
end
| _50_1960 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _129_674 = (let _129_673 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _129_673))
in (fail _129_674))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (
# 1033 "FStar.Parser.Desugar.fst"
let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (
# 1034 "FStar.Parser.Desugar.fst"
let setpos = (fun kk -> (
# 1034 "FStar.Parser.Desugar.fst"
let _50_1967 = kk
in {FStar_Absyn_Syntax.n = _50_1967.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _50_1967.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _50_1967.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _50_1967.FStar_Absyn_Syntax.uvs}))
in (
# 1035 "FStar.Parser.Desugar.fst"
let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _50_1976; FStar_Ident.ident = _50_1974; FStar_Ident.nsstr = _50_1972; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _50_1985; FStar_Ident.ident = _50_1983; FStar_Ident.nsstr = _50_1981; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _129_686 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _129_686))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _50_1993 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(
# 1046 "FStar.Parser.Desugar.fst"
let _50_2001 = (uncurry bs k)
in (match (_50_2001) with
| (bs, k) -> begin
(
# 1047 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _50_13 -> (match (_50_13) with
| [] -> begin
(let _129_697 = (let _129_696 = (let _129_695 = (desugar_kind env k)
in ((FStar_List.rev bs), _129_695))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_696))
in (FStar_All.pipe_left pos _129_697))
end
| hd::tl -> begin
(
# 1051 "FStar.Parser.Desugar.fst"
let _50_2012 = (let _129_699 = (let _129_698 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _129_698 hd))
in (FStar_All.pipe_right _129_699 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_50_2012) with
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
# 1059 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _50_2022 -> (match (_50_2022) with
| (t, b) -> begin
(
# 1060 "FStar.Parser.Desugar.fst"
let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _129_701 = (desugar_typ_or_exp env t)
in (_129_701, qual)))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _50_2026 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env f -> (
# 1067 "FStar.Parser.Desugar.fst"
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
| _50_2037 -> begin
None
end))
in (
# 1074 "FStar.Parser.Desugar.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 1075 "FStar.Parser.Desugar.fst"
let setpos = (fun t -> (
# 1075 "FStar.Parser.Desugar.fst"
let _50_2042 = t
in {FStar_Absyn_Syntax.n = _50_2042.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _50_2042.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _50_2042.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _50_2042.FStar_Absyn_Syntax.uvs}))
in (
# 1076 "FStar.Parser.Desugar.fst"
let desugar_quant = (fun q qt b pats body -> (
# 1077 "FStar.Parser.Desugar.fst"
let tk = (desugar_binder env (
# 1077 "FStar.Parser.Desugar.fst"
let _50_2050 = b
in {FStar_Parser_AST.b = _50_2050.FStar_Parser_AST.b; FStar_Parser_AST.brange = _50_2050.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _50_2050.FStar_Parser_AST.aqual}))
in (
# 1078 "FStar.Parser.Desugar.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _129_737 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _129_737)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1081 "FStar.Parser.Desugar.fst"
let _50_2065 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_50_2065) with
| (env, a) -> begin
(
# 1082 "FStar.Parser.Desugar.fst"
let pats = (desugar_pats env pats)
in (
# 1083 "FStar.Parser.Desugar.fst"
let body = (desugar_formula env body)
in (
# 1084 "FStar.Parser.Desugar.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _50_2070 -> begin
(let _129_738 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (FStar_All.pipe_left setpos _129_738))
end)
in (
# 1087 "FStar.Parser.Desugar.fst"
let body = (let _129_744 = (let _129_743 = (let _129_742 = (let _129_741 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_129_741)::[])
in (_129_742, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _129_743))
in (FStar_All.pipe_left pos _129_744))
in (let _129_749 = (let _129_748 = (let _129_745 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _129_745 FStar_Absyn_Syntax.kun))
in (let _129_747 = (let _129_746 = (FStar_Absyn_Syntax.targ body)
in (_129_746)::[])
in (FStar_Absyn_Util.mk_typ_app _129_748 _129_747)))
in (FStar_All.pipe_left setpos _129_749))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1091 "FStar.Parser.Desugar.fst"
let _50_2080 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_50_2080) with
| (env, x) -> begin
(
# 1092 "FStar.Parser.Desugar.fst"
let pats = (desugar_pats env pats)
in (
# 1093 "FStar.Parser.Desugar.fst"
let body = (desugar_formula env body)
in (
# 1094 "FStar.Parser.Desugar.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _50_2085 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (
# 1097 "FStar.Parser.Desugar.fst"
let body = (let _129_755 = (let _129_754 = (let _129_753 = (let _129_752 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_129_752)::[])
in (_129_753, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _129_754))
in (FStar_All.pipe_left pos _129_755))
in (let _129_760 = (let _129_759 = (let _129_756 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _129_756 FStar_Absyn_Syntax.kun))
in (let _129_758 = (let _129_757 = (FStar_Absyn_Syntax.targ body)
in (_129_757)::[])
in (FStar_Absyn_Util.mk_typ_app _129_759 _129_758)))
in (FStar_All.pipe_left setpos _129_760))))))
end))
end
| _50_2089 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1102 "FStar.Parser.Desugar.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 1104 "FStar.Parser.Desugar.fst"
let rest = (b')::_rest
in (
# 1105 "FStar.Parser.Desugar.fst"
let body = (let _129_775 = (q (rest, pats, body))
in (let _129_774 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _129_775 _129_774 FStar_Parser_AST.Formula)))
in (let _129_776 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _129_776 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _50_2103 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _129_777 = (unparen f)
in _129_777.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 1111 "FStar.Parser.Desugar.fst"
let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, l, FStar_Absyn_Syntax.dummyRange, p)))))
end
| FStar_Parser_AST.Op ("==", hd::_args) -> begin
(
# 1115 "FStar.Parser.Desugar.fst"
let args = (hd)::_args
in (
# 1116 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun t -> (let _129_779 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _129_779))) args)
in (
# 1117 "FStar.Parser.Desugar.fst"
let eq = if (is_type env hd) then begin
(let _129_780 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _129_780 FStar_Absyn_Syntax.kun))
end else begin
(let _129_781 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _129_781 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match (((connective s), args)) with
| (Some (conn), _50_2129::_50_2127::[]) -> begin
(let _129_786 = (let _129_782 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _129_782 FStar_Absyn_Syntax.kun))
in (let _129_785 = (FStar_List.map (fun x -> (let _129_784 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _129_784))) args)
in (FStar_Absyn_Util.mk_typ_app _129_786 _129_785)))
end
| _50_2134 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _129_787 = (desugar_exp env f)
in (FStar_All.pipe_right _129_787 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _129_792 = (let _129_788 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _129_788 FStar_Absyn_Syntax.kun))
in (let _129_791 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _129_790 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _129_790))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _129_792 _129_791)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 1145 "FStar.Parser.Desugar.fst"
let binders = (_1)::(_2)::_3
in (let _129_794 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _129_794)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 1149 "FStar.Parser.Desugar.fst"
let binders = (_1)::(_2)::_3
in (let _129_796 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _129_796)))
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
| _50_2196 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _129_797 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _129_797))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (
# 1166 "FStar.Parser.Desugar.fst"
let _50_2199 = env
in {FStar_Parser_DesugarEnv.curmodule = _50_2199.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _50_2199.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _50_2199.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _50_2199.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _50_2199.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _50_2199.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _50_2199.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _50_2199.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _50_2199.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _50_2199.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _50_2199.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _129_802 = (desugar_type_binder env b)
in FStar_Util.Inl (_129_802))
end else begin
(let _129_803 = (desugar_exp_binder env b)
in FStar_Util.Inr (_129_803))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 1174 "FStar.Parser.Desugar.fst"
let _50_2232 = (FStar_List.fold_left (fun _50_2207 b -> (match (_50_2207) with
| (env, out) -> begin
(
# 1175 "FStar.Parser.Desugar.fst"
let tk = (desugar_binder env (
# 1175 "FStar.Parser.Desugar.fst"
let _50_2209 = b
in {FStar_Parser_AST.b = _50_2209.FStar_Parser_AST.b; FStar_Parser_AST.brange = _50_2209.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _50_2209.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1178 "FStar.Parser.Desugar.fst"
let _50_2219 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_50_2219) with
| (env, a) -> begin
(env, ((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1181 "FStar.Parser.Desugar.fst"
let _50_2227 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_50_2227) with
| (env, x) -> begin
(env, ((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| _50_2229 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_50_2232) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _129_810 = (desugar_typ env t)
in (Some (x), _129_810))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _129_811 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _129_811))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _129_812 = (desugar_typ env t)
in (None, _129_812))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Absyn_Syntax.tun)
end
| _50_2246 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.FStar_Parser_AST.brange))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (
# 1194 "FStar.Parser.Desugar.fst"
let fail = (fun _50_2250 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.FStar_Parser_AST.brange))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _129_817 = (desugar_kind env t)
in (Some (x), _129_817))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _129_818 = (desugar_kind env t)
in (None, _129_818))
end
| FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (
# 1199 "FStar.Parser.Desugar.fst"
let _50_2261 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _50_2261.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _50_2261.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _50_2261.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _50_2261.FStar_Absyn_Syntax.uvs}))
end
| _50_2264 -> begin
(fail ())
end)))

# 1202 "FStar.Parser.Desugar.fst"
let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (
# 1203 "FStar.Parser.Desugar.fst"
let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_50_2275, k) -> begin
(aux bs k)
end
| _50_2280 -> begin
bs
end))
in (let _129_827 = (aux tps k)
in (FStar_All.pipe_right _129_827 FStar_Absyn_Util.name_binders))))

# 1210 "FStar.Parser.Desugar.fst"
let mk_data_discriminators : FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Ident.lid  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1212 "FStar.Parser.Desugar.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1213 "FStar.Parser.Desugar.fst"
let binders = (gather_tc_binders tps k)
in (
# 1214 "FStar.Parser.Desugar.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1215 "FStar.Parser.Desugar.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _50_2294 -> (match (_50_2294) with
| (x, _50_2293) -> begin
(x, Some (imp_tag))
end))))
in (
# 1216 "FStar.Parser.Desugar.fst"
let binders = (let _129_848 = (let _129_847 = (let _129_846 = (let _129_845 = (let _129_844 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _129_843 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_129_844, _129_843)))
in (FStar_Absyn_Syntax.mk_Typ_app' _129_845 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _129_846))
in (_129_847)::[])
in (FStar_List.append imp_binders _129_848))
in (
# 1217 "FStar.Parser.Desugar.fst"
let disc_type = (let _129_851 = (let _129_850 = (let _129_849 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _129_849 p))
in (binders, _129_850))
in (FStar_Absyn_Syntax.mk_Typ_fun _129_851 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1219 "FStar.Parser.Desugar.fst"
let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _129_854 = (let _129_853 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in (disc_name, disc_type, _129_853, (FStar_Ident.range_of_lid disc_name)))
in FStar_Absyn_Syntax.Sig_val_decl (_129_854)))))))))))))

# 1223 "FStar.Parser.Desugar.fst"
let mk_indexed_projectors = (fun fvq refine_domain env _50_2306 lid formals t -> (match (_50_2306) with
| (tc, tps, k) -> begin
(
# 1224 "FStar.Parser.Desugar.fst"
let binders = (gather_tc_binders tps k)
in (
# 1225 "FStar.Parser.Desugar.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1226 "FStar.Parser.Desugar.fst"
let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (
# 1227 "FStar.Parser.Desugar.fst"
let projectee = (let _129_865 = (FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _129_864 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _129_865; FStar_Absyn_Syntax.realname = _129_864}))
in (
# 1229 "FStar.Parser.Desugar.fst"
let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (
# 1230 "FStar.Parser.Desugar.fst"
let arg_binder = (
# 1231 "FStar.Parser.Desugar.fst"
let arg_typ = (let _129_868 = (let _129_867 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _129_866 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_129_867, _129_866)))
in (FStar_Absyn_Syntax.mk_Typ_app' _129_868 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(
# 1234 "FStar.Parser.Desugar.fst"
let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (
# 1235 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _129_878 = (let _129_877 = (let _129_876 = (let _129_875 = (let _129_874 = (let _129_873 = (let _129_872 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _129_871 = (let _129_870 = (let _129_869 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _129_869))
in (_129_870)::[])
in (_129_872, _129_871)))
in (FStar_Absyn_Syntax.mk_Exp_app _129_873 None p))
in (FStar_Absyn_Util.b2t _129_874))
in (x, _129_875))
in (FStar_Absyn_Syntax.mk_Typ_refine _129_876 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _129_877))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _129_878))))
end)
in (
# 1237 "FStar.Parser.Desugar.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _50_2323 -> (match (_50_2323) with
| (x, _50_2322) -> begin
(x, Some (imp_tag))
end))))
in (
# 1238 "FStar.Parser.Desugar.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1239 "FStar.Parser.Desugar.fst"
let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (
# 1240 "FStar.Parser.Desugar.fst"
let subst = (let _129_886 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(
# 1242 "FStar.Parser.Desugar.fst"
let _50_2334 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_50_2334) with
| (field_name, _50_2333) -> begin
(
# 1243 "FStar.Parser.Desugar.fst"
let proj = (let _129_883 = (let _129_882 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in (_129_882, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _129_883 None p))
in (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, proj)))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(
# 1247 "FStar.Parser.Desugar.fst"
let _50_2341 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_50_2341) with
| (field_name, _50_2340) -> begin
(
# 1248 "FStar.Parser.Desugar.fst"
let proj = (let _129_885 = (let _129_884 = (FStar_Absyn_Util.fvar None field_name p)
in (_129_884, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _129_885 None p))
in (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, proj)))::[])
end))
end))))
in (FStar_All.pipe_right _129_886 FStar_List.flatten))
in (
# 1251 "FStar.Parser.Desugar.fst"
let ntps = (FStar_List.length tps)
in (
# 1252 "FStar.Parser.Desugar.fst"
let all_params = (let _129_888 = (FStar_All.pipe_right tps (FStar_List.map (fun _50_2348 -> (match (_50_2348) with
| (b, _50_2347) -> begin
(b, Some (imp_tag))
end))))
in (FStar_List.append _129_888 formals))
in (let _129_918 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(
# 1256 "FStar.Parser.Desugar.fst"
let _50_2357 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_50_2357) with
| (field_name, _50_2356) -> begin
(
# 1257 "FStar.Parser.Desugar.fst"
let kk = (let _129_892 = (let _129_891 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (binders, _129_891))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_892 p))
in (FStar_Absyn_Syntax.Sig_tycon ((field_name, [], kk, [], [], (FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inl (a.FStar_Absyn_Syntax.v))))::[], (FStar_Ident.range_of_lid field_name))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(
# 1261 "FStar.Parser.Desugar.fst"
let _50_2364 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_50_2364) with
| (field_name, _50_2363) -> begin
(
# 1262 "FStar.Parser.Desugar.fst"
let t = (let _129_895 = (let _129_894 = (let _129_893 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _129_893 p))
in (binders, _129_894))
in (FStar_Absyn_Syntax.mk_Typ_fun _129_895 None p))
in (
# 1263 "FStar.Parser.Desugar.fst"
let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1264 "FStar.Parser.Desugar.fst"
let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inr (x.FStar_Absyn_Syntax.v))))::[]))
in (
# 1265 "FStar.Parser.Desugar.fst"
let impl = if (((let _129_898 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _129_898)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _129_900 = (let _129_899 = (FStar_Parser_DesugarEnv.current_module env)
in _129_899.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _129_900))) then begin
[]
end else begin
(
# 1270 "FStar.Parser.Desugar.fst"
let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (
# 1271 "FStar.Parser.Desugar.fst"
let as_imp = (fun _50_14 -> (match (_50_14) with
| Some (FStar_Absyn_Syntax.Implicit (_50_2372)) -> begin
true
end
| _50_2376 -> begin
false
end))
in (
# 1274 "FStar.Parser.Desugar.fst"
let arg_pats = (let _129_915 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_50_2381), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _129_908 = (let _129_907 = (let _129_906 = (let _129_905 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_129_905))
in (pos _129_906))
in (_129_907, (as_imp imp)))
in (_129_908)::[])
end
end
| (FStar_Util.Inr (_50_2386), imp) -> begin
if ((i + ntps) = j) then begin
(let _129_910 = (let _129_909 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in (_129_909, (as_imp imp)))
in (_129_910)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _129_914 = (let _129_913 = (let _129_912 = (let _129_911 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_129_911))
in (pos _129_912))
in (_129_913, (as_imp imp)))
in (_129_914)::[])
end
end
end))))
in (FStar_All.pipe_right _129_915 FStar_List.flatten))
in (
# 1283 "FStar.Parser.Desugar.fst"
let pat = (let _129_917 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv lid), Some (fvq), arg_pats))) pos)
in (let _129_916 = (FStar_Absyn_Util.bvar_to_exp projection)
in (_129_917, None, _129_916)))
in (
# 1284 "FStar.Parser.Desugar.fst"
let body = (FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (
# 1285 "FStar.Parser.Desugar.fst"
let imp = (FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None (FStar_Ident.range_of_lid field_name))
in (
# 1286 "FStar.Parser.Desugar.fst"
let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end
in (FStar_Absyn_Syntax.Sig_val_decl ((field_name, t, quals, (FStar_Ident.range_of_lid field_name))))::impl))))
end))
end))))
in (FStar_All.pipe_right _129_918 FStar_List.flatten))))))))))))))
end))

# 1295 "FStar.Parser.Desugar.fst"
let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _50_17 -> (match (_50_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _50_2403, _50_2405) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(
# 1298 "FStar.Parser.Desugar.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_15 -> (match (_50_15) with
| FStar_Absyn_Syntax.RecordConstructor (_50_2410) -> begin
true
end
| _50_2413 -> begin
false
end)))) then begin
false
end else begin
(
# 1301 "FStar.Parser.Desugar.fst"
let _50_2419 = tycon
in (match (_50_2419) with
| (l, _50_2416, _50_2418) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _50_2423 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(
# 1307 "FStar.Parser.Desugar.fst"
let cod = (FStar_Absyn_Util.comp_result cod)
in (
# 1308 "FStar.Parser.Desugar.fst"
let qual = (match ((FStar_Util.find_map quals (fun _50_16 -> (match (_50_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((lid, fns)))
end
| _50_2434 -> begin
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
| _50_2440 -> begin
[]
end))
end
| _50_2442 -> begin
[]
end))

# 1318 "FStar.Parser.Desugar.fst"
let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1319 "FStar.Parser.Desugar.fst"
let tycon_id = (fun _50_18 -> (match (_50_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1324 "FStar.Parser.Desugar.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _129_938 = (let _129_937 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_129_937))
in (FStar_Parser_AST.mk_term _129_938 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1330 "FStar.Parser.Desugar.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1331 "FStar.Parser.Desugar.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1332 "FStar.Parser.Desugar.fst"
let apply_binders = (fun t binders -> (
# 1333 "FStar.Parser.Desugar.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _50_2507 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _129_951 = (let _129_950 = (let _129_949 = (binder_to_term b)
in (out, _129_949, (imp_of_aqual b)))
in FStar_Parser_AST.App (_129_950))
in (FStar_Parser_AST.mk_term _129_951 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1338 "FStar.Parser.Desugar.fst"
let tycon_record_as_variant = (fun _50_19 -> (match (_50_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1340 "FStar.Parser.Desugar.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1341 "FStar.Parser.Desugar.fst"
let mfields = (FStar_List.map (fun _50_2520 -> (match (_50_2520) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Absyn_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1342 "FStar.Parser.Desugar.fst"
let result = (let _129_957 = (let _129_956 = (let _129_955 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_129_955))
in (FStar_Parser_AST.mk_term _129_956 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _129_957 parms))
in (
# 1343 "FStar.Parser.Desugar.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _129_959 = (FStar_All.pipe_right fields (FStar_List.map (fun _50_2527 -> (match (_50_2527) with
| (x, _50_2526) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _129_959))))))
end
| _50_2529 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1347 "FStar.Parser.Desugar.fst"
let desugar_abstract_tc = (fun quals _env mutuals _50_20 -> (match (_50_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1349 "FStar.Parser.Desugar.fst"
let _50_2543 = (typars_of_binders _env binders)
in (match (_50_2543) with
| (_env', typars) -> begin
(
# 1350 "FStar.Parser.Desugar.fst"
let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (
# 1353 "FStar.Parser.Desugar.fst"
let tconstr = (let _129_970 = (let _129_969 = (let _129_968 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_129_968))
in (FStar_Parser_AST.mk_term _129_969 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _129_970 binders))
in (
# 1354 "FStar.Parser.Desugar.fst"
let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (
# 1355 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (
# 1356 "FStar.Parser.Desugar.fst"
let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (
# 1357 "FStar.Parser.Desugar.fst"
let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, _env2, se, tconstr)))))))
end))
end
| _50_2554 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1360 "FStar.Parser.Desugar.fst"
let push_tparam = (fun env _50_21 -> (match (_50_21) with
| (FStar_Util.Inr (x), _50_2561) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _50_2566) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (
# 1363 "FStar.Parser.Desugar.fst"
let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_50_2570)::[] -> begin
(
# 1366 "FStar.Parser.Desugar.fst"
let tc = (FStar_List.hd tcs)
in (
# 1367 "FStar.Parser.Desugar.fst"
let _50_2581 = (desugar_abstract_tc quals env [] tc)
in (match (_50_2581) with
| (_50_2575, _50_2577, se, _50_2580) -> begin
(
# 1368 "FStar.Parser.Desugar.fst"
let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(
# 1371 "FStar.Parser.Desugar.fst"
let _50_2582 = (let _129_980 = (FStar_Range.string_of_range rng)
in (let _129_979 = (let _129_978 = (let _129_977 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _129_977 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _129_978 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _129_980 _129_979)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (
# 1374 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1379 "FStar.Parser.Desugar.fst"
let _50_2595 = (typars_of_binders env binders)
in (match (_50_2595) with
| (env', typars) -> begin
(
# 1380 "FStar.Parser.Desugar.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _50_22 -> (match (_50_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _50_2600 -> begin
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
# 1386 "FStar.Parser.Desugar.fst"
let t0 = t
in (
# 1387 "FStar.Parser.Desugar.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_23 -> (match (_50_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _50_2608 -> begin
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
# 1392 "FStar.Parser.Desugar.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Effect)) then begin
(
# 1394 "FStar.Parser.Desugar.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let _129_986 = (let _129_985 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _129_984 = (FStar_All.pipe_right quals (FStar_List.filter (fun _50_24 -> (match (_50_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _50_2614 -> begin
true
end))))
in (_129_985, typars, c, _129_984, rng)))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_129_986)))
end else begin
(
# 1396 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env' t)
in (let _129_988 = (let _129_987 = (FStar_Parser_DesugarEnv.qualify env id)
in (_129_987, typars, k, t, quals, rng))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_129_988)))
end
in (
# 1398 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_50_2619)::[] -> begin
(
# 1402 "FStar.Parser.Desugar.fst"
let trec = (FStar_List.hd tcs)
in (
# 1403 "FStar.Parser.Desugar.fst"
let _50_2625 = (tycon_record_as_variant trec)
in (match (_50_2625) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _50_2629::_50_2627 -> begin
(
# 1407 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1408 "FStar.Parser.Desugar.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (
# 1409 "FStar.Parser.Desugar.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1410 "FStar.Parser.Desugar.fst"
let _50_2640 = et
in (match (_50_2640) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_50_2642) -> begin
(
# 1413 "FStar.Parser.Desugar.fst"
let trec = tc
in (
# 1414 "FStar.Parser.Desugar.fst"
let _50_2647 = (tycon_record_as_variant trec)
in (match (_50_2647) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1417 "FStar.Parser.Desugar.fst"
let _50_2659 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_50_2659) with
| (env, _50_2656, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1420 "FStar.Parser.Desugar.fst"
let _50_2671 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_50_2671) with
| (env, _50_2668, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _50_2673 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1423 "FStar.Parser.Desugar.fst"
let _50_2676 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_50_2676) with
| (env, tcs) -> begin
(
# 1424 "FStar.Parser.Desugar.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1425 "FStar.Parser.Desugar.fst"
let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _50_26 -> (match (_50_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _50_2683, _50_2685, _50_2687, _50_2689), t, quals) -> begin
(
# 1427 "FStar.Parser.Desugar.fst"
let env_tps = (push_tparams env tpars)
in (
# 1428 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _50_2703, tags, _50_2706), constrs, tconstr, quals) -> begin
(
# 1432 "FStar.Parser.Desugar.fst"
let tycon = (tname, tpars, k)
in (
# 1433 "FStar.Parser.Desugar.fst"
let env_tps = (push_tparams env tpars)
in (
# 1434 "FStar.Parser.Desugar.fst"
let _50_2737 = (let _129_1004 = (FStar_All.pipe_right constrs (FStar_List.map (fun _50_2719 -> (match (_50_2719) with
| (id, topt, of_notation) -> begin
(
# 1436 "FStar.Parser.Desugar.fst"
let t = if of_notation then begin
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
in (
# 1444 "FStar.Parser.Desugar.fst"
let t = (let _129_999 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _129_998 = (close env_tps t)
in (desugar_typ _129_999 _129_998)))
in (
# 1445 "FStar.Parser.Desugar.fst"
let name = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1446 "FStar.Parser.Desugar.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _50_25 -> (match (_50_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _50_2733 -> begin
[]
end))))
in (let _129_1003 = (let _129_1002 = (let _129_1001 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in (name, _129_1001, tycon, quals, mutuals, rng))
in FStar_Absyn_Syntax.Sig_datacon (_129_1002))
in (name, _129_1003))))))
end))))
in (FStar_All.pipe_left FStar_List.split _129_1004))
in (match (_50_2737) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _50_2739 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1452 "FStar.Parser.Desugar.fst"
let bundle = (let _129_1006 = (let _129_1005 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _129_1005, rng))
in FStar_Absyn_Syntax.Sig_bundle (_129_1006))
in (
# 1453 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (
# 1454 "FStar.Parser.Desugar.fst"
let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (
# 1455 "FStar.Parser.Desugar.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _50_27 -> (match (_50_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _50_2749, constrs, quals, _50_2753) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _50_2757 -> begin
[]
end))))
in (
# 1459 "FStar.Parser.Desugar.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1460 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end)))))))))))

# 1465 "FStar.Parser.Desugar.fst"
let desugar_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.binder Prims.list) = (fun env binders -> (
# 1466 "FStar.Parser.Desugar.fst"
let _50_2788 = (FStar_List.fold_left (fun _50_2766 b -> (match (_50_2766) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1469 "FStar.Parser.Desugar.fst"
let _50_2775 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_50_2775) with
| (env, a) -> begin
(let _129_1015 = (let _129_1014 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_129_1014)::binders)
in (env, _129_1015))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1473 "FStar.Parser.Desugar.fst"
let _50_2783 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_50_2783) with
| (env, x) -> begin
(let _129_1017 = (let _129_1016 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_129_1016)::binders)
in (env, _129_1017))
end))
end
| _50_2785 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_50_2788) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1479 "FStar.Parser.Desugar.fst"
let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Absyn_Syntax.qualifier = (fun r _50_28 -> (match (_50_28) with
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
| (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Irreducible) | (FStar_Parser_AST.Unfoldable) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("This qualifier is supported only with the --universes option", r))))
end))

# 1493 "FStar.Parser.Desugar.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _50_29 -> (match (_50_29) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Absyn_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Absyn_Syntax.ResetOptions
end))

# 1497 "FStar.Parser.Desugar.fst"
let trans_quals : FStar_Range.range  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun r -> (FStar_List.map (trans_qual r)))

# 1499 "FStar.Parser.Desugar.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env d -> (
# 1500 "FStar.Parser.Desugar.fst"
let trans_quals = (trans_quals d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1503 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.TopLevelModule (_50_2815) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1510 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _129_1035 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in (_129_1035, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _129_1036 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _129_1036 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _129_1038 = (let _129_1037 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _129_1037))
in _129_1038.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _50_2835) -> begin
(
# 1522 "FStar.Parser.Desugar.fst"
let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _50_2842 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1525 "FStar.Parser.Desugar.fst"
let quals = (match (quals) with
| _50_2847::_50_2845 -> begin
(trans_quals quals)
end
| _50_2850 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _50_30 -> (match (_50_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_50_2859); FStar_Absyn_Syntax.lbtyp = _50_2857; FStar_Absyn_Syntax.lbeff = _50_2855; FStar_Absyn_Syntax.lbdef = _50_2853} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _50_2867; FStar_Absyn_Syntax.lbeff = _50_2865; FStar_Absyn_Syntax.lbdef = _50_2863} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (
# 1530 "FStar.Parser.Desugar.fst"
let s = FStar_Absyn_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (
# 1531 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _50_2875 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1537 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env t)
in (
# 1538 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1542 "FStar.Parser.Desugar.fst"
let f = (desugar_formula env t)
in (let _129_1044 = (let _129_1043 = (let _129_1042 = (let _129_1041 = (FStar_Parser_DesugarEnv.qualify env id)
in (_129_1041, f, (FStar_Absyn_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_assume (_129_1042))
in (_129_1043)::[])
in (env, _129_1044)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1546 "FStar.Parser.Desugar.fst"
let t = (let _129_1045 = (close_fun env t)
in (desugar_typ env _129_1045))
in (
# 1547 "FStar.Parser.Desugar.fst"
let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _129_1046 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_129_1046)
end else begin
(trans_quals quals)
end
in (
# 1548 "FStar.Parser.Desugar.fst"
let se = (let _129_1048 = (let _129_1047 = (FStar_Parser_DesugarEnv.qualify env id)
in (_129_1047, t, quals, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_val_decl (_129_1048))
in (
# 1549 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1553 "FStar.Parser.Desugar.fst"
let t = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (
# 1554 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1555 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1556 "FStar.Parser.Desugar.fst"
let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1557 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (
# 1558 "FStar.Parser.Desugar.fst"
let data_ops = (mk_data_projectors env se)
in (
# 1559 "FStar.Parser.Desugar.fst"
let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (
# 1560 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1564 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env term)
in (
# 1565 "FStar.Parser.Desugar.fst"
let t = (let _129_1053 = (let _129_1052 = (let _129_1049 = (FStar_Absyn_Syntax.null_v_binder t)
in (_129_1049)::[])
in (let _129_1051 = (let _129_1050 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _129_1050))
in (_129_1052, _129_1051)))
in (FStar_Absyn_Syntax.mk_Typ_fun _129_1053 None d.FStar_Parser_AST.drange))
in (
# 1566 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1567 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1568 "FStar.Parser.Desugar.fst"
let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1569 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (
# 1570 "FStar.Parser.Desugar.fst"
let data_ops = (mk_data_projectors env se)
in (
# 1571 "FStar.Parser.Desugar.fst"
let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (
# 1572 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1576 "FStar.Parser.Desugar.fst"
let _50_2928 = (desugar_binders env binders)
in (match (_50_2928) with
| (env_k, binders) -> begin
(
# 1577 "FStar.Parser.Desugar.fst"
let k = (desugar_kind env_k k)
in (
# 1578 "FStar.Parser.Desugar.fst"
let name = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1579 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((name, binders, k, d.FStar_Parser_AST.drange))
in (
# 1580 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1584 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1585 "FStar.Parser.Desugar.fst"
let _50_2944 = (desugar_binders env eff_binders)
in (match (_50_2944) with
| (env, binders) -> begin
(
# 1586 "FStar.Parser.Desugar.fst"
let defn = (desugar_typ env defn)
in (
# 1587 "FStar.Parser.Desugar.fst"
let _50_2948 = (FStar_Absyn_Util.head_and_args defn)
in (match (_50_2948) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _129_1058 = (let _129_1057 = (let _129_1056 = (let _129_1055 = (let _129_1054 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat "Effect " _129_1054))
in (Prims.strcat _129_1055 " not found"))
in (_129_1056, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_129_1057))
in (Prims.raise _129_1058))
end
| Some (ed) -> begin
(
# 1593 "FStar.Parser.Desugar.fst"
let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (
# 1594 "FStar.Parser.Desugar.fst"
let sub = (FStar_Absyn_Util.subst_typ subst)
in (
# 1595 "FStar.Parser.Desugar.fst"
let ed = (let _129_1076 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _129_1075 = (trans_quals quals)
in (let _129_1074 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _129_1073 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _129_1072 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _129_1071 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _129_1070 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _129_1069 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _129_1068 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _129_1067 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _129_1066 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _129_1065 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _129_1064 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _129_1063 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _129_1062 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _129_1061 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _129_1060 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _129_1076; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _129_1075; FStar_Absyn_Syntax.signature = _129_1074; FStar_Absyn_Syntax.ret = _129_1073; FStar_Absyn_Syntax.bind_wp = _129_1072; FStar_Absyn_Syntax.bind_wlp = _129_1071; FStar_Absyn_Syntax.if_then_else = _129_1070; FStar_Absyn_Syntax.ite_wp = _129_1069; FStar_Absyn_Syntax.ite_wlp = _129_1068; FStar_Absyn_Syntax.wp_binop = _129_1067; FStar_Absyn_Syntax.wp_as_type = _129_1066; FStar_Absyn_Syntax.close_wp = _129_1065; FStar_Absyn_Syntax.close_wp_t = _129_1064; FStar_Absyn_Syntax.assert_p = _129_1063; FStar_Absyn_Syntax.assume_p = _129_1062; FStar_Absyn_Syntax.null_wp = _129_1061; FStar_Absyn_Syntax.trivial = _129_1060})))))))))))))))))
in (
# 1615 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1616 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _50_2960 -> begin
(let _129_1080 = (let _129_1079 = (let _129_1078 = (let _129_1077 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _129_1077 " is not an effect"))
in (_129_1078, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_129_1079))
in (Prims.raise _129_1080))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1623 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1624 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (
# 1625 "FStar.Parser.Desugar.fst"
let _50_2974 = (desugar_binders env eff_binders)
in (match (_50_2974) with
| (env, binders) -> begin
(
# 1626 "FStar.Parser.Desugar.fst"
let eff_k = (desugar_kind env eff_kind)
in (
# 1627 "FStar.Parser.Desugar.fst"
let _50_2985 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _50_2978 decl -> (match (_50_2978) with
| (env, out) -> begin
(
# 1628 "FStar.Parser.Desugar.fst"
let _50_2982 = (desugar_decl env decl)
in (match (_50_2982) with
| (env, ses) -> begin
(let _129_1084 = (let _129_1083 = (FStar_List.hd ses)
in (_129_1083)::out)
in (env, _129_1084))
end))
end)) (env, [])))
in (match (_50_2985) with
| (env, decls) -> begin
(
# 1630 "FStar.Parser.Desugar.fst"
let decls = (FStar_List.rev decls)
in (
# 1631 "FStar.Parser.Desugar.fst"
let lookup = (fun s -> (match ((let _129_1088 = (let _129_1087 = (FStar_Absyn_Syntax.mk_ident (s, d.FStar_Parser_AST.drange))
in (FStar_Parser_DesugarEnv.qualify env _129_1087))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _129_1088))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat (Prims.strcat "Monad " eff_name.FStar_Ident.idText) " expects definition of ") s), d.FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (
# 1634 "FStar.Parser.Desugar.fst"
let ed = (let _129_1104 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _129_1103 = (trans_quals quals)
in (let _129_1102 = (lookup "return")
in (let _129_1101 = (lookup "bind_wp")
in (let _129_1100 = (lookup "bind_wlp")
in (let _129_1099 = (lookup "if_then_else")
in (let _129_1098 = (lookup "ite_wp")
in (let _129_1097 = (lookup "ite_wlp")
in (let _129_1096 = (lookup "wp_binop")
in (let _129_1095 = (lookup "wp_as_type")
in (let _129_1094 = (lookup "close_wp")
in (let _129_1093 = (lookup "close_wp_t")
in (let _129_1092 = (lookup "assert_p")
in (let _129_1091 = (lookup "assume_p")
in (let _129_1090 = (lookup "null_wp")
in (let _129_1089 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _129_1104; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _129_1103; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _129_1102; FStar_Absyn_Syntax.bind_wp = _129_1101; FStar_Absyn_Syntax.bind_wlp = _129_1100; FStar_Absyn_Syntax.if_then_else = _129_1099; FStar_Absyn_Syntax.ite_wp = _129_1098; FStar_Absyn_Syntax.ite_wlp = _129_1097; FStar_Absyn_Syntax.wp_binop = _129_1096; FStar_Absyn_Syntax.wp_as_type = _129_1095; FStar_Absyn_Syntax.close_wp = _129_1094; FStar_Absyn_Syntax.close_wp_t = _129_1093; FStar_Absyn_Syntax.assert_p = _129_1092; FStar_Absyn_Syntax.assume_p = _129_1091; FStar_Absyn_Syntax.null_wp = _129_1090; FStar_Absyn_Syntax.trivial = _129_1089}))))))))))))))))
in (
# 1654 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1655 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1659 "FStar.Parser.Desugar.fst"
let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _129_1111 = (let _129_1110 = (let _129_1109 = (let _129_1108 = (let _129_1107 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Effect name " _129_1107))
in (Prims.strcat _129_1108 " not found"))
in (_129_1109, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_129_1110))
in (Prims.raise _129_1111))
end
| Some (l) -> begin
l
end))
in (
# 1662 "FStar.Parser.Desugar.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1663 "FStar.Parser.Desugar.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1664 "FStar.Parser.Desugar.fst"
let lift = (desugar_typ env l.FStar_Parser_AST.lift_op)
in (
# 1665 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_sub_effect (({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))

# 1668 "FStar.Parser.Desugar.fst"
let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _50_3010 d -> (match (_50_3010) with
| (env, sigelts) -> begin
(
# 1670 "FStar.Parser.Desugar.fst"
let _50_3014 = (desugar_decl env d)
in (match (_50_3014) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1673 "FStar.Parser.Desugar.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]

# 1680 "FStar.Parser.Desugar.fst"
let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1681 "FStar.Parser.Desugar.fst"
let open_ns = (fun mname d -> (
# 1682 "FStar.Parser.Desugar.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _129_1131 = (let _129_1130 = (let _129_1128 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_129_1128))
in (let _129_1129 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _129_1130 _129_1129)))
in (_129_1131)::d)
end else begin
d
end
in d))
in (
# 1686 "FStar.Parser.Desugar.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (
# 1689 "FStar.Parser.Desugar.fst"
let _50_3041 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _129_1133 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _129_1132 = (open_ns mname decls)
in (_129_1133, mname, _129_1132, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _129_1135 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _129_1134 = (open_ns mname decls)
in (_129_1135, mname, _129_1134, false)))
end)
in (match (_50_3041) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1694 "FStar.Parser.Desugar.fst"
let _50_3044 = (desugar_decls env decls)
in (match (_50_3044) with
| (env, sigelts) -> begin
(
# 1695 "FStar.Parser.Desugar.fst"
let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul, pop_when_done))
end))
end)))))

# 1704 "FStar.Parser.Desugar.fst"
let desugar_partial_modul : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun curmod env m -> (
# 1705 "FStar.Parser.Desugar.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _50_3055, _50_3057) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1712 "FStar.Parser.Desugar.fst"
let _50_3065 = (desugar_modul_common curmod env m)
in (match (_50_3065) with
| (x, y, _50_3064) -> begin
(x, y)
end))))

# 1715 "FStar.Parser.Desugar.fst"
let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (
# 1716 "FStar.Parser.Desugar.fst"
let _50_3071 = (desugar_modul_common None env m)
in (match (_50_3071) with
| (env, modul, pop_when_done) -> begin
(
# 1717 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (
# 1718 "FStar.Parser.Desugar.fst"
let _50_3073 = if (FStar_Options.should_dump modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _129_1146 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _129_1146))
end else begin
()
end
in (let _129_1147 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in (_129_1147, modul))))
end)))

# 1721 "FStar.Parser.Desugar.fst"
let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (
# 1722 "FStar.Parser.Desugar.fst"
let _50_3086 = (FStar_List.fold_left (fun _50_3079 m -> (match (_50_3079) with
| (env, mods) -> begin
(
# 1723 "FStar.Parser.Desugar.fst"
let _50_3083 = (desugar_modul env m)
in (match (_50_3083) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_50_3086) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1727 "FStar.Parser.Desugar.fst"
let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (
# 1728 "FStar.Parser.Desugar.fst"
let _50_3091 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_50_3091) with
| (en, pop_when_done) -> begin
(
# 1729 "FStar.Parser.Desugar.fst"
let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (
# 1729 "FStar.Parser.Desugar.fst"
let _50_3092 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _50_3092.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _50_3092.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _50_3092.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _50_3092.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _50_3092.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _50_3092.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _50_3092.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _50_3092.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _50_3092.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _50_3092.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _50_3092.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (
# 1730 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))





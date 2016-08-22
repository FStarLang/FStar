
open Prims
# 33 "FStar.Parser.Desugar.fst"
let imp_tag : FStar_Absyn_Syntax.arg_qualifier = FStar_Absyn_Syntax.Implicit (false)

# 35 "FStar.Parser.Desugar.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _61_1 -> (match (_61_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (imp_tag)
end
| _61_36 -> begin
None
end))

# 39 "FStar.Parser.Desugar.fst"
let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))

# 41 "FStar.Parser.Desugar.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (imp_tag)))
end
| _61_43 -> begin
((t), (None))
end))

# 45 "FStar.Parser.Desugar.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_61_47) -> begin
true
end
| _61_50 -> begin
false
end)))))

# 50 "FStar.Parser.Desugar.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _61_55 -> begin
t
end))

# 54 "FStar.Parser.Desugar.fst"
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

# 58 "FStar.Parser.Desugar.fst"
let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _153_17 = (let _153_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_153_16))
in (FStar_Parser_AST.mk_term _153_17 r FStar_Parser_AST.Kind)))

# 60 "FStar.Parser.Desugar.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 64 "FStar.Parser.Desugar.fst"
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
# 83 "FStar.Parser.Desugar.fst"
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

# 87 "FStar.Parser.Desugar.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _153_40 = (let _153_39 = (let _153_38 = (let _153_37 = (compile_op n s)
in ((_153_37), (r)))
in (FStar_Absyn_Syntax.mk_ident _153_38))
in (_153_39)::[])
in (FStar_All.pipe_right _153_40 FStar_Absyn_Syntax.lid_of_ids)))

# 89 "FStar.Parser.Desugar.fst"
let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 92 "FStar.Parser.Desugar.fst"
let r = (fun l -> (let _153_51 = (FStar_Ident.set_lid_range l rng)
in Some (_153_51)))
in (
# 93 "FStar.Parser.Desugar.fst"
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

# 119 "FStar.Parser.Desugar.fst"
let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 122 "FStar.Parser.Desugar.fst"
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

# 136 "FStar.Parser.Desugar.fst"
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
# 179 "FStar.Parser.Desugar.fst"
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
# 186 "FStar.Parser.Desugar.fst"
let _61_331 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_61_331) with
| (env, _61_330) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(
# 189 "FStar.Parser.Desugar.fst"
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

# 213 "FStar.Parser.Desugar.fst"
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

# 228 "FStar.Parser.Desugar.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _153_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _153_92)))

# 232 "FStar.Parser.Desugar.fst"
let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_61_467) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 237 "FStar.Parser.Desugar.fst"
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
# 242 "FStar.Parser.Desugar.fst"
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
# 271 "FStar.Parser.Desugar.fst"
let _61_558 = (free_type_vars_b env b)
in (match (_61_558) with
| (env, f) -> begin
(let _153_107 = (free_type_vars env t)
in (FStar_List.append f _153_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 276 "FStar.Parser.Desugar.fst"
let _61_574 = (FStar_List.fold_left (fun _61_567 binder -> (match (_61_567) with
| (env, free) -> begin
(
# 277 "FStar.Parser.Desugar.fst"
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
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Assign (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 294 "FStar.Parser.Desugar.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 297 "FStar.Parser.Desugar.fst"
let rec aux = (fun args t -> (match ((let _153_117 = (unparen t)
in _153_117.FStar_Parser_AST.tm)) with
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

# 301 "FStar.Parser.Desugar.fst"
let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 304 "FStar.Parser.Desugar.fst"
let ftv = (let _153_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _153_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 307 "FStar.Parser.Desugar.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _153_126 = (let _153_125 = (let _153_124 = (kind_star x.FStar_Ident.idRange)
in ((x), (_153_124)))
in FStar_Parser_AST.TAnnotated (_153_125))
in (FStar_Parser_AST.mk_binder _153_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 308 "FStar.Parser.Desugar.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 309 "FStar.Parser.Desugar.fst"
let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 312 "FStar.Parser.Desugar.fst"
let ftv = (let _153_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _153_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 315 "FStar.Parser.Desugar.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _153_135 = (let _153_134 = (let _153_133 = (kind_star x.FStar_Ident.idRange)
in ((x), (_153_133)))
in FStar_Parser_AST.TAnnotated (_153_134))
in (FStar_Parser_AST.mk_binder _153_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 316 "FStar.Parser.Desugar.fst"
let t = (match ((let _153_136 = (unlabel t)
in _153_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_61_640) -> begin
t
end
| _61_643 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 319 "FStar.Parser.Desugar.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 320 "FStar.Parser.Desugar.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _61_653 -> begin
((bs), (t))
end))

# 324 "FStar.Parser.Desugar.fst"
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

# 329 "FStar.Parser.Desugar.fst"
let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 333 "FStar.Parser.Desugar.fst"
let _61_683 = (destruct_app_pattern env is_top_level p)
in (match (_61_683) with
| (name, args, _61_682) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_688); FStar_Parser_AST.prange = _61_685}, args) when is_top_level -> begin
(let _153_150 = (let _153_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_153_149))
in ((_153_150), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_699); FStar_Parser_AST.prange = _61_696}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _61_707 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 340 "FStar.Parser.Desugar.fst"
type bnd =
| TBinder of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual)
| VBinder of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)

# 343 "FStar.Parser.Desugar.fst"
let is_TBinder = (fun _discr_ -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 344 "FStar.Parser.Desugar.fst"
let is_VBinder = (fun _discr_ -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 345 "FStar.Parser.Desugar.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 343 "FStar.Parser.Desugar.fst"
let ___TBinder____0 = (fun projectee -> (match (projectee) with
| TBinder (_61_710) -> begin
_61_710
end))

# 344 "FStar.Parser.Desugar.fst"
let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_61_713) -> begin
_61_713
end))

# 345 "FStar.Parser.Desugar.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_61_716) -> begin
_61_716
end))

# 345 "FStar.Parser.Desugar.fst"
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

# 349 "FStar.Parser.Desugar.fst"
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

# 353 "FStar.Parser.Desugar.fst"
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
# 358 "FStar.Parser.Desugar.fst"
let _61_755 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_755) with
| (env, a) -> begin
((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual imp)))), (env))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 361 "FStar.Parser.Desugar.fst"
let _61_763 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_763) with
| (env, x) -> begin
((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), ((trans_aqual imp)))), (env))
end))
end))

# 362 "FStar.Parser.Desugar.fst"
type env_t =
FStar_Parser_DesugarEnv.env

# 364 "FStar.Parser.Desugar.fst"
type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list

# 365 "FStar.Parser.Desugar.fst"
let label_conjuncts : Prims.string  ->  Prims.bool  ->  Prims.string Prims.option  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun tag polarity label_opt f -> (
# 368 "FStar.Parser.Desugar.fst"
let label = (fun f -> (
# 369 "FStar.Parser.Desugar.fst"
let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _61_773 -> begin
(let _153_215 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _153_215))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (((f), (msg), (polarity)))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (
# 375 "FStar.Parser.Desugar.fst"
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
| _61_795 -> begin
(label f)
end))
in (aux f))))

# 391 "FStar.Parser.Desugar.fst"
let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _61_799 -> (match (_61_799) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))

# 393 "FStar.Parser.Desugar.fst"
let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (
# 396 "FStar.Parser.Desugar.fst"
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
# 400 "FStar.Parser.Desugar.fst"
let _61_818 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_61_818) with
| (e, x) -> begin
(((FStar_Util.Inr (x))::l), (e), (x))
end))
end))
in (
# 402 "FStar.Parser.Desugar.fst"
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
# 406 "FStar.Parser.Desugar.fst"
let _61_835 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_61_835) with
| (e, a) -> begin
(((FStar_Util.Inl (a))::l), (e), (a))
end))
end))
in (
# 408 "FStar.Parser.Desugar.fst"
let rec aux = (fun loc env p -> (
# 409 "FStar.Parser.Desugar.fst"
let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p.FStar_Parser_AST.prange))
in (
# 410 "FStar.Parser.Desugar.fst"
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
# 415 "FStar.Parser.Desugar.fst"
let _61_860 = (aux loc env p)
in (match (_61_860) with
| (loc, env, var, p, _61_859) -> begin
(
# 416 "FStar.Parser.Desugar.fst"
let _61_877 = (FStar_List.fold_left (fun _61_864 p -> (match (_61_864) with
| (loc, env, ps) -> begin
(
# 417 "FStar.Parser.Desugar.fst"
let _61_873 = (aux loc env p)
in (match (_61_873) with
| (loc, env, _61_869, p, _61_872) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_61_877) with
| (loc, env, ps) -> begin
(
# 419 "FStar.Parser.Desugar.fst"
let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (
# 420 "FStar.Parser.Desugar.fst"
let _61_879 = (let _153_304 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _153_304))
in ((loc), (env), (var), (pat), (false))))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 424 "FStar.Parser.Desugar.fst"
let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_61_886) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(
# 427 "FStar.Parser.Desugar.fst"
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
# 430 "FStar.Parser.Desugar.fst"
let _61_902 = (aux loc env p)
in (match (_61_902) with
| (loc, env', binder, p, imp) -> begin
(
# 431 "FStar.Parser.Desugar.fst"
let binder = (match (binder) with
| LetBinder (_61_904) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _61_908, aq) -> begin
(let _153_306 = (let _153_305 = (desugar_kind env t)
in ((x), (_153_305), (aq)))
in TBinder (_153_306))
end
| VBinder (x, _61_914, aq) -> begin
(
# 435 "FStar.Parser.Desugar.fst"
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
# 440 "FStar.Parser.Desugar.fst"
let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (
# 441 "FStar.Parser.Desugar.fst"
let aq = (trans_aqual aq)
in if (a.FStar_Ident.idText = "\'_") then begin
(
# 443 "FStar.Parser.Desugar.fst"
let a = (FStar_All.pipe_left FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((a), (FStar_Absyn_Syntax.kun), (aq)))), (_153_309), (imp))))
end else begin
(
# 445 "FStar.Parser.Desugar.fst"
let _61_930 = (resolvea loc env a)
in (match (_61_930) with
| (loc, env, abvd) -> begin
(let _153_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in ((loc), (env), (TBinder (((abvd), (FStar_Absyn_Syntax.kun), (aq)))), (_153_310), (imp)))
end))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 449 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (
# 450 "FStar.Parser.Desugar.fst"
let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_311), (false)))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 454 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_312), (false))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(
# 458 "FStar.Parser.Desugar.fst"
let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (
# 459 "FStar.Parser.Desugar.fst"
let aq = (trans_aqual aq)
in (
# 460 "FStar.Parser.Desugar.fst"
let _61_946 = (resolvex loc env x)
in (match (_61_946) with
| (loc, env, xbvd) -> begin
(let _153_313 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in ((loc), (env), (VBinder (((xbvd), (FStar_Absyn_Syntax.tun), (aq)))), (_153_313), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 464 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (
# 465 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_314 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), ([])))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_314), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _61_952}, args) -> begin
(
# 469 "FStar.Parser.Desugar.fst"
let _61_974 = (FStar_List.fold_right (fun arg _61_963 -> (match (_61_963) with
| (loc, env, args) -> begin
(
# 470 "FStar.Parser.Desugar.fst"
let _61_970 = (aux loc env arg)
in (match (_61_970) with
| (loc, env, _61_967, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_61_974) with
| (loc, env, args) -> begin
(
# 472 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (
# 473 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _153_317 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons (((l), (Some (FStar_Absyn_Syntax.Data_ctor)), (args)))))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (_153_317), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_61_978) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 479 "FStar.Parser.Desugar.fst"
let _61_998 = (FStar_List.fold_right (fun pat _61_986 -> (match (_61_986) with
| (loc, env, pats) -> begin
(
# 480 "FStar.Parser.Desugar.fst"
let _61_994 = (aux loc env pat)
in (match (_61_994) with
| (loc, env, _61_990, pat, _61_993) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_61_998) with
| (loc, env, pats) -> begin
(
# 482 "FStar.Parser.Desugar.fst"
let pat = (let _153_324 = (let _153_323 = (let _153_322 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _153_322))
in (FStar_All.pipe_left _153_323 (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ([]))))))
in (FStar_List.fold_right (fun hd tl -> (
# 483 "FStar.Parser.Desugar.fst"
let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((hd), (false)))::(((tl), (false)))::[]))))))) pats _153_324))
in (
# 486 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in ((loc), (env), (VBinder (((x), (FStar_Absyn_Syntax.tun), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 490 "FStar.Parser.Desugar.fst"
let _61_1024 = (FStar_List.fold_left (fun _61_1011 p -> (match (_61_1011) with
| (loc, env, pats) -> begin
(
# 491 "FStar.Parser.Desugar.fst"
let _61_1020 = (aux loc env p)
in (match (_61_1020) with
| (loc, env, _61_1016, pat, _61_1019) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_61_1024) with
| (loc, env, args) -> begin
(
# 493 "FStar.Parser.Desugar.fst"
let args = (FStar_List.rev args)
in (
# 494 "FStar.Parser.Desugar.fst"
let l = if dep then begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 496 "FStar.Parser.Desugar.fst"
let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (
# 497 "FStar.Parser.Desugar.fst"
let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _61_1030) -> begin
v
end
| _61_1034 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 500 "FStar.Parser.Desugar.fst"
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
# 507 "FStar.Parser.Desugar.fst"
let _61_1044 = (FStar_List.hd fields)
in (match (_61_1044) with
| (f, _61_1043) -> begin
(
# 508 "FStar.Parser.Desugar.fst"
let _61_1048 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_61_1048) with
| (record, _61_1047) -> begin
(
# 509 "FStar.Parser.Desugar.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _61_1051 -> (match (_61_1051) with
| (f, p) -> begin
(let _153_329 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in ((_153_329), (p)))
end))))
in (
# 511 "FStar.Parser.Desugar.fst"
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
# 515 "FStar.Parser.Desugar.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (
# 516 "FStar.Parser.Desugar.fst"
let _61_1075 = (aux loc env app)
in (match (_61_1075) with
| (env, e, b, p, _61_1074) -> begin
(
# 517 "FStar.Parser.Desugar.fst"
let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _61_1078, args) -> begin
(let _153_337 = (let _153_336 = (let _153_335 = (let _153_334 = (let _153_333 = (let _153_332 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_DesugarEnv.typename), (_153_332)))
in FStar_Absyn_Syntax.Record_ctor (_153_333))
in Some (_153_334))
in ((fv), (_153_335), (args)))
in FStar_Absyn_Syntax.Pat_cons (_153_336))
in (FStar_All.pipe_left pos _153_337))
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
# 522 "FStar.Parser.Desugar.fst"
let _61_1092 = (aux [] env p)
in (match (_61_1092) with
| (_61_1086, env, b, p, _61_1091) -> begin
((env), (b), (p))
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _61_1098) -> begin
(let _153_343 = (let _153_342 = (let _153_341 = (FStar_Parser_DesugarEnv.qualify env x)
in ((_153_341), (FStar_Absyn_Syntax.tun)))
in LetBinder (_153_342))
in ((env), (_153_343), (None)))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _61_1105); FStar_Parser_AST.prange = _61_1102}, t) -> begin
(let _153_347 = (let _153_346 = (let _153_345 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _153_344 = (desugar_typ env t)
in ((_153_345), (_153_344))))
in LetBinder (_153_346))
in ((env), (_153_347), (None)))
end
| _61_1113 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(
# 533 "FStar.Parser.Desugar.fst"
let _61_1117 = (desugar_data_pat env p)
in (match (_61_1117) with
| (env, binder, p) -> begin
(
# 534 "FStar.Parser.Desugar.fst"
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
# 544 "FStar.Parser.Desugar.fst"
let _61_1140 = (desugar_data_pat env pat)
in (match (_61_1140) with
| (env, _61_1138, pat) -> begin
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
# 557 "FStar.Parser.Desugar.fst"
let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (
# 558 "FStar.Parser.Desugar.fst"
let setpos = (fun e -> (
# 558 "FStar.Parser.Desugar.fst"
let _61_1154 = e
in {FStar_Absyn_Syntax.n = _61_1154.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1154.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1154.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1154.FStar_Absyn_Syntax.uvs}))
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
# 566 "FStar.Parser.Desugar.fst"
let op = (FStar_Absyn_Util.fvar None l (FStar_Ident.range_of_lid l))
in (
# 567 "FStar.Parser.Desugar.fst"
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
# 582 "FStar.Parser.Desugar.fst"
let dt = (let _153_389 = (let _153_388 = (let _153_387 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in ((_153_387), (Some (FStar_Absyn_Syntax.Data_ctor))))
in (FStar_Absyn_Syntax.mk_Exp_fvar _153_388))
in (FStar_All.pipe_left pos _153_389))
in (match (args) with
| [] -> begin
dt
end
| _61_1181 -> begin
(
# 586 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _61_1184 -> (match (_61_1184) with
| (t, imp) -> begin
(
# 587 "FStar.Parser.Desugar.fst"
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
# 593 "FStar.Parser.Desugar.fst"
let _61_1221 = (FStar_List.fold_left (fun _61_1193 pat -> (match (_61_1193) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _61_1196}, t) -> begin
(
# 596 "FStar.Parser.Desugar.fst"
let ftvs = (let _153_397 = (free_type_vars env t)
in (FStar_List.append _153_397 ftvs))
in (let _153_399 = (let _153_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _153_398))
in ((_153_399), (ftvs))))
end
| FStar_Parser_AST.PatTvar (a, _61_1208) -> begin
(let _153_401 = (let _153_400 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _153_400))
in ((_153_401), (ftvs)))
end
| FStar_Parser_AST.PatAscribed (_61_1212, t) -> begin
(let _153_403 = (let _153_402 = (free_type_vars env t)
in (FStar_List.append _153_402 ftvs))
in ((env), (_153_403)))
end
| _61_1217 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_61_1221) with
| (_61_1219, ftv) -> begin
(
# 601 "FStar.Parser.Desugar.fst"
let ftv = (sort_ftv ftv)
in (
# 602 "FStar.Parser.Desugar.fst"
let binders = (let _153_405 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _153_405 binders))
in (
# 604 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs sc_pat_opt _61_8 -> (match (_61_8) with
| [] -> begin
(
# 606 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env body)
in (
# 607 "FStar.Parser.Desugar.fst"
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
# 613 "FStar.Parser.Desugar.fst"
let _61_1244 = (desugar_binding_pat env p)
in (match (_61_1244) with
| (env, b, pat) -> begin
(
# 614 "FStar.Parser.Desugar.fst"
let _61_1304 = (match (b) with
| LetBinder (_61_1246) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _153_414 = (binder_of_bnd b)
in ((_153_414), (sc_pat_opt)))
end
| VBinder (x, t, aq) -> begin
(
# 618 "FStar.Parser.Desugar.fst"
let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (
# 619 "FStar.Parser.Desugar.fst"
let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _61_1261) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _153_416 = (let _153_415 = (FStar_Absyn_Util.bvar_to_exp b)
in ((_153_415), (p)))
in Some (_153_416))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Absyn_Syntax.n), (p'.FStar_Absyn_Syntax.v))) with
| (FStar_Absyn_Syntax.Exp_bvar (_61_1275), _61_1278) -> begin
(
# 625 "FStar.Parser.Desugar.fst"
let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (
# 626 "FStar.Parser.Desugar.fst"
let sc = (let _153_423 = (let _153_422 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _153_421 = (let _153_420 = (FStar_Absyn_Syntax.varg sc)
in (let _153_419 = (let _153_418 = (let _153_417 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _153_417))
in (_153_418)::[])
in (_153_420)::_153_419))
in ((_153_422), (_153_421))))
in (FStar_Absyn_Syntax.mk_Exp_app _153_423 None top.FStar_Parser_AST.range))
in (
# 627 "FStar.Parser.Desugar.fst"
let p = (let _153_424 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((((p'), (false)))::(((p), (false)))::[])))) None _153_424))
in Some (((sc), (p))))))
end
| (FStar_Absyn_Syntax.Exp_app (_61_1284, args), FStar_Absyn_Syntax.Pat_cons (_61_1289, _61_1291, pats)) -> begin
(
# 630 "FStar.Parser.Desugar.fst"
let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (
# 631 "FStar.Parser.Desugar.fst"
let sc = (let _153_430 = (let _153_429 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _153_428 = (let _153_427 = (let _153_426 = (let _153_425 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _153_425))
in (_153_426)::[])
in (FStar_List.append args _153_427))
in ((_153_429), (_153_428))))
in (FStar_Absyn_Syntax.mk_Exp_app _153_430 None top.FStar_Parser_AST.range))
in (
# 632 "FStar.Parser.Desugar.fst"
let p = (let _153_431 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv tup)), (Some (FStar_Absyn_Syntax.Data_ctor)), ((FStar_List.append pats ((((p), (false)))::[])))))) None _153_431))
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
# 643 "FStar.Parser.Desugar.fst"
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
| FStar_Parser_AST.App (_61_1319) -> begin
(
# 649 "FStar.Parser.Desugar.fst"
let rec aux = (fun args e -> (match ((let _153_446 = (unparen e)
in _153_446.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 651 "FStar.Parser.Desugar.fst"
let arg = (let _153_447 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _153_447))
in (aux ((arg)::args) e))
end
| _61_1331 -> begin
(
# 654 "FStar.Parser.Desugar.fst"
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
| FStar_Parser_AST.LetOpen (_61_1338) -> begin
(FStar_All.failwith "let open in universes")
end
| FStar_Parser_AST.Let (is_rec, ((pat, _snd))::_tl, body) -> begin
(
# 666 "FStar.Parser.Desugar.fst"
let is_rec = (is_rec = FStar_Parser_AST.Rec)
in (
# 667 "FStar.Parser.Desugar.fst"
let ds_let_rec = (fun _61_1351 -> (match (()) with
| () -> begin
(
# 668 "FStar.Parser.Desugar.fst"
let bindings = (((pat), (_snd)))::_tl
in (
# 669 "FStar.Parser.Desugar.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _61_1355 -> (match (_61_1355) with
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
| _61_1361 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _61_1366); FStar_Parser_AST.prange = _61_1363}, t) -> begin
if top_level then begin
(let _153_461 = (let _153_460 = (let _153_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_153_459))
in ((_153_460), ([]), (Some (t))))
in ((_153_461), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _61_1375) -> begin
if top_level then begin
(let _153_464 = (let _153_463 = (let _153_462 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_153_462))
in ((_153_463), ([]), (None)))
in ((_153_464), (def)))
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
# 685 "FStar.Parser.Desugar.fst"
let _61_1405 = (FStar_List.fold_left (fun _61_1383 _61_1392 -> (match (((_61_1383), (_61_1392))) with
| ((env, fnames), ((f, _61_1386, _61_1388), _61_1391)) -> begin
(
# 687 "FStar.Parser.Desugar.fst"
let _61_1402 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 689 "FStar.Parser.Desugar.fst"
let _61_1397 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_1397) with
| (env, xx) -> begin
((env), (FStar_Util.Inl (xx)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _153_467 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in ((_153_467), (FStar_Util.Inr (l))))
end)
in (match (_61_1402) with
| (env, lbname) -> begin
((env), ((lbname)::fnames))
end))
end)) ((env), ([])) funs)
in (match (_61_1405) with
| (env', fnames) -> begin
(
# 694 "FStar.Parser.Desugar.fst"
let fnames = (FStar_List.rev fnames)
in (
# 695 "FStar.Parser.Desugar.fst"
let desugar_one_def = (fun env lbname _61_1416 -> (match (_61_1416) with
| ((_61_1411, args, result_t), def) -> begin
(
# 696 "FStar.Parser.Desugar.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _153_474 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _153_474 FStar_Parser_AST.Expr))
end)
in (
# 699 "FStar.Parser.Desugar.fst"
let def = (match (args) with
| [] -> begin
def
end
| _61_1423 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 702 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env def)
in (mk_lb ((lbname), (FStar_Absyn_Syntax.tun), (body))))))
end))
in (
# 704 "FStar.Parser.Desugar.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 705 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env' body)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((is_rec), (lbs))), (body))))))))
end))))
end))
in (
# 708 "FStar.Parser.Desugar.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 709 "FStar.Parser.Desugar.fst"
let t1 = (desugar_exp env t1)
in (
# 710 "FStar.Parser.Desugar.fst"
let _61_1436 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_61_1436) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_61_1438) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(
# 714 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((((false), (({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]))), (body)))))
end
| VBinder (x, t, _61_1448) -> begin
(
# 717 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env t2)
in (
# 718 "FStar.Parser.Desugar.fst"
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
# 735 "FStar.Parser.Desugar.fst"
let r = top.FStar_Parser_AST.range
in (
# 736 "FStar.Parser.Desugar.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 737 "FStar.Parser.Desugar.fst"
let body = (FStar_Parser_AST.mk_function (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r)), (None), (e)))::[]) r r)
in (
# 738 "FStar.Parser.Desugar.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Absyn_Const.try_with_lid)) r top.FStar_Parser_AST.level)), (body), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (
# 739 "FStar.Parser.Desugar.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((a1), (handler), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 743 "FStar.Parser.Desugar.fst"
let desugar_branch = (fun _61_1487 -> (match (_61_1487) with
| (pat, wopt, b) -> begin
(
# 744 "FStar.Parser.Desugar.fst"
let _61_1490 = (desugar_match_pat env pat)
in (match (_61_1490) with
| (env, pat) -> begin
(
# 745 "FStar.Parser.Desugar.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _153_502 = (desugar_exp env e)
in Some (_153_502))
end)
in (
# 748 "FStar.Parser.Desugar.fst"
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
| FStar_Parser_AST.Record (_61_1501, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 759 "FStar.Parser.Desugar.fst"
let _61_1512 = (FStar_List.hd fields)
in (match (_61_1512) with
| (f, _61_1511) -> begin
(
# 760 "FStar.Parser.Desugar.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 761 "FStar.Parser.Desugar.fst"
let _61_1518 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_61_1518) with
| (record, _61_1517) -> begin
(
# 762 "FStar.Parser.Desugar.fst"
let get_field = (fun xopt f -> (
# 763 "FStar.Parser.Desugar.fst"
let fn = f.FStar_Ident.ident
in (
# 764 "FStar.Parser.Desugar.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _61_1526 -> (match (_61_1526) with
| (g, _61_1525) -> begin
(
# 765 "FStar.Parser.Desugar.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_61_1530, e) -> begin
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
# 775 "FStar.Parser.Desugar.fst"
let recterm = (match (eopt) with
| None -> begin
(let _153_531 = (let _153_530 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _61_1542 -> (match (_61_1542) with
| (f, _61_1541) -> begin
(let _153_529 = (let _153_528 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _153_528))
in ((_153_529), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_DesugarEnv.constrname), (_153_530)))
in FStar_Parser_AST.Construct (_153_531))
end
| Some (e) -> begin
(
# 782 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (
# 783 "FStar.Parser.Desugar.fst"
let xterm = (let _153_533 = (let _153_532 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_153_532))
in (FStar_Parser_AST.mk_term _153_533 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 784 "FStar.Parser.Desugar.fst"
let record = (let _153_536 = (let _153_535 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _61_1550 -> (match (_61_1550) with
| (f, _61_1549) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_153_535)))
in FStar_Parser_AST.Record (_153_536))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (
# 787 "FStar.Parser.Desugar.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 788 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _61_1573); FStar_Absyn_Syntax.tk = _61_1570; FStar_Absyn_Syntax.pos = _61_1568; FStar_Absyn_Syntax.fvs = _61_1566; FStar_Absyn_Syntax.uvs = _61_1564}, args); FStar_Absyn_Syntax.tk = _61_1562; FStar_Absyn_Syntax.pos = _61_1560; FStar_Absyn_Syntax.fvs = _61_1558; FStar_Absyn_Syntax.uvs = _61_1556}, FStar_Absyn_Syntax.Data_app)) -> begin
(
# 791 "FStar.Parser.Desugar.fst"
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
| _61_1587 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 799 "FStar.Parser.Desugar.fst"
let _61_1594 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_61_1594) with
| (fieldname, is_rec) -> begin
(
# 800 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env e)
in (
# 801 "FStar.Parser.Desugar.fst"
let fn = (
# 802 "FStar.Parser.Desugar.fst"
let _61_1599 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_61_1599) with
| (ns, _61_1598) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 804 "FStar.Parser.Desugar.fst"
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
| _61_1605 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (
# 815 "FStar.Parser.Desugar.fst"
let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (
# 816 "FStar.Parser.Desugar.fst"
let setpos = (fun t -> (
# 816 "FStar.Parser.Desugar.fst"
let _61_1612 = t
in {FStar_Absyn_Syntax.n = _61_1612.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1612.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1612.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1612.FStar_Absyn_Syntax.uvs}))
in (
# 817 "FStar.Parser.Desugar.fst"
let top = (unparen top)
in (
# 818 "FStar.Parser.Desugar.fst"
let head_and_args = (fun t -> (
# 819 "FStar.Parser.Desugar.fst"
let rec aux = (fun args t -> (match ((let _153_576 = (unparen t)
in _153_576.FStar_Parser_AST.tm)) with
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
# 828 "FStar.Parser.Desugar.fst"
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
# 834 "FStar.Parser.Desugar.fst"
let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _153_578 = (desugar_exp env t)
in (FStar_All.pipe_right _153_578 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", (t1)::(_61_1644)::[]) -> begin
if (is_type env t1) then begin
(
# 840 "FStar.Parser.Desugar.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _153_581 = (flatten t1)
in (FStar_List.append _153_581 ((t2)::[])))
end
| _61_1658 -> begin
(t)::[]
end))
in (
# 844 "FStar.Parser.Desugar.fst"
let targs = (let _153_584 = (flatten top)
in (FStar_All.pipe_right _153_584 (FStar_List.map (fun t -> (let _153_583 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _153_583))))))
in (
# 845 "FStar.Parser.Desugar.fst"
let tup = (let _153_585 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _153_585))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))))
end else begin
(let _153_591 = (let _153_590 = (let _153_589 = (let _153_588 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _153_588))
in ((_153_589), (top.FStar_Parser_AST.range)))
in FStar_Absyn_Syntax.Error (_153_590))
in (Prims.raise _153_591))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _153_592 = (desugar_exp env top)
in (FStar_All.pipe_right _153_592 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(
# 856 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun t -> (let _153_594 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _153_594))) args)
in (let _153_595 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _153_595 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _153_596 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _153_596))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _153_597 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _153_597))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(
# 872 "FStar.Parser.Desugar.fst"
let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _153_598 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _153_598)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 876 "FStar.Parser.Desugar.fst"
let t = (let _153_599 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _153_599))
in (
# 877 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _61_1694 -> (match (_61_1694) with
| (t, imp) -> begin
(let _153_601 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _153_601))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 881 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _61_9 -> (match (_61_9) with
| [] -> begin
(
# 883 "FStar.Parser.Desugar.fst"
let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_List.rev bs)), (body)))))
end
| (hd)::tl -> begin
(
# 886 "FStar.Parser.Desugar.fst"
let _61_1712 = (desugar_binding_pat env hd)
in (match (_61_1712) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _153_613 = (let _153_612 = (let _153_611 = (let _153_610 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _153_610))
in ((_153_611), (hd.FStar_Parser_AST.prange)))
in FStar_Absyn_Syntax.Error (_153_612))
in (Prims.raise _153_613))
end
| None -> begin
(
# 890 "FStar.Parser.Desugar.fst"
let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_61_1718) -> begin
(
# 895 "FStar.Parser.Desugar.fst"
let rec aux = (fun args e -> (match ((let _153_618 = (unparen e)
in _153_618.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(
# 897 "FStar.Parser.Desugar.fst"
let arg = (let _153_619 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _153_619))
in (aux ((arg)::args) e))
end
| _61_1730 -> begin
(
# 900 "FStar.Parser.Desugar.fst"
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
# 908 "FStar.Parser.Desugar.fst"
let _61_1742 = (uncurry binders t)
in (match (_61_1742) with
| (bs, t) -> begin
(
# 909 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _61_10 -> (match (_61_10) with
| [] -> begin
(
# 911 "FStar.Parser.Desugar.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun (((FStar_List.rev bs)), (cod)))))
end
| (hd)::tl -> begin
(
# 914 "FStar.Parser.Desugar.fst"
let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (
# 915 "FStar.Parser.Desugar.fst"
let bb = (desugar_binder mlenv hd)
in (
# 916 "FStar.Parser.Desugar.fst"
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
# 924 "FStar.Parser.Desugar.fst"
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
# 927 "FStar.Parser.Desugar.fst"
let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _153_630 = (desugar_exp env f)
in (FStar_All.pipe_right _153_630 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine ((b), (f)))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _153_638 = (let _153_637 = (let _153_636 = (desugar_typ env t)
in (let _153_635 = (desugar_kind env k)
in ((_153_636), (_153_635))))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _153_637))
in (FStar_All.pipe_left wpos _153_638))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(
# 939 "FStar.Parser.Desugar.fst"
let _61_1811 = (FStar_List.fold_left (fun _61_1796 b -> (match (_61_1796) with
| (env, tparams, typs) -> begin
(
# 940 "FStar.Parser.Desugar.fst"
let _61_1800 = (desugar_exp_binder env b)
in (match (_61_1800) with
| (xopt, t) -> begin
(
# 941 "FStar.Parser.Desugar.fst"
let _61_1806 = (match (xopt) with
| None -> begin
(let _153_641 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in ((env), (_153_641)))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_61_1806) with
| (env, x) -> begin
(let _153_645 = (let _153_644 = (let _153_643 = (let _153_642 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _153_642))
in (_153_643)::[])
in (FStar_List.append typs _153_644))
in ((env), ((FStar_List.append tparams ((((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t))), (None)))::[]))), (_153_645)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_61_1811) with
| (env, _61_1809, targs) -> begin
(
# 946 "FStar.Parser.Desugar.fst"
let tup = (let _153_646 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _153_646))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app ((tup), (targs)))))
end))
end
| FStar_Parser_AST.Record (_61_1814) -> begin
(FStar_All.failwith "Unexpected record type")
end
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, ((x, v))::[], t) -> begin
(
# 953 "FStar.Parser.Desugar.fst"
let let_v = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.let_in_typ)) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)), (v), (FStar_Parser_AST.Nothing)))) v.FStar_Parser_AST.range v.FStar_Parser_AST.level)
in (
# 954 "FStar.Parser.Desugar.fst"
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
# 964 "FStar.Parser.Desugar.fst"
let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error (((msg), (r))))))
in (
# 965 "FStar.Parser.Desugar.fst"
let pre_process_comp_typ = (fun t -> (
# 966 "FStar.Parser.Desugar.fst"
let _61_1846 = (head_and_args t)
in (match (_61_1846) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 969 "FStar.Parser.Desugar.fst"
let unit = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (
# 970 "FStar.Parser.Desugar.fst"
let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (
# 971 "FStar.Parser.Desugar.fst"
let _61_1872 = (FStar_All.pipe_right args (FStar_List.partition (fun _61_1854 -> (match (_61_1854) with
| (arg, _61_1853) -> begin
(match ((let _153_658 = (unparen arg)
in _153_658.FStar_Parser_AST.tm)) with
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
# 975 "FStar.Parser.Desugar.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Not enough arguments to \'Lemma\'"), (t.FStar_Parser_AST.range)))))
end
| (ens)::[] -> begin
(
# 978 "FStar.Parser.Desugar.fst"
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
# 982 "FStar.Parser.Desugar.fst"
let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((lemma), ((FStar_List.append args decreases_clause))))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _153_659 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _153_659 FStar_Absyn_Const.prims_lid))) -> begin
(
# 989 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _61_1887 -> (match (_61_1887) with
| (t, imp) -> begin
(let _153_661 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _153_661))
end)) args)
in (let _153_662 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _153_662 args)))
end
| _61_1890 -> begin
(desugar_typ env t)
end)
end)))
in (
# 994 "FStar.Parser.Desugar.fst"
let t = (pre_process_comp_typ t)
in (
# 995 "FStar.Parser.Desugar.fst"
let _61_1894 = (FStar_Absyn_Util.head_and_args t)
in (match (_61_1894) with
| (head, args) -> begin
(match ((let _153_664 = (let _153_663 = (FStar_Absyn_Util.compress_typ head)
in _153_663.FStar_Absyn_Syntax.n)
in ((_153_664), (args)))) with
| (FStar_Absyn_Syntax.Typ_const (eff), ((FStar_Util.Inl (result_typ), _61_1901))::rest) -> begin
(
# 998 "FStar.Parser.Desugar.fst"
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
# 1006 "FStar.Parser.Desugar.fst"
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
# 1017 "FStar.Parser.Desugar.fst"
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
# 1022 "FStar.Parser.Desugar.fst"
let rest = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(match (rest) with
| (req)::(ens)::((FStar_Util.Inr (pat), aq))::[] -> begin
(let _153_671 = (let _153_670 = (let _153_669 = (let _153_668 = (let _153_667 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared (((pat), (FStar_Absyn_Syntax.Meta_smt_pat)))))
in FStar_Util.Inr (_153_667))
in ((_153_668), (aq)))
in (_153_669)::[])
in (ens)::_153_670)
in (req)::_153_671)
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
(let _153_673 = (let _153_672 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _153_672))
in (fail _153_673))
end
end)
end))
end
| _61_1975 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _153_675 = (let _153_674 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _153_674))
in (fail _153_675))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (
# 1041 "FStar.Parser.Desugar.fst"
let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (
# 1042 "FStar.Parser.Desugar.fst"
let setpos = (fun kk -> (
# 1042 "FStar.Parser.Desugar.fst"
let _61_1982 = kk
in {FStar_Absyn_Syntax.n = _61_1982.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_1982.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_1982.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_1982.FStar_Absyn_Syntax.uvs}))
in (
# 1043 "FStar.Parser.Desugar.fst"
let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _61_1991; FStar_Ident.ident = _61_1989; FStar_Ident.nsstr = _61_1987; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _61_2000; FStar_Ident.ident = _61_1998; FStar_Ident.nsstr = _61_1996; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _153_687 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _153_687))) with
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
# 1054 "FStar.Parser.Desugar.fst"
let _61_2016 = (uncurry bs k)
in (match (_61_2016) with
| (bs, k) -> begin
(
# 1055 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _61_13 -> (match (_61_13) with
| [] -> begin
(let _153_698 = (let _153_697 = (let _153_696 = (desugar_kind env k)
in (((FStar_List.rev bs)), (_153_696)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _153_697))
in (FStar_All.pipe_left pos _153_698))
end
| (hd)::tl -> begin
(
# 1059 "FStar.Parser.Desugar.fst"
let _61_2027 = (let _153_700 = (let _153_699 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _153_699 hd))
in (FStar_All.pipe_right _153_700 (as_binder env hd.FStar_Parser_AST.aqual)))
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
# 1067 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _61_2037 -> (match (_61_2037) with
| (t, b) -> begin
(
# 1068 "FStar.Parser.Desugar.fst"
let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _153_702 = (desugar_typ_or_exp env t)
in ((_153_702), (qual))))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((((l), (args))), (FStar_Absyn_Syntax.mk_Kind_unknown)))))
end)
end
| _61_2041 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env f -> (
# 1075 "FStar.Parser.Desugar.fst"
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
# 1082 "FStar.Parser.Desugar.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 1083 "FStar.Parser.Desugar.fst"
let setpos = (fun t -> (
# 1083 "FStar.Parser.Desugar.fst"
let _61_2057 = t
in {FStar_Absyn_Syntax.n = _61_2057.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_2057.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _61_2057.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_2057.FStar_Absyn_Syntax.uvs}))
in (
# 1084 "FStar.Parser.Desugar.fst"
let desugar_quant = (fun q qt b pats body -> (
# 1085 "FStar.Parser.Desugar.fst"
let tk = (desugar_binder env (
# 1085 "FStar.Parser.Desugar.fst"
let _61_2065 = b
in {FStar_Parser_AST.b = _61_2065.FStar_Parser_AST.b; FStar_Parser_AST.brange = _61_2065.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _61_2065.FStar_Parser_AST.aqual}))
in (
# 1086 "FStar.Parser.Desugar.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _153_738 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _153_738)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1089 "FStar.Parser.Desugar.fst"
let _61_2080 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2080) with
| (env, a) -> begin
(
# 1090 "FStar.Parser.Desugar.fst"
let pats = (desugar_pats env pats)
in (
# 1091 "FStar.Parser.Desugar.fst"
let body = (desugar_formula env body)
in (
# 1092 "FStar.Parser.Desugar.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _61_2085 -> begin
(let _153_739 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
in (FStar_All.pipe_left setpos _153_739))
end)
in (
# 1095 "FStar.Parser.Desugar.fst"
let body = (let _153_745 = (let _153_744 = (let _153_743 = (let _153_742 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_153_742)::[])
in ((_153_743), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _153_744))
in (FStar_All.pipe_left pos _153_745))
in (let _153_750 = (let _153_749 = (let _153_746 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _153_746 FStar_Absyn_Syntax.kun))
in (let _153_748 = (let _153_747 = (FStar_Absyn_Syntax.targ body)
in (_153_747)::[])
in (FStar_Absyn_Util.mk_typ_app _153_749 _153_748)))
in (FStar_All.pipe_left setpos _153_750))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1099 "FStar.Parser.Desugar.fst"
let _61_2095 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_2095) with
| (env, x) -> begin
(
# 1100 "FStar.Parser.Desugar.fst"
let pats = (desugar_pats env pats)
in (
# 1101 "FStar.Parser.Desugar.fst"
let body = (desugar_formula env body)
in (
# 1102 "FStar.Parser.Desugar.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _61_2100 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern (((body), (pats)))))
end)
in (
# 1105 "FStar.Parser.Desugar.fst"
let body = (let _153_756 = (let _153_755 = (let _153_754 = (let _153_753 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_153_753)::[])
in ((_153_754), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _153_755))
in (FStar_All.pipe_left pos _153_756))
in (let _153_761 = (let _153_760 = (let _153_757 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _153_757 FStar_Absyn_Syntax.kun))
in (let _153_759 = (let _153_758 = (FStar_Absyn_Syntax.targ body)
in (_153_758)::[])
in (FStar_Absyn_Util.mk_typ_app _153_760 _153_759)))
in (FStar_All.pipe_left setpos _153_761))))))
end))
end
| _61_2104 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1110 "FStar.Parser.Desugar.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(
# 1112 "FStar.Parser.Desugar.fst"
let rest = (b')::_rest
in (
# 1113 "FStar.Parser.Desugar.fst"
let body = (let _153_776 = (q ((rest), (pats), (body)))
in (let _153_775 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _153_776 _153_775 FStar_Parser_AST.Formula)))
in (let _153_777 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _153_777 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _61_2118 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _153_778 = (unparen f)
in _153_778.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 1119 "FStar.Parser.Desugar.fst"
let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled (((f), (l), (FStar_Absyn_Syntax.dummyRange), (p))))))
end
| FStar_Parser_AST.Op ("==", (hd)::_args) -> begin
(
# 1123 "FStar.Parser.Desugar.fst"
let args = (hd)::_args
in (
# 1124 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun t -> (let _153_780 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _153_780))) args)
in (
# 1125 "FStar.Parser.Desugar.fst"
let eq = if (is_type env hd) then begin
(let _153_781 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _153_781 FStar_Absyn_Syntax.kun))
end else begin
(let _153_782 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _153_782 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((((connective s)), (args))) with
| (Some (conn), (_61_2144)::(_61_2142)::[]) -> begin
(let _153_787 = (let _153_783 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _153_783 FStar_Absyn_Syntax.kun))
in (let _153_786 = (FStar_List.map (fun x -> (let _153_785 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _153_785))) args)
in (FStar_Absyn_Util.mk_typ_app _153_787 _153_786)))
end
| _61_2149 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _153_788 = (desugar_exp env f)
in (FStar_All.pipe_right _153_788 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _153_793 = (let _153_789 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _153_789 FStar_Absyn_Syntax.kun))
in (let _153_792 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _153_791 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _153_791))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _153_793 _153_792)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(
# 1153 "FStar.Parser.Desugar.fst"
let binders = (_1)::(_2)::_3
in (let _153_795 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _153_795)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(
# 1157 "FStar.Parser.Desugar.fst"
let binders = (_1)::(_2)::_3
in (let _153_797 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _153_797)))
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
(let _153_798 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _153_798))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (
# 1174 "FStar.Parser.Desugar.fst"
let _61_2214 = env
in {FStar_Parser_DesugarEnv.curmodule = _61_2214.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _61_2214.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _61_2214.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _61_2214.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _61_2214.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _61_2214.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _61_2214.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _61_2214.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _61_2214.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _61_2214.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _61_2214.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _153_803 = (desugar_type_binder env b)
in FStar_Util.Inl (_153_803))
end else begin
(let _153_804 = (desugar_exp_binder env b)
in FStar_Util.Inr (_153_804))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 1182 "FStar.Parser.Desugar.fst"
let _61_2247 = (FStar_List.fold_left (fun _61_2222 b -> (match (_61_2222) with
| (env, out) -> begin
(
# 1183 "FStar.Parser.Desugar.fst"
let tk = (desugar_binder env (
# 1183 "FStar.Parser.Desugar.fst"
let _61_2224 = b
in {FStar_Parser_AST.b = _61_2224.FStar_Parser_AST.b; FStar_Parser_AST.brange = _61_2224.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _61_2224.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1186 "FStar.Parser.Desugar.fst"
let _61_2234 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2234) with
| (env, a) -> begin
((env), ((((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k))), ((trans_aqual b.FStar_Parser_AST.aqual))))::out))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1189 "FStar.Parser.Desugar.fst"
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
(let _153_811 = (desugar_typ env t)
in ((Some (x)), (_153_811)))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _153_812 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in ((None), (_153_812)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _153_813 = (desugar_typ env t)
in ((None), (_153_813)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Absyn_Syntax.tun))
end
| _61_2261 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a type)"), (b.FStar_Parser_AST.brange)))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (
# 1202 "FStar.Parser.Desugar.fst"
let fail = (fun _61_2265 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected domain of an arrow or sum (expected a kind)"), (b.FStar_Parser_AST.brange)))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _153_818 = (desugar_kind env t)
in ((Some (x)), (_153_818)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _153_819 = (desugar_kind env t)
in ((None), (_153_819)))
end
| FStar_Parser_AST.TVariable (x) -> begin
((Some (x)), ((
# 1207 "FStar.Parser.Desugar.fst"
let _61_2276 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _61_2276.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _61_2276.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _61_2276.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _61_2276.FStar_Absyn_Syntax.uvs})))
end
| _61_2279 -> begin
(fail ())
end)))

# 1208 "FStar.Parser.Desugar.fst"
let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (
# 1211 "FStar.Parser.Desugar.fst"
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
in (let _153_828 = (aux tps k)
in (FStar_All.pipe_right _153_828 FStar_Absyn_Util.name_binders))))

# 1215 "FStar.Parser.Desugar.fst"
let mk_data_discriminators : FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Ident.lid  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1220 "FStar.Parser.Desugar.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1221 "FStar.Parser.Desugar.fst"
let binders = (gather_tc_binders tps k)
in (
# 1222 "FStar.Parser.Desugar.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1223 "FStar.Parser.Desugar.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _61_2309 -> (match (_61_2309) with
| (x, _61_2308) -> begin
((x), (Some (imp_tag)))
end))))
in (
# 1224 "FStar.Parser.Desugar.fst"
let binders = (let _153_849 = (let _153_848 = (let _153_847 = (let _153_846 = (let _153_845 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _153_844 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_153_845), (_153_844))))
in (FStar_Absyn_Syntax.mk_Typ_app' _153_846 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _153_847))
in (_153_848)::[])
in (FStar_List.append imp_binders _153_849))
in (
# 1225 "FStar.Parser.Desugar.fst"
let disc_type = (let _153_852 = (let _153_851 = (let _153_850 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _153_850 p))
in ((binders), (_153_851)))
in (FStar_Absyn_Syntax.mk_Typ_fun _153_852 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1227 "FStar.Parser.Desugar.fst"
let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _153_855 = (let _153_854 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in ((disc_name), (disc_type), (_153_854), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Absyn_Syntax.Sig_val_decl (_153_855)))))))))))))

# 1229 "FStar.Parser.Desugar.fst"
let mk_indexed_projectors = (fun fvq refine_domain env _61_2321 lid formals t -> (match (_61_2321) with
| (tc, tps, k) -> begin
(
# 1232 "FStar.Parser.Desugar.fst"
let binders = (gather_tc_binders tps k)
in (
# 1233 "FStar.Parser.Desugar.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1234 "FStar.Parser.Desugar.fst"
let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (
# 1235 "FStar.Parser.Desugar.fst"
let projectee = (let _153_866 = (FStar_Absyn_Syntax.mk_ident (("projectee"), (p)))
in (let _153_865 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _153_866; FStar_Absyn_Syntax.realname = _153_865}))
in (
# 1237 "FStar.Parser.Desugar.fst"
let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (
# 1238 "FStar.Parser.Desugar.fst"
let arg_binder = (
# 1239 "FStar.Parser.Desugar.fst"
let arg_typ = (let _153_869 = (let _153_868 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _153_867 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((_153_868), (_153_867))))
in (FStar_Absyn_Syntax.mk_Typ_app' _153_869 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(
# 1242 "FStar.Parser.Desugar.fst"
let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (
# 1243 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _153_879 = (let _153_878 = (let _153_877 = (let _153_876 = (let _153_875 = (let _153_874 = (let _153_873 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _153_872 = (let _153_871 = (let _153_870 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _153_870))
in (_153_871)::[])
in ((_153_873), (_153_872))))
in (FStar_Absyn_Syntax.mk_Exp_app _153_874 None p))
in (FStar_Absyn_Util.b2t _153_875))
in ((x), (_153_876)))
in (FStar_Absyn_Syntax.mk_Typ_refine _153_877 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _153_878))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _153_879))))
end)
in (
# 1245 "FStar.Parser.Desugar.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _61_2338 -> (match (_61_2338) with
| (x, _61_2337) -> begin
((x), (Some (imp_tag)))
end))))
in (
# 1246 "FStar.Parser.Desugar.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1247 "FStar.Parser.Desugar.fst"
let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (
# 1248 "FStar.Parser.Desugar.fst"
let subst = (let _153_887 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(
# 1250 "FStar.Parser.Desugar.fst"
let _61_2349 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_61_2349) with
| (field_name, _61_2348) -> begin
(
# 1251 "FStar.Parser.Desugar.fst"
let proj = (let _153_884 = (let _153_883 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in ((_153_883), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Typ_app _153_884 None p))
in (FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(
# 1255 "FStar.Parser.Desugar.fst"
let _61_2356 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_61_2356) with
| (field_name, _61_2355) -> begin
(
# 1256 "FStar.Parser.Desugar.fst"
let proj = (let _153_886 = (let _153_885 = (FStar_Absyn_Util.fvar None field_name p)
in ((_153_885), ((arg)::[])))
in (FStar_Absyn_Syntax.mk_Exp_app _153_886 None p))
in (FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (proj))))::[])
end))
end))))
in (FStar_All.pipe_right _153_887 FStar_List.flatten))
in (
# 1259 "FStar.Parser.Desugar.fst"
let ntps = (FStar_List.length tps)
in (
# 1260 "FStar.Parser.Desugar.fst"
let all_params = (let _153_889 = (FStar_All.pipe_right tps (FStar_List.map (fun _61_2363 -> (match (_61_2363) with
| (b, _61_2362) -> begin
((b), (Some (imp_tag)))
end))))
in (FStar_List.append _153_889 formals))
in (let _153_919 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(
# 1264 "FStar.Parser.Desugar.fst"
let _61_2372 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_61_2372) with
| (field_name, _61_2371) -> begin
(
# 1265 "FStar.Parser.Desugar.fst"
let kk = (let _153_893 = (let _153_892 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in ((binders), (_153_892)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _153_893 p))
in (FStar_Absyn_Syntax.Sig_tycon (((field_name), ([]), (kk), ([]), ([]), ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inl (a.FStar_Absyn_Syntax.v)))))::[]), ((FStar_Ident.range_of_lid field_name)))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(
# 1269 "FStar.Parser.Desugar.fst"
let _61_2379 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_61_2379) with
| (field_name, _61_2378) -> begin
(
# 1270 "FStar.Parser.Desugar.fst"
let t = (let _153_896 = (let _153_895 = (let _153_894 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _153_894 p))
in ((binders), (_153_895)))
in (FStar_Absyn_Syntax.mk_Typ_fun _153_896 None p))
in (
# 1271 "FStar.Parser.Desugar.fst"
let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1272 "FStar.Parser.Desugar.fst"
let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector (((lid), (FStar_Util.Inr (x.FStar_Absyn_Syntax.v)))))::[]))
in (
# 1273 "FStar.Parser.Desugar.fst"
let impl = if (((let _153_899 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _153_899)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _153_901 = (let _153_900 = (FStar_Parser_DesugarEnv.current_module env)
in _153_900.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _153_901))) then begin
[]
end else begin
(
# 1278 "FStar.Parser.Desugar.fst"
let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (
# 1279 "FStar.Parser.Desugar.fst"
let as_imp = (fun _61_14 -> (match (_61_14) with
| Some (FStar_Absyn_Syntax.Implicit (_61_2387)) -> begin
true
end
| _61_2391 -> begin
false
end))
in (
# 1282 "FStar.Parser.Desugar.fst"
let arg_pats = (let _153_916 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_61_2396), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _153_909 = (let _153_908 = (let _153_907 = (let _153_906 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_153_906))
in (pos _153_907))
in ((_153_908), ((as_imp imp))))
in (_153_909)::[])
end
end
| (FStar_Util.Inr (_61_2401), imp) -> begin
if ((i + ntps) = j) then begin
(let _153_911 = (let _153_910 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in ((_153_910), ((as_imp imp))))
in (_153_911)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _153_915 = (let _153_914 = (let _153_913 = (let _153_912 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_153_912))
in (pos _153_913))
in ((_153_914), ((as_imp imp))))
in (_153_915)::[])
end
end
end))))
in (FStar_All.pipe_right _153_916 FStar_List.flatten))
in (
# 1291 "FStar.Parser.Desugar.fst"
let pat = (let _153_918 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons ((((FStar_Absyn_Util.fv lid)), (Some (fvq)), (arg_pats)))) pos)
in (let _153_917 = (FStar_Absyn_Util.bvar_to_exp projection)
in ((_153_918), (None), (_153_917))))
in (
# 1292 "FStar.Parser.Desugar.fst"
let body = (FStar_Absyn_Syntax.mk_Exp_match ((arg_exp), ((pat)::[])) None p)
in (
# 1293 "FStar.Parser.Desugar.fst"
let imp = (FStar_Absyn_Syntax.mk_Exp_abs ((binders), (body)) None (FStar_Ident.range_of_lid field_name))
in (
# 1294 "FStar.Parser.Desugar.fst"
let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((((false), ((lb)::[]))), (p), ([]), (quals))))::[])))))))
end
in (FStar_Absyn_Syntax.Sig_val_decl (((field_name), (t), (quals), ((FStar_Ident.range_of_lid field_name)))))::impl))))
end))
end))))
in (FStar_All.pipe_right _153_919 FStar_List.flatten))))))))))))))
end))

# 1301 "FStar.Parser.Desugar.fst"
let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _61_17 -> (match (_61_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _61_2418, _61_2420) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(
# 1306 "FStar.Parser.Desugar.fst"
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
# 1309 "FStar.Parser.Desugar.fst"
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
# 1315 "FStar.Parser.Desugar.fst"
let cod = (FStar_Absyn_Util.comp_result cod)
in (
# 1316 "FStar.Parser.Desugar.fst"
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

# 1324 "FStar.Parser.Desugar.fst"
let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1327 "FStar.Parser.Desugar.fst"
let tycon_id = (fun _61_18 -> (match (_61_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1332 "FStar.Parser.Desugar.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _153_939 = (let _153_938 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_153_938))
in (FStar_Parser_AST.mk_term _153_939 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1338 "FStar.Parser.Desugar.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1339 "FStar.Parser.Desugar.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1340 "FStar.Parser.Desugar.fst"
let apply_binders = (fun t binders -> (
# 1341 "FStar.Parser.Desugar.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _61_2522 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _153_952 = (let _153_951 = (let _153_950 = (binder_to_term b)
in ((out), (_153_950), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_153_951))
in (FStar_Parser_AST.mk_term _153_952 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1346 "FStar.Parser.Desugar.fst"
let tycon_record_as_variant = (fun _61_19 -> (match (_61_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1348 "FStar.Parser.Desugar.fst"
let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (
# 1349 "FStar.Parser.Desugar.fst"
let mfields = (FStar_List.map (fun _61_2535 -> (match (_61_2535) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Absyn_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1350 "FStar.Parser.Desugar.fst"
let result = (let _153_958 = (let _153_957 = (let _153_956 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_153_956))
in (FStar_Parser_AST.mk_term _153_957 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _153_958 parms))
in (
# 1351 "FStar.Parser.Desugar.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _153_960 = (FStar_All.pipe_right fields (FStar_List.map (fun _61_2542 -> (match (_61_2542) with
| (x, _61_2541) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (false)))::[])))), (_153_960)))))))
end
| _61_2544 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1355 "FStar.Parser.Desugar.fst"
let desugar_abstract_tc = (fun quals _env mutuals _61_20 -> (match (_61_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1357 "FStar.Parser.Desugar.fst"
let _61_2558 = (typars_of_binders _env binders)
in (match (_61_2558) with
| (_env', typars) -> begin
(
# 1358 "FStar.Parser.Desugar.fst"
let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (
# 1361 "FStar.Parser.Desugar.fst"
let tconstr = (let _153_971 = (let _153_970 = (let _153_969 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_153_969))
in (FStar_Parser_AST.mk_term _153_970 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _153_971 binders))
in (
# 1362 "FStar.Parser.Desugar.fst"
let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (
# 1363 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_tycon (((qlid), (typars), (k), (mutuals), ([]), (quals), (rng)))
in (
# 1364 "FStar.Parser.Desugar.fst"
let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (
# 1365 "FStar.Parser.Desugar.fst"
let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in ((_env), (_env2), (se), (tconstr))))))))
end))
end
| _61_2569 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1368 "FStar.Parser.Desugar.fst"
let push_tparam = (fun env _61_21 -> (match (_61_21) with
| (FStar_Util.Inr (x), _61_2576) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _61_2581) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (
# 1371 "FStar.Parser.Desugar.fst"
let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (_61_2585))::[] -> begin
(
# 1374 "FStar.Parser.Desugar.fst"
let tc = (FStar_List.hd tcs)
in (
# 1375 "FStar.Parser.Desugar.fst"
let _61_2596 = (desugar_abstract_tc quals env [] tc)
in (match (_61_2596) with
| (_61_2590, _61_2592, se, _61_2595) -> begin
(
# 1376 "FStar.Parser.Desugar.fst"
let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(
# 1379 "FStar.Parser.Desugar.fst"
let _61_2597 = (let _153_981 = (FStar_Range.string_of_range rng)
in (let _153_980 = (let _153_979 = (let _153_978 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _153_978 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _153_979 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _153_981 _153_980)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (
# 1382 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))
end)))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(
# 1387 "FStar.Parser.Desugar.fst"
let _61_2610 = (typars_of_binders env binders)
in (match (_61_2610) with
| (env', typars) -> begin
(
# 1388 "FStar.Parser.Desugar.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _61_22 -> (match (_61_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _61_2615 -> begin
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
# 1394 "FStar.Parser.Desugar.fst"
let t0 = t
in (
# 1395 "FStar.Parser.Desugar.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_23 -> (match (_61_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _61_2623 -> begin
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
# 1400 "FStar.Parser.Desugar.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Effect)) then begin
(
# 1402 "FStar.Parser.Desugar.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let _153_987 = (let _153_986 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _153_985 = (FStar_All.pipe_right quals (FStar_List.filter (fun _61_24 -> (match (_61_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _61_2629 -> begin
true
end))))
in ((_153_986), (typars), (c), (_153_985), (rng))))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_153_987)))
end else begin
(
# 1404 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env' t)
in (let _153_989 = (let _153_988 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_153_988), (typars), (k), (t), (quals), (rng)))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_153_989)))
end
in (
# 1406 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_61_2634))::[] -> begin
(
# 1410 "FStar.Parser.Desugar.fst"
let trec = (FStar_List.hd tcs)
in (
# 1411 "FStar.Parser.Desugar.fst"
let _61_2640 = (tycon_record_as_variant trec)
in (match (_61_2640) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_61_2644)::_61_2642 -> begin
(
# 1415 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1416 "FStar.Parser.Desugar.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (
# 1417 "FStar.Parser.Desugar.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1418 "FStar.Parser.Desugar.fst"
let _61_2655 = et
in (match (_61_2655) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_61_2657) -> begin
(
# 1421 "FStar.Parser.Desugar.fst"
let trec = tc
in (
# 1422 "FStar.Parser.Desugar.fst"
let _61_2662 = (tycon_record_as_variant trec)
in (match (_61_2662) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1425 "FStar.Parser.Desugar.fst"
let _61_2674 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_61_2674) with
| (env, _61_2671, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1428 "FStar.Parser.Desugar.fst"
let _61_2686 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_61_2686) with
| (env, _61_2683, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _61_2688 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1431 "FStar.Parser.Desugar.fst"
let _61_2691 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_61_2691) with
| (env, tcs) -> begin
(
# 1432 "FStar.Parser.Desugar.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1433 "FStar.Parser.Desugar.fst"
let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _61_26 -> (match (_61_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _61_2698, _61_2700, _61_2702, _61_2704), t, quals) -> begin
(
# 1435 "FStar.Parser.Desugar.fst"
let env_tps = (push_tparams env tpars)
in (
# 1436 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev (((id), (tpars), (k), (t), ([]), (rng))))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _61_2718, tags, _61_2721), constrs, tconstr, quals) -> begin
(
# 1440 "FStar.Parser.Desugar.fst"
let tycon = ((tname), (tpars), (k))
in (
# 1441 "FStar.Parser.Desugar.fst"
let env_tps = (push_tparams env tpars)
in (
# 1442 "FStar.Parser.Desugar.fst"
let _61_2752 = (let _153_1005 = (FStar_All.pipe_right constrs (FStar_List.map (fun _61_2734 -> (match (_61_2734) with
| (id, topt, of_notation) -> begin
(
# 1444 "FStar.Parser.Desugar.fst"
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
# 1452 "FStar.Parser.Desugar.fst"
let t = (let _153_1000 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _153_999 = (close env_tps t)
in (desugar_typ _153_1000 _153_999)))
in (
# 1453 "FStar.Parser.Desugar.fst"
let name = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1454 "FStar.Parser.Desugar.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _61_25 -> (match (_61_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _61_2748 -> begin
[]
end))))
in (let _153_1004 = (let _153_1003 = (let _153_1002 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in ((name), (_153_1002), (tycon), (quals), (mutuals), (rng)))
in FStar_Absyn_Syntax.Sig_datacon (_153_1003))
in ((name), (_153_1004)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _153_1005))
in (match (_61_2752) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon (((tname), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))::constrs
end))))
end
| _61_2754 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1460 "FStar.Parser.Desugar.fst"
let bundle = (let _153_1007 = (let _153_1006 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_153_1006), (rng)))
in FStar_Absyn_Syntax.Sig_bundle (_153_1007))
in (
# 1461 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (
# 1462 "FStar.Parser.Desugar.fst"
let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (
# 1463 "FStar.Parser.Desugar.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _61_27 -> (match (_61_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _61_2764, constrs, quals, _61_2768) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _61_2772 -> begin
[]
end))))
in (
# 1467 "FStar.Parser.Desugar.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1468 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env ops)
in ((env), ((FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end)))))))))))

# 1471 "FStar.Parser.Desugar.fst"
let desugar_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.binder Prims.list) = (fun env binders -> (
# 1474 "FStar.Parser.Desugar.fst"
let _61_2803 = (FStar_List.fold_left (fun _61_2781 b -> (match (_61_2781) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1477 "FStar.Parser.Desugar.fst"
let _61_2790 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_61_2790) with
| (env, a) -> begin
(let _153_1016 = (let _153_1015 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_153_1015)::binders)
in ((env), (_153_1016)))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1481 "FStar.Parser.Desugar.fst"
let _61_2798 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_61_2798) with
| (env, x) -> begin
(let _153_1018 = (let _153_1017 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_153_1017)::binders)
in ((env), (_153_1018)))
end))
end
| _61_2800 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_61_2803) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))

# 1485 "FStar.Parser.Desugar.fst"
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

# 1503 "FStar.Parser.Desugar.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _61_29 -> (match (_61_29) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Absyn_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (s) -> begin
FStar_Absyn_Syntax.ResetOptions (s)
end))

# 1507 "FStar.Parser.Desugar.fst"
let trans_quals : FStar_Range.range  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun r -> (FStar_List.map (trans_qual r)))

# 1509 "FStar.Parser.Desugar.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env d -> (
# 1512 "FStar.Parser.Desugar.fst"
let trans_quals = (trans_quals d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1515 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.TopLevelModule (_61_2835) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Multiple modules in a file are no longer supported"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1522 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _153_1036 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in ((_153_1036), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _153_1037 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _153_1037 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _153_1039 = (let _153_1038 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _153_1038))
in _153_1039.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _61_2855) -> begin
(
# 1534 "FStar.Parser.Desugar.fst"
let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _61_2862 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1537 "FStar.Parser.Desugar.fst"
let quals = (match (quals) with
| (_61_2867)::_61_2865 -> begin
(trans_quals quals)
end
| _61_2870 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _61_30 -> (match (_61_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_61_2879); FStar_Absyn_Syntax.lbtyp = _61_2877; FStar_Absyn_Syntax.lbeff = _61_2875; FStar_Absyn_Syntax.lbdef = _61_2873} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _61_2887; FStar_Absyn_Syntax.lbeff = _61_2885; FStar_Absyn_Syntax.lbdef = _61_2883} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (
# 1542 "FStar.Parser.Desugar.fst"
let s = FStar_Absyn_Syntax.Sig_let (((lbs), (d.FStar_Parser_AST.drange), (lids), (quals)))
in (
# 1543 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in ((env), ((s)::[]))))))
end
| _61_2895 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1549 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env t)
in (
# 1550 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_main (((e), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1554 "FStar.Parser.Desugar.fst"
let f = (desugar_formula env t)
in (let _153_1045 = (let _153_1044 = (let _153_1043 = (let _153_1042 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_153_1042), (f), ((FStar_Absyn_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_assume (_153_1043))
in (_153_1044)::[])
in ((env), (_153_1045))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1558 "FStar.Parser.Desugar.fst"
let t = (let _153_1046 = (close_fun env t)
in (desugar_typ env _153_1046))
in (
# 1559 "FStar.Parser.Desugar.fst"
let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _153_1047 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_153_1047)
end else begin
(trans_quals quals)
end
in (
# 1560 "FStar.Parser.Desugar.fst"
let se = (let _153_1049 = (let _153_1048 = (FStar_Parser_DesugarEnv.qualify env id)
in ((_153_1048), (t), (quals), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Sig_val_decl (_153_1049))
in (
# 1561 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1565 "FStar.Parser.Desugar.fst"
let t = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (
# 1566 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1567 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_datacon (((l), (t), (((FStar_Absyn_Const.exn_lid), ([]), (FStar_Absyn_Syntax.ktype))), ((FStar_Absyn_Syntax.ExceptionConstructor)::[]), ((FStar_Absyn_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (
# 1568 "FStar.Parser.Desugar.fst"
let se' = FStar_Absyn_Syntax.Sig_bundle ((((se)::[]), ((FStar_Absyn_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
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
in ((env), ((FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1576 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env term)
in (
# 1577 "FStar.Parser.Desugar.fst"
let t = (let _153_1054 = (let _153_1053 = (let _153_1050 = (FStar_Absyn_Syntax.null_v_binder t)
in (_153_1050)::[])
in (let _153_1052 = (let _153_1051 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _153_1051))
in ((_153_1053), (_153_1052))))
in (FStar_Absyn_Syntax.mk_Typ_fun _153_1054 None d.FStar_Parser_AST.drange))
in (
# 1578 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1579 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_datacon (((l), (t), (((FStar_Absyn_Const.exn_lid), ([]), (FStar_Absyn_Syntax.ktype))), ((FStar_Absyn_Syntax.ExceptionConstructor)::[]), ((FStar_Absyn_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (
# 1580 "FStar.Parser.Desugar.fst"
let se' = FStar_Absyn_Syntax.Sig_bundle ((((se)::[]), ((FStar_Absyn_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (
# 1581 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (
# 1582 "FStar.Parser.Desugar.fst"
let data_ops = (mk_data_projectors env se)
in (
# 1583 "FStar.Parser.Desugar.fst"
let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (
# 1584 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1588 "FStar.Parser.Desugar.fst"
let _61_2948 = (desugar_binders env binders)
in (match (_61_2948) with
| (env_k, binders) -> begin
(
# 1589 "FStar.Parser.Desugar.fst"
let k = (desugar_kind env_k k)
in (
# 1590 "FStar.Parser.Desugar.fst"
let name = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1591 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_kind_abbrev (((name), (binders), (k), (d.FStar_Parser_AST.drange)))
in (
# 1592 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in ((env), ((se)::[]))))))
end))
end
| FStar_Parser_AST.NewEffectForFree (_61_2954) -> begin
(FStar_All.failwith "effects for free only supported in conjunction with --universes")
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1599 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1600 "FStar.Parser.Desugar.fst"
let _61_2967 = (desugar_binders env eff_binders)
in (match (_61_2967) with
| (env, binders) -> begin
(
# 1601 "FStar.Parser.Desugar.fst"
let defn = (desugar_typ env defn)
in (
# 1602 "FStar.Parser.Desugar.fst"
let _61_2971 = (FStar_Absyn_Util.head_and_args defn)
in (match (_61_2971) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _153_1059 = (let _153_1058 = (let _153_1057 = (let _153_1056 = (let _153_1055 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat _153_1055 " not found"))
in (Prims.strcat "Effect " _153_1056))
in ((_153_1057), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_153_1058))
in (Prims.raise _153_1059))
end
| Some (ed) -> begin
(
# 1608 "FStar.Parser.Desugar.fst"
let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (
# 1609 "FStar.Parser.Desugar.fst"
let sub = (FStar_Absyn_Util.subst_typ subst)
in (
# 1610 "FStar.Parser.Desugar.fst"
let ed = (let _153_1077 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _153_1076 = (trans_quals quals)
in (let _153_1075 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _153_1074 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _153_1073 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _153_1072 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _153_1071 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _153_1070 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _153_1069 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _153_1068 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _153_1067 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _153_1066 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _153_1065 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _153_1064 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _153_1063 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _153_1062 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _153_1061 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _153_1077; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _153_1076; FStar_Absyn_Syntax.signature = _153_1075; FStar_Absyn_Syntax.ret = _153_1074; FStar_Absyn_Syntax.bind_wp = _153_1073; FStar_Absyn_Syntax.bind_wlp = _153_1072; FStar_Absyn_Syntax.if_then_else = _153_1071; FStar_Absyn_Syntax.ite_wp = _153_1070; FStar_Absyn_Syntax.ite_wlp = _153_1069; FStar_Absyn_Syntax.wp_binop = _153_1068; FStar_Absyn_Syntax.wp_as_type = _153_1067; FStar_Absyn_Syntax.close_wp = _153_1066; FStar_Absyn_Syntax.close_wp_t = _153_1065; FStar_Absyn_Syntax.assert_p = _153_1064; FStar_Absyn_Syntax.assume_p = _153_1063; FStar_Absyn_Syntax.null_wp = _153_1062; FStar_Absyn_Syntax.trivial = _153_1061})))))))))))))))))
in (
# 1630 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (
# 1631 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)
end
| _61_2983 -> begin
(let _153_1081 = (let _153_1080 = (let _153_1079 = (let _153_1078 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _153_1078 " is not an effect"))
in ((_153_1079), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_153_1080))
in (Prims.raise _153_1081))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, _actions)) -> begin
(
# 1638 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1639 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (
# 1640 "FStar.Parser.Desugar.fst"
let _61_2998 = (desugar_binders env eff_binders)
in (match (_61_2998) with
| (env, binders) -> begin
(
# 1641 "FStar.Parser.Desugar.fst"
let eff_k = (desugar_kind env eff_kind)
in (
# 1642 "FStar.Parser.Desugar.fst"
let _61_3009 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _61_3002 decl -> (match (_61_3002) with
| (env, out) -> begin
(
# 1643 "FStar.Parser.Desugar.fst"
let _61_3006 = (desugar_decl env decl)
in (match (_61_3006) with
| (env, ses) -> begin
(let _153_1085 = (let _153_1084 = (FStar_List.hd ses)
in (_153_1084)::out)
in ((env), (_153_1085)))
end))
end)) ((env), ([]))))
in (match (_61_3009) with
| (env, decls) -> begin
(
# 1645 "FStar.Parser.Desugar.fst"
let decls = (FStar_List.rev decls)
in (
# 1646 "FStar.Parser.Desugar.fst"
let lookup = (fun s -> (match ((let _153_1089 = (let _153_1088 = (FStar_Absyn_Syntax.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_DesugarEnv.qualify env _153_1088))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _153_1089))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((((Prims.strcat "Monad " (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat " expects definition of " s)))), (d.FStar_Parser_AST.drange)))))
end
| Some (t) -> begin
t
end))
in (
# 1649 "FStar.Parser.Desugar.fst"
let ed = (let _153_1105 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _153_1104 = (trans_quals quals)
in (let _153_1103 = (lookup "return")
in (let _153_1102 = (lookup "bind_wp")
in (let _153_1101 = (lookup "bind_wlp")
in (let _153_1100 = (lookup "if_then_else")
in (let _153_1099 = (lookup "ite_wp")
in (let _153_1098 = (lookup "ite_wlp")
in (let _153_1097 = (lookup "wp_binop")
in (let _153_1096 = (lookup "wp_as_type")
in (let _153_1095 = (lookup "close_wp")
in (let _153_1094 = (lookup "close_wp_t")
in (let _153_1093 = (lookup "assert_p")
in (let _153_1092 = (lookup "assume_p")
in (let _153_1091 = (lookup "null_wp")
in (let _153_1090 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _153_1105; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _153_1104; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _153_1103; FStar_Absyn_Syntax.bind_wp = _153_1102; FStar_Absyn_Syntax.bind_wlp = _153_1101; FStar_Absyn_Syntax.if_then_else = _153_1100; FStar_Absyn_Syntax.ite_wp = _153_1099; FStar_Absyn_Syntax.ite_wlp = _153_1098; FStar_Absyn_Syntax.wp_binop = _153_1097; FStar_Absyn_Syntax.wp_as_type = _153_1096; FStar_Absyn_Syntax.close_wp = _153_1095; FStar_Absyn_Syntax.close_wp_t = _153_1094; FStar_Absyn_Syntax.assert_p = _153_1093; FStar_Absyn_Syntax.assume_p = _153_1092; FStar_Absyn_Syntax.null_wp = _153_1091; FStar_Absyn_Syntax.trivial = _153_1090}))))))))))))))))
in (
# 1669 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (
# 1670 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1674 "FStar.Parser.Desugar.fst"
let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _153_1112 = (let _153_1111 = (let _153_1110 = (let _153_1109 = (let _153_1108 = (FStar_Absyn_Print.sli l)
in (Prims.strcat _153_1108 " not found"))
in (Prims.strcat "Effect name " _153_1109))
in ((_153_1110), (d.FStar_Parser_AST.drange)))
in FStar_Absyn_Syntax.Error (_153_1111))
in (Prims.raise _153_1112))
end
| Some (l) -> begin
l
end))
in (
# 1677 "FStar.Parser.Desugar.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1678 "FStar.Parser.Desugar.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1679 "FStar.Parser.Desugar.fst"
let non_reifiable = (fun _61_31 -> (match (_61_31) with
| FStar_Parser_AST.NonReifiableLift (f) -> begin
f
end
| _61_3032 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error ((("Unexpected reifiable sub-effect"), (d.FStar_Parser_AST.drange)))))
end))
in (
# 1682 "FStar.Parser.Desugar.fst"
let lift = (let _153_1115 = (non_reifiable l.FStar_Parser_AST.lift_op)
in (desugar_typ env _153_1115))
in (
# 1683 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_sub_effect ((({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))))))
end)))

# 1684 "FStar.Parser.Desugar.fst"
let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _61_3040 d -> (match (_61_3040) with
| (env, sigelts) -> begin
(
# 1688 "FStar.Parser.Desugar.fst"
let _61_3044 = (desugar_decl env d)
in (match (_61_3044) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))

# 1689 "FStar.Parser.Desugar.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]

# 1693 "FStar.Parser.Desugar.fst"
let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1699 "FStar.Parser.Desugar.fst"
let open_ns = (fun mname d -> (
# 1700 "FStar.Parser.Desugar.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _153_1135 = (let _153_1134 = (let _153_1132 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_153_1132))
in (let _153_1133 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _153_1134 _153_1133)))
in (_153_1135)::d)
end else begin
d
end
in d))
in (
# 1704 "FStar.Parser.Desugar.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (
# 1707 "FStar.Parser.Desugar.fst"
let _61_3071 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _153_1137 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _153_1136 = (open_ns mname decls)
in ((_153_1137), (mname), (_153_1136), (true))))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _153_1139 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _153_1138 = (open_ns mname decls)
in ((_153_1139), (mname), (_153_1138), (false))))
end)
in (match (_61_3071) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1712 "FStar.Parser.Desugar.fst"
let _61_3074 = (desugar_decls env decls)
in (match (_61_3074) with
| (env, sigelts) -> begin
(
# 1713 "FStar.Parser.Desugar.fst"
let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in ((env), (modul), (pop_when_done)))
end))
end)))))

# 1720 "FStar.Parser.Desugar.fst"
let desugar_partial_modul : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun curmod env m -> (
# 1723 "FStar.Parser.Desugar.fst"
let m = if (FStar_Options.interactive_fsi ()) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, _61_3085, _61_3087) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1730 "FStar.Parser.Desugar.fst"
let _61_3095 = (desugar_modul_common curmod env m)
in (match (_61_3095) with
| (x, y, _61_3094) -> begin
((x), (y))
end))))

# 1731 "FStar.Parser.Desugar.fst"
let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (
# 1734 "FStar.Parser.Desugar.fst"
let _61_3101 = (desugar_modul_common None env m)
in (match (_61_3101) with
| (env, modul, pop_when_done) -> begin
(
# 1735 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (
# 1736 "FStar.Parser.Desugar.fst"
let _61_3103 = if (FStar_Options.dump_module modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _153_1150 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _153_1150))
end else begin
()
end
in (let _153_1151 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in ((_153_1151), (modul)))))
end)))

# 1737 "FStar.Parser.Desugar.fst"
let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (
# 1740 "FStar.Parser.Desugar.fst"
let _61_3116 = (FStar_List.fold_left (fun _61_3109 m -> (match (_61_3109) with
| (env, mods) -> begin
(
# 1741 "FStar.Parser.Desugar.fst"
let _61_3113 = (desugar_modul env m)
in (match (_61_3113) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_61_3116) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))

# 1743 "FStar.Parser.Desugar.fst"
let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (
# 1746 "FStar.Parser.Desugar.fst"
let _61_3121 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_61_3121) with
| (en, pop_when_done) -> begin
(
# 1747 "FStar.Parser.Desugar.fst"
let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (
# 1747 "FStar.Parser.Desugar.fst"
let _61_3122 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _61_3122.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _61_3122.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _61_3122.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _61_3122.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _61_3122.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _61_3122.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _61_3122.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _61_3122.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _61_3122.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _61_3122.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _61_3122.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (
# 1748 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))





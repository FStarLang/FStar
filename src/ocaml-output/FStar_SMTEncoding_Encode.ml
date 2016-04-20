
open Prims
# 34 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 35 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _83_27 -> (match (_83_27) with
| (a, b) -> begin
(a, b, c)
end))

# 36 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _83_1 -> (match (_83_1) with
| (FStar_Util.Inl (_83_31), _83_34) -> begin
false
end
| _83_37 -> begin
true
end)) args))

# 37 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _172_12 = (let _172_11 = (let _172_10 = (let _172_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _172_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _172_10))
in FStar_Util.Inl (_172_11))
in Some (_172_12))
end
| _83_44 -> begin
l
end))

# 42 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 43 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _83_48 = a
in (let _172_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _172_19; FStar_Syntax_Syntax.index = _83_48.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _83_48.FStar_Syntax_Syntax.sort}))
in (let _172_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _172_20))))

# 46 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _83_55 -> (match (()) with
| () -> begin
(let _172_30 = (let _172_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _172_29 lid.FStar_Ident.str))
in (FStar_All.failwith _172_30))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _83_59 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_83_59) with
| (_83_57, t) -> begin
(match ((let _172_31 = (FStar_Syntax_Subst.compress t)
in _172_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _83_67 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_83_67) with
| (binders, _83_66) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 54 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _83_70 -> begin
(fail ())
end)
end))))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _172_37 = (let _172_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _172_36))
in (FStar_All.pipe_left escape _172_37)))

# 58 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _172_43 = (let _172_42 = (mk_term_projector_name lid a)
in (_172_42, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _172_43)))

# 60 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _172_49 = (let _172_48 = (mk_term_projector_name_by_pos lid i)
in (_172_48, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _172_49)))

# 62 "FStar.SMTEncoding.Encode.fst"
let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

# 65 "FStar.SMTEncoding.Encode.fst"
type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}

# 65 "FStar.SMTEncoding.Encode.fst"
let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

# 77 "FStar.SMTEncoding.Encode.fst"
let varops : varops_t = (
# 78 "FStar.SMTEncoding.Encode.fst"
let initial_ctr = 100
in (
# 79 "FStar.SMTEncoding.Encode.fst"
let ctr = (FStar_Util.mk_ref initial_ctr)
in (
# 80 "FStar.SMTEncoding.Encode.fst"
let new_scope = (fun _83_94 -> (match (()) with
| () -> begin
(let _172_153 = (FStar_Util.smap_create 100)
in (let _172_152 = (FStar_Util.smap_create 100)
in (_172_153, _172_152)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _172_155 = (let _172_154 = (new_scope ())
in (_172_154)::[])
in (FStar_Util.mk_ref _172_155))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _172_159 = (FStar_ST.read scopes)
in (FStar_Util.find_map _172_159 (fun _83_102 -> (match (_83_102) with
| (names, _83_101) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_83_105) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _83_107 = (FStar_Util.incr ctr)
in (let _172_161 = (let _172_160 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_160))
in (Prims.strcat (Prims.strcat y "__") _172_161)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _172_163 = (let _172_162 = (FStar_ST.read scopes)
in (FStar_List.hd _172_162))
in (FStar_All.pipe_left Prims.fst _172_163))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _83_111 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _172_170 = (let _172_168 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _172_168 "__"))
in (let _172_169 = (FStar_Util.string_of_int rn)
in (Prims.strcat _172_170 _172_169))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _83_119 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _83_120 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _172_178 = (let _172_177 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _172_177))
in (FStar_Util.format2 "%s_%s" pfx _172_178)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _172_182 = (FStar_ST.read scopes)
in (FStar_Util.find_map _172_182 (fun _83_129 -> (match (_83_129) with
| (_83_127, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(
# 96 "FStar.SMTEncoding.Encode.fst"
let id = (next_id ())
in (
# 97 "FStar.SMTEncoding.Encode.fst"
let f = (let _172_183 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _172_183))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _172_185 = (let _172_184 = (FStar_ST.read scopes)
in (FStar_List.hd _172_184))
in (FStar_All.pipe_left Prims.snd _172_185))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _83_136 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _83_139 -> (match (()) with
| () -> begin
(let _172_190 = (let _172_189 = (new_scope ())
in (let _172_188 = (FStar_ST.read scopes)
in (_172_189)::_172_188))
in (FStar_ST.op_Colon_Equals scopes _172_190))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _83_141 -> (match (()) with
| () -> begin
(let _172_194 = (let _172_193 = (FStar_ST.read scopes)
in (FStar_List.tl _172_193))
in (FStar_ST.op_Colon_Equals scopes _172_194))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _83_143 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _83_145 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _83_147 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _83_160 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _83_165 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _83_168 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 122 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _83_170 = x
in (let _172_209 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _172_209; FStar_Syntax_Syntax.index = _83_170.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _83_170.FStar_Syntax_Syntax.sort})))

# 126 "FStar.SMTEncoding.Encode.fst"
type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)

# 127 "FStar.SMTEncoding.Encode.fst"
let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 127 "FStar.SMTEncoding.Encode.fst"
let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_83_174) -> begin
_83_174
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_83_177) -> begin
_83_177
end))

# 131 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 132 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 142 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _172_267 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _83_2 -> (match (_83_2) with
| Binding_var (x, _83_192) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _83_197, _83_199, _83_201) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _172_267 (FStar_String.concat ", "))))

# 147 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_277 = (FStar_Syntax_Print.term_to_string t)
in Some (_172_277))
end else begin
None
end)

# 154 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _172_282 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _172_282))))

# 158 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _172_287 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _172_287))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _83_215 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _83_215.tcenv; warn = _83_215.warn; cache = _83_215.cache; nolabels = _83_215.nolabels; use_zfuel_name = _83_215.use_zfuel_name; encode_non_total_function_typ = _83_215.encode_non_total_function_typ})))))

# 162 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _83_221 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _83_221.depth; tcenv = _83_221.tcenv; warn = _83_221.warn; cache = _83_221.cache; nolabels = _83_221.nolabels; use_zfuel_name = _83_221.use_zfuel_name; encode_non_total_function_typ = _83_221.encode_non_total_function_typ})))))

# 166 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _83_226 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _83_226.depth; tcenv = _83_226.tcenv; warn = _83_226.warn; cache = _83_226.cache; nolabels = _83_226.nolabels; use_zfuel_name = _83_226.use_zfuel_name; encode_non_total_function_typ = _83_226.encode_non_total_function_typ}))

# 168 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _83_3 -> (match (_83_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _83_236 -> begin
None
end)))) with
| None -> begin
(let _172_304 = (let _172_303 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _172_303))
in (FStar_All.failwith _172_304))
end
| Some (b, t) -> begin
t
end))

# 174 "FStar.SMTEncoding.Encode.fst"
let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (
# 175 "FStar.SMTEncoding.Encode.fst"
let fname = (varops.new_fvar x)
in (
# 176 "FStar.SMTEncoding.Encode.fst"
let ftok = (Prims.strcat fname "@tok")
in (let _172_315 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _83_246 = env
in (let _172_314 = (let _172_313 = (let _172_312 = (let _172_311 = (let _172_310 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _172_309 -> Some (_172_309)) _172_310))
in (x, fname, _172_311, None))
in Binding_fvar (_172_312))
in (_172_313)::env.bindings)
in {bindings = _172_314; depth = _83_246.depth; tcenv = _83_246.tcenv; warn = _83_246.warn; cache = _83_246.cache; nolabels = _83_246.nolabels; use_zfuel_name = _83_246.use_zfuel_name; encode_non_total_function_typ = _83_246.encode_non_total_function_typ}))
in (fname, ftok, _172_315)))))

# 179 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _83_4 -> (match (_83_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _83_258 -> begin
None
end))))

# 181 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _172_326 = (let _172_325 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _172_325))
in (FStar_All.failwith _172_326))
end
| Some (s) -> begin
s
end))

# 185 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _83_268 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _83_268.depth; tcenv = _83_268.tcenv; warn = _83_268.warn; cache = _83_268.cache; nolabels = _83_268.nolabels; use_zfuel_name = _83_268.use_zfuel_name; encode_non_total_function_typ = _83_268.encode_non_total_function_typ}))

# 187 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _83_277 = (lookup_lid env x)
in (match (_83_277) with
| (t1, t2, _83_276) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _172_343 = (let _172_342 = (let _172_341 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_172_341)::[])
in (f, _172_342))
in (FStar_SMTEncoding_Term.mkApp _172_343))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _83_279 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _83_279.depth; tcenv = _83_279.tcenv; warn = _83_279.warn; cache = _83_279.cache; nolabels = _83_279.nolabels; use_zfuel_name = _83_279.use_zfuel_name; encode_non_total_function_typ = _83_279.encode_non_total_function_typ}))
end)))

# 191 "FStar.SMTEncoding.Encode.fst"
let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| _83_292 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_83_296, fuel::[]) -> begin
if (let _172_349 = (let _172_348 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _172_348 Prims.fst))
in (FStar_Util.starts_with _172_349 "fuel")) then begin
(let _172_352 = (let _172_351 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _172_351 fuel))
in (FStar_All.pipe_left (fun _172_350 -> Some (_172_350)) _172_352))
end else begin
Some (t)
end
end
| _83_302 -> begin
Some (t)
end)
end
| _83_304 -> begin
None
end)
end)
end))

# 208 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _172_356 = (let _172_355 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _172_355))
in (FStar_All.failwith _172_356))
end))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _83_317 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_83_317) with
| (x, _83_314, _83_316) -> begin
x
end)))

# 213 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _83_323 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_83_323) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _83_327; FStar_SMTEncoding_Term.freevars = _83_325}) when env.use_zfuel_name -> begin
(g, zf)
end
| _83_335 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _83_345 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 225 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _83_5 -> (match (_83_5) with
| Binding_fvar (_83_350, nm', tok, _83_354) when (nm = nm') -> begin
tok
end
| _83_358 -> begin
None
end))))

# 234 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _83_363 -> (match (_83_363) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _83_365 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _83_368 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_368) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _83_378 -> begin
p
end)))))
in (
# 243 "FStar.SMTEncoding.Encode.fst"
let pats = (FStar_List.map add_fuel pats)
in (
# 244 "FStar.SMTEncoding.Encode.fst"
let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, guard::body'::[]) -> begin
(
# 246 "FStar.SMTEncoding.Encode.fst"
let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _172_373 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _172_373))
end
| _83_391 -> begin
(let _172_374 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _172_374 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _83_394 -> begin
body
end)
in (
# 251 "FStar.SMTEncoding.Encode.fst"
let vars = ((fsym, FStar_SMTEncoding_Term.Fuel_sort))::vars
in (FStar_SMTEncoding_Term.mkForall (pats, vars, body))))))
end))
end)
end))

# 254 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' 1)

# 256 "FStar.SMTEncoding.Encode.fst"
let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (
# 257 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _172_380 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_380 FStar_Option.isNone))
end
| _83_433 -> begin
false
end)))

# 269 "FStar.SMTEncoding.Encode.fst"
let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _172_385 = (FStar_Syntax_Util.un_uinst t)
in _172_385.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_83_437) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _172_386 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_386 FStar_Option.isSome))
end
| _83_442 -> begin
false
end))

# 274 "FStar.SMTEncoding.Encode.fst"
let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)

# 277 "FStar.SMTEncoding.Encode.fst"
let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))

# 279 "FStar.SMTEncoding.Encode.fst"
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _172_399 = (let _172_397 = (FStar_Syntax_Syntax.null_binder t)
in (_172_397)::[])
in (let _172_398 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _172_399 _172_398 None))))

# 284 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _172_406 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _172_406))
end
| s -> begin
(
# 287 "FStar.SMTEncoding.Encode.fst"
let _83_454 = ()
in (let _172_407 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _172_407)))
end)) e)))

# 288 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 290 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _83_6 -> (match (_83_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _83_464 -> begin
false
end))

# 295 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 296 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _83_475; FStar_SMTEncoding_Term.freevars = _83_473}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _83_493) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _83_500 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_83_502, []) -> begin
(
# 307 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _83_508 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

# 338 "FStar.SMTEncoding.Encode.fst"
type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)

# 339 "FStar.SMTEncoding.Encode.fst"
type labels =
label Prims.list

# 340 "FStar.SMTEncoding.Encode.fst"
type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}

# 340 "FStar.SMTEncoding.Encode.fst"
let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

# 346 "FStar.SMTEncoding.Encode.fst"
exception Let_rec_unencodeable

# 346 "FStar.SMTEncoding.Encode.fst"
let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))

# 348 "FStar.SMTEncoding.Encode.fst"
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _83_7 -> (match (_83_7) with
| FStar_Const.Const_unit -> begin
FStar_SMTEncoding_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _172_464 = (let _172_463 = (let _172_462 = (let _172_461 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _172_461))
in (_172_462)::[])
in ("FStar.Char.Char", _172_463))
in (FStar_SMTEncoding_Term.mkApp _172_464))
end
| FStar_Const.Const_int (i, None) -> begin
(let _172_465 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _172_465))
end
| FStar_Const.Const_int (i, Some (q)) -> begin
(let _172_469 = (let _172_468 = (let _172_467 = (let _172_466 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _172_466))
in (_172_467)::[])
in ((FStar_Const.constructor_string_of_int_qualifier q), _172_468))
in (FStar_SMTEncoding_Term.mkApp _172_469))
end
| FStar_Const.Const_string (bytes, _83_533) -> begin
(let _172_470 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _172_470))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _172_472 = (let _172_471 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _172_471))
in (FStar_All.failwith _172_472))
end))

# 360 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 361 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 362 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_83_547) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_83_550) -> begin
(let _172_481 = (FStar_Syntax_Util.unrefine t)
in (aux true _172_481))
end
| _83_553 -> begin
if norm then begin
(let _172_482 = (whnf env t)
in (aux false _172_482))
end else begin
(let _172_485 = (let _172_484 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _172_483 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _172_484 _172_483)))
in (FStar_All.failwith _172_485))
end
end)))
in (aux true t0)))

# 371 "FStar.SMTEncoding.Encode.fst"
let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (
# 372 "FStar.SMTEncoding.Encode.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _83_561 -> begin
(let _172_488 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _172_488))
end)))

# 378 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 385 "FStar.SMTEncoding.Encode.fst"
let _83_565 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_536 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _172_536))
end else begin
()
end
in (
# 387 "FStar.SMTEncoding.Encode.fst"
let _83_593 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _83_572 b -> (match (_83_572) with
| (vars, guards, env, decls, names) -> begin
(
# 388 "FStar.SMTEncoding.Encode.fst"
let _83_587 = (
# 389 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 390 "FStar.SMTEncoding.Encode.fst"
let _83_578 = (gen_term_var env x)
in (match (_83_578) with
| (xxsym, xx, env') -> begin
(
# 391 "FStar.SMTEncoding.Encode.fst"
let _83_581 = (let _172_539 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _172_539 env xx))
in (match (_83_581) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_83_587) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_83_593) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 406 "FStar.SMTEncoding.Encode.fst"
let _83_600 = (encode_term t env)
in (match (_83_600) with
| (t, decls) -> begin
(let _172_544 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_172_544, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 410 "FStar.SMTEncoding.Encode.fst"
let _83_607 = (encode_term t env)
in (match (_83_607) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _172_549 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_172_549, decls))
end
| Some (f) -> begin
(let _172_550 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_172_550, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 418 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 419 "FStar.SMTEncoding.Encode.fst"
let _83_614 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_555 = (FStar_Syntax_Print.tag_of_term t)
in (let _172_554 = (FStar_Syntax_Print.tag_of_term t0)
in (let _172_553 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _172_555 _172_554 _172_553))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _172_560 = (let _172_559 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _172_558 = (FStar_Syntax_Print.tag_of_term t0)
in (let _172_557 = (FStar_Syntax_Print.term_to_string t0)
in (let _172_556 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _172_559 _172_558 _172_557 _172_556)))))
in (FStar_All.failwith _172_560))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _172_562 = (let _172_561 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _172_561))
in (FStar_All.failwith _172_562))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _83_625) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _83_630) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 435 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _172_563 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_172_563, []))
end
| FStar_Syntax_Syntax.Tm_type (_83_639) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _83_643) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _172_564 = (encode_const c)
in (_172_564, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 451 "FStar.SMTEncoding.Encode.fst"
let _83_654 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_654) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 455 "FStar.SMTEncoding.Encode.fst"
let _83_661 = (encode_binders None binders env)
in (match (_83_661) with
| (vars, guards, env', decls, _83_660) -> begin
(
# 456 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _172_565 = (varops.fresh "f")
in (_172_565, FStar_SMTEncoding_Term.Term_sort))
in (
# 457 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 458 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 459 "FStar.SMTEncoding.Encode.fst"
let _83_667 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_83_667) with
| (pre_opt, res_t) -> begin
(
# 460 "FStar.SMTEncoding.Encode.fst"
let _83_670 = (encode_term_pred None res_t env' app)
in (match (_83_670) with
| (res_pred, decls') -> begin
(
# 461 "FStar.SMTEncoding.Encode.fst"
let _83_679 = (match (pre_opt) with
| None -> begin
(let _172_566 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_566, decls))
end
| Some (pre) -> begin
(
# 464 "FStar.SMTEncoding.Encode.fst"
let _83_676 = (encode_formula pre env')
in (match (_83_676) with
| (guard, decls0) -> begin
(let _172_567 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_172_567, (FStar_List.append decls decls0)))
end))
end)
in (match (_83_679) with
| (guards, guard_decls) -> begin
(
# 466 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _172_569 = (let _172_568 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _172_568))
in (FStar_SMTEncoding_Term.mkForall _172_569))
in (
# 471 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _172_571 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _172_571 (FStar_List.filter (fun _83_684 -> (match (_83_684) with
| (x, _83_683) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 472 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _83_690) -> begin
(let _172_574 = (let _172_573 = (let _172_572 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _172_572))
in (FStar_SMTEncoding_Term.mkApp _172_573))
in (_172_574, []))
end
| None -> begin
(
# 478 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Tm_arrow")
in (
# 479 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 480 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _172_575 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_172_575))
end else begin
None
end
in (
# 485 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 487 "FStar.SMTEncoding.Encode.fst"
let t = (let _172_577 = (let _172_576 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _172_576))
in (FStar_SMTEncoding_Term.mkApp _172_577))
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 490 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _172_579 = (let _172_578 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_172_578, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_172_579))
in (
# 492 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 493 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _172_586 = (let _172_585 = (let _172_584 = (let _172_583 = (let _172_582 = (let _172_581 = (let _172_580 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_580))
in (f_has_t, _172_581))
in (FStar_SMTEncoding_Term.mkImp _172_582))
in (((f_has_t)::[])::[], (fsym)::cvars, _172_583))
in (mkForall_fuel _172_584))
in (_172_585, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_172_586))
in (
# 495 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _172_590 = (let _172_589 = (let _172_588 = (let _172_587 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _172_587))
in (FStar_SMTEncoding_Term.mkForall _172_588))
in (_172_589, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_172_590))
in (
# 498 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 499 "FStar.SMTEncoding.Encode.fst"
let _83_706 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 503 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Non_total_Tm_arrow")
in (
# 504 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 505 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (
# 506 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (let _172_592 = (let _172_591 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_172_591, Some ("Typing for non-total arrows")))
in FStar_SMTEncoding_Term.Assume (_172_592))
in (
# 507 "FStar.SMTEncoding.Encode.fst"
let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (
# 508 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 509 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 510 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _172_599 = (let _172_598 = (let _172_597 = (let _172_596 = (let _172_595 = (let _172_594 = (let _172_593 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_593))
in (f_has_t, _172_594))
in (FStar_SMTEncoding_Term.mkImp _172_595))
in (((f_has_t)::[])::[], (fsym)::[], _172_596))
in (mkForall_fuel _172_597))
in (_172_598, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_172_599))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_83_717) -> begin
(
# 517 "FStar.SMTEncoding.Encode.fst"
let _83_737 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _83_724; FStar_Syntax_Syntax.pos = _83_722; FStar_Syntax_Syntax.vars = _83_720} -> begin
(
# 519 "FStar.SMTEncoding.Encode.fst"
let _83_732 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_83_732) with
| (b, f) -> begin
(let _172_601 = (let _172_600 = (FStar_List.hd b)
in (Prims.fst _172_600))
in (_172_601, f))
end))
end
| _83_734 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_83_737) with
| (x, f) -> begin
(
# 523 "FStar.SMTEncoding.Encode.fst"
let _83_740 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_83_740) with
| (base_t, decls) -> begin
(
# 524 "FStar.SMTEncoding.Encode.fst"
let _83_744 = (gen_term_var env x)
in (match (_83_744) with
| (x, xtm, env') -> begin
(
# 525 "FStar.SMTEncoding.Encode.fst"
let _83_747 = (encode_formula f env')
in (match (_83_747) with
| (refinement, decls') -> begin
(
# 527 "FStar.SMTEncoding.Encode.fst"
let _83_750 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_750) with
| (fsym, fterm) -> begin
(
# 529 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _172_603 = (let _172_602 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_172_602, refinement))
in (FStar_SMTEncoding_Term.mkAnd _172_603))
in (
# 531 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _172_605 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _172_605 (FStar_List.filter (fun _83_755 -> (match (_83_755) with
| (y, _83_754) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 532 "FStar.SMTEncoding.Encode.fst"
let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (
# 533 "FStar.SMTEncoding.Encode.fst"
let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (
# 534 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _83_762, _83_764) -> begin
(let _172_608 = (let _172_607 = (let _172_606 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _172_606))
in (FStar_SMTEncoding_Term.mkApp _172_607))
in (_172_608, []))
end
| None -> begin
(
# 541 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Tm_refine")
in (
# 542 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 543 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 544 "FStar.SMTEncoding.Encode.fst"
let t = (let _172_610 = (let _172_609 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _172_609))
in (FStar_SMTEncoding_Term.mkApp _172_610))
in (
# 546 "FStar.SMTEncoding.Encode.fst"
let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 547 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 549 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (
# 550 "FStar.SMTEncoding.Encode.fst"
let assumption = (let _172_612 = (let _172_611 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _172_611))
in (FStar_SMTEncoding_Term.mkForall _172_612))
in (
# 552 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _172_619 = (let _172_618 = (let _172_617 = (let _172_616 = (let _172_615 = (let _172_614 = (let _172_613 = (FStar_Syntax_Print.term_to_string t0)
in Some (_172_613))
in (assumption, _172_614))
in FStar_SMTEncoding_Term.Assume (_172_615))
in (_172_616)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, Some ("refinement kinding"))))::_172_617)
in (tdecl)::_172_618)
in (FStar_List.append (FStar_List.append decls decls') _172_619))
in (
# 557 "FStar.SMTEncoding.Encode.fst"
let _83_777 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(
# 562 "FStar.SMTEncoding.Encode.fst"
let ttm = (let _172_620 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _172_620))
in (
# 563 "FStar.SMTEncoding.Encode.fst"
let _83_786 = (encode_term_pred None k env ttm)
in (match (_83_786) with
| (t_has_k, decls) -> begin
(
# 564 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, Some ("Uvar typing")))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_83_789) -> begin
(
# 568 "FStar.SMTEncoding.Encode.fst"
let _83_793 = (FStar_Syntax_Util.head_and_args t0)
in (match (_83_793) with
| (head, args_e) -> begin
(match ((let _172_622 = (let _172_621 = (FStar_Syntax_Subst.compress head)
in _172_621.FStar_Syntax_Syntax.n)
in (_172_622, args_e))) with
| (_83_795, _83_797) when (head_redex env head) -> begin
(let _172_623 = (whnf env t)
in (encode_term _172_623 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), _::(v1, _)::(v2, _)::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(
# 575 "FStar.SMTEncoding.Encode.fst"
let _83_837 = (encode_term v1 env)
in (match (_83_837) with
| (v1, decls1) -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let _83_840 = (encode_term v2 env)
in (match (_83_840) with
| (v2, decls2) -> begin
(let _172_624 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_172_624, (FStar_List.append decls1 decls2)))
end))
end))
end
| _83_842 -> begin
(
# 580 "FStar.SMTEncoding.Encode.fst"
let _83_845 = (encode_args args_e env)
in (match (_83_845) with
| (args, decls) -> begin
(
# 582 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 583 "FStar.SMTEncoding.Encode.fst"
let _83_850 = (encode_term head env)
in (match (_83_850) with
| (head, decls') -> begin
(
# 584 "FStar.SMTEncoding.Encode.fst"
let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(
# 588 "FStar.SMTEncoding.Encode.fst"
let _83_859 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_83_859) with
| (formals, rest) -> begin
(
# 589 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _83_863 _83_867 -> (match ((_83_863, _83_867)) with
| ((bv, _83_862), (a, _83_866)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 590 "FStar.SMTEncoding.Encode.fst"
let ty = (let _172_629 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _172_629 (FStar_Syntax_Subst.subst subst)))
in (
# 591 "FStar.SMTEncoding.Encode.fst"
let _83_872 = (encode_term_pred None ty env app_tm)
in (match (_83_872) with
| (has_type, decls'') -> begin
(
# 592 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 593 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _172_631 = (let _172_630 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_172_630, Some ("Partial app typing")))
in FStar_SMTEncoding_Term.Assume (_172_631))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 597 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 598 "FStar.SMTEncoding.Encode.fst"
let _83_879 = (lookup_free_var_sym env fv)
in (match (_83_879) with
| (fname, fuel_args) -> begin
(
# 599 "FStar.SMTEncoding.Encode.fst"
let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (
# 602 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Subst.compress head)
in (
# 604 "FStar.SMTEncoding.Encode.fst"
let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _172_635 = (let _172_634 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_634 Prims.snd))
in Some (_172_635))
end
| FStar_Syntax_Syntax.Tm_ascribed (_83_911, FStar_Util.Inl (t), _83_915) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_83_919, FStar_Util.Inr (c), _83_923) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _83_927 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 616 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _172_636 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _172_636))
in (
# 617 "FStar.SMTEncoding.Encode.fst"
let _83_935 = (curried_arrow_formals_comp head_type)
in (match (_83_935) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _83_951 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))
end)))))
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 631 "FStar.SMTEncoding.Encode.fst"
let _83_960 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_83_960) with
| (bs, body, opening) -> begin
(
# 632 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _83_962 -> (match (()) with
| () -> begin
(
# 633 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 634 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, Some ("Imprecise function encoding")))
in (let _172_639 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_172_639, (decl)::[]))))
end))
in (
# 637 "FStar.SMTEncoding.Encode.fst"
let is_pure_or_ghost = (fun lc_eff -> (match (lc_eff) with
| FStar_Util.Inl (lc) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
end
| FStar_Util.Inr (eff) -> begin
((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))
end))
in (
# 642 "FStar.SMTEncoding.Encode.fst"
let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _172_644 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _172_644))
end
| FStar_Util.Inr (ef) -> begin
(let _172_646 = (let _172_645 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _172_645 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _172_646))
end))
in (match (lopt) with
| None -> begin
(
# 648 "FStar.SMTEncoding.Encode.fst"
let _83_978 = (let _172_648 = (let _172_647 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _172_647))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _172_648))
in (fallback ()))
end
| Some (lc) -> begin
if (let _172_649 = (is_pure_or_ghost lc)
in (FStar_All.pipe_left Prims.op_Negation _172_649)) then begin
(fallback ())
end else begin
(
# 654 "FStar.SMTEncoding.Encode.fst"
let c = (codomain_eff lc)
in (
# 657 "FStar.SMTEncoding.Encode.fst"
let _83_989 = (encode_binders None bs env)
in (match (_83_989) with
| (vars, guards, envbody, decls, _83_988) -> begin
(
# 658 "FStar.SMTEncoding.Encode.fst"
let _83_992 = (encode_term body envbody)
in (match (_83_992) with
| (body, decls') -> begin
(
# 659 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _172_653 = (let _172_652 = (let _172_651 = (let _172_650 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_650, body))
in (FStar_SMTEncoding_Term.mkImp _172_651))
in ([], vars, _172_652))
in (FStar_SMTEncoding_Term.mkForall _172_653))
in (
# 660 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 661 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _83_998, _83_1000) -> begin
(let _172_656 = (let _172_655 = (let _172_654 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _172_654))
in (FStar_SMTEncoding_Term.mkApp _172_655))
in (_172_656, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(
# 670 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 671 "FStar.SMTEncoding.Encode.fst"
let fsym = (varops.fresh "Exp_abs")
in (
# 672 "FStar.SMTEncoding.Encode.fst"
let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 673 "FStar.SMTEncoding.Encode.fst"
let f = (let _172_658 = (let _172_657 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _172_657))
in (FStar_SMTEncoding_Term.mkApp _172_658))
in (
# 674 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 675 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 676 "FStar.SMTEncoding.Encode.fst"
let _83_1015 = (encode_term_pred None tfun env f)
in (match (_83_1015) with
| (f_has_t, decls'') -> begin
(
# 677 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _172_660 = (let _172_659 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_172_659, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_172_660))
in (
# 679 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _172_667 = (let _172_666 = (let _172_665 = (let _172_664 = (let _172_663 = (let _172_662 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _172_661 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_172_662, _172_661)))
in (FStar_SMTEncoding_Term.mkImp _172_663))
in (((app)::[])::[], (FStar_List.append vars cvars), _172_664))
in (FStar_SMTEncoding_Term.mkForall _172_665))
in (_172_666, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_172_667))
in (
# 681 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 682 "FStar.SMTEncoding.Encode.fst"
let _83_1019 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end))))))))
end)
end))))
end))
end)))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_83_1022, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_83_1034); FStar_Syntax_Syntax.lbunivs = _83_1032; FStar_Syntax_Syntax.lbtyp = _83_1030; FStar_Syntax_Syntax.lbeff = _83_1028; FStar_Syntax_Syntax.lbdef = _83_1026}::_83_1024), _83_1040) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1049; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1046; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_83_1059) -> begin
(
# 695 "FStar.SMTEncoding.Encode.fst"
let _83_1061 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 696 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 697 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _172_668 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_172_668, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 704 "FStar.SMTEncoding.Encode.fst"
let _83_1077 = (encode_term e1 env)
in (match (_83_1077) with
| (ee1, decls1) -> begin
(
# 705 "FStar.SMTEncoding.Encode.fst"
let _83_1080 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_83_1080) with
| (xs, e2) -> begin
(
# 706 "FStar.SMTEncoding.Encode.fst"
let _83_1084 = (FStar_List.hd xs)
in (match (_83_1084) with
| (x, _83_1083) -> begin
(
# 707 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 708 "FStar.SMTEncoding.Encode.fst"
let _83_1088 = (encode_body e2 env')
in (match (_83_1088) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 712 "FStar.SMTEncoding.Encode.fst"
let _83_1096 = (encode_term e env)
in (match (_83_1096) with
| (scr, decls) -> begin
(
# 713 "FStar.SMTEncoding.Encode.fst"
let _83_1133 = (FStar_List.fold_right (fun b _83_1100 -> (match (_83_1100) with
| (else_case, decls) -> begin
(
# 714 "FStar.SMTEncoding.Encode.fst"
let _83_1104 = (FStar_Syntax_Subst.open_branch b)
in (match (_83_1104) with
| (p, w, br) -> begin
(
# 715 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _83_1108 _83_1111 -> (match ((_83_1108, _83_1111)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 717 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 718 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 719 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _83_1117 -> (match (_83_1117) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 720 "FStar.SMTEncoding.Encode.fst"
let _83_1127 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 723 "FStar.SMTEncoding.Encode.fst"
let _83_1124 = (encode_term w env)
in (match (_83_1124) with
| (w, decls2) -> begin
(let _172_702 = (let _172_701 = (let _172_700 = (let _172_699 = (let _172_698 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _172_698))
in (FStar_SMTEncoding_Term.mkEq _172_699))
in (guard, _172_700))
in (FStar_SMTEncoding_Term.mkAnd _172_701))
in (_172_702, decls2))
end))
end)
in (match (_83_1127) with
| (guard, decls2) -> begin
(
# 725 "FStar.SMTEncoding.Encode.fst"
let _83_1130 = (encode_br br env)
in (match (_83_1130) with
| (br, decls3) -> begin
(let _172_703 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_172_703, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_83_1133) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _83_1139 -> begin
(let _172_706 = (encode_one_pat env pat)
in (_172_706)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 739 "FStar.SMTEncoding.Encode.fst"
let _83_1142 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_709 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _172_709))
end else begin
()
end
in (
# 740 "FStar.SMTEncoding.Encode.fst"
let _83_1146 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_83_1146) with
| (vars, pat_term) -> begin
(
# 742 "FStar.SMTEncoding.Encode.fst"
let _83_1158 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _83_1149 v -> (match (_83_1149) with
| (env, vars) -> begin
(
# 743 "FStar.SMTEncoding.Encode.fst"
let _83_1155 = (gen_term_var env v)
in (match (_83_1155) with
| (xx, _83_1153, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_83_1158) with
| (env, vars) -> begin
(
# 746 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_83_1163) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _172_717 = (let _172_716 = (encode_const c)
in (scrutinee, _172_716))
in (FStar_SMTEncoding_Term.mkEq _172_717))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(
# 754 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (
# 755 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1185 -> (match (_83_1185) with
| (arg, _83_1184) -> begin
(
# 756 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _172_720 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _172_720)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 760 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_83_1192) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_83_1202) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _172_728 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1212 -> (match (_83_1212) with
| (arg, _83_1211) -> begin
(
# 772 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _172_727 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _172_727)))
end))))
in (FStar_All.pipe_right _172_728 FStar_List.flatten))
end))
in (
# 776 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _83_1215 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (
# 778 "FStar.SMTEncoding.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let _83_1231 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _83_1221 _83_1225 -> (match ((_83_1221, _83_1225)) with
| ((tms, decls), (t, _83_1224)) -> begin
(
# 789 "FStar.SMTEncoding.Encode.fst"
let _83_1228 = (encode_term t env)
in (match (_83_1228) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_83_1231) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 795 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 796 "FStar.SMTEncoding.Encode.fst"
let _83_1240 = (let _172_741 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _172_741))
in (match (_83_1240) with
| (head, args) -> begin
(match ((let _172_743 = (let _172_742 = (FStar_Syntax_Util.un_uinst head)
in _172_742.FStar_Syntax_Syntax.n)
in (_172_743, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1244) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1257::(hd, _83_1254)::(tl, _83_1250)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _172_744 = (list_elements tl)
in (hd)::_172_744)
end
| _83_1261 -> begin
(
# 801 "FStar.SMTEncoding.Encode.fst"
let _83_1262 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 803 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 804 "FStar.SMTEncoding.Encode.fst"
let _83_1268 = (let _172_747 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _172_747 FStar_Syntax_Util.head_and_args))
in (match (_83_1268) with
| (head, args) -> begin
(match ((let _172_749 = (let _172_748 = (FStar_Syntax_Util.un_uinst head)
in _172_748.FStar_Syntax_Syntax.n)
in (_172_749, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_83_1276, _83_1278)::(e, _83_1273)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _83_1286)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _83_1291 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (
# 810 "FStar.SMTEncoding.Encode.fst"
let lemma_pats = (fun p -> (
# 811 "FStar.SMTEncoding.Encode.fst"
let elts = (list_elements p)
in (
# 812 "FStar.SMTEncoding.Encode.fst"
let smt_pat_or = (fun t -> (
# 813 "FStar.SMTEncoding.Encode.fst"
let _83_1299 = (let _172_754 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _172_754 FStar_Syntax_Util.head_and_args))
in (match (_83_1299) with
| (head, args) -> begin
(match ((let _172_756 = (let _172_755 = (FStar_Syntax_Util.un_uinst head)
in _172_755.FStar_Syntax_Syntax.n)
in (_172_756, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _83_1304)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _83_1309 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _172_759 = (list_elements e)
in (FStar_All.pipe_right _172_759 (FStar_List.map (fun branch -> (let _172_758 = (list_elements branch)
in (FStar_All.pipe_right _172_758 (FStar_List.map one_pat)))))))
end
| _83_1316 -> begin
(let _172_760 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_172_760)::[])
end)
end
| _83_1318 -> begin
(let _172_761 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_172_761)::[])
end))))
in (
# 827 "FStar.SMTEncoding.Encode.fst"
let _83_1352 = (match ((let _172_762 = (FStar_Syntax_Subst.compress t)
in _172_762.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 829 "FStar.SMTEncoding.Encode.fst"
let _83_1325 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_1325) with
| (binders, c) -> begin
(
# 830 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _83_1337)::(post, _83_1333)::(pats, _83_1329)::[] -> begin
(
# 833 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _172_763 = (lemma_pats pats')
in (binders, pre, post, _172_763)))
end
| _83_1345 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _83_1347 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_83_1352) with
| (binders, pre, post, patterns) -> begin
(
# 841 "FStar.SMTEncoding.Encode.fst"
let _83_1359 = (encode_binders None binders env)
in (match (_83_1359) with
| (vars, guards, env, decls, _83_1358) -> begin
(
# 844 "FStar.SMTEncoding.Encode.fst"
let _83_1372 = (let _172_767 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 845 "FStar.SMTEncoding.Encode.fst"
let _83_1369 = (let _172_766 = (FStar_All.pipe_right branch (FStar_List.map (fun _83_1364 -> (match (_83_1364) with
| (t, _83_1363) -> begin
(encode_term t (
# 845 "FStar.SMTEncoding.Encode.fst"
let _83_1365 = env
in {bindings = _83_1365.bindings; depth = _83_1365.depth; tcenv = _83_1365.tcenv; warn = _83_1365.warn; cache = _83_1365.cache; nolabels = _83_1365.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1365.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _172_766 FStar_List.unzip))
in (match (_83_1369) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _172_767 FStar_List.unzip))
in (match (_83_1372) with
| (pats, decls') -> begin
(
# 848 "FStar.SMTEncoding.Encode.fst"
let decls' = (FStar_List.flatten decls')
in (
# 850 "FStar.SMTEncoding.Encode.fst"
let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _172_770 = (let _172_769 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _172_769 e))
in (_172_770)::p))))
end
| _83_1382 -> begin
(
# 858 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _172_776 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_172_776)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _172_778 = (let _172_777 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _172_777 tl))
in (aux _172_778 vars))
end
| _83_1394 -> begin
pats
end))
in (let _172_779 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _172_779 vars)))
end)
end)
in (
# 865 "FStar.SMTEncoding.Encode.fst"
let env = (
# 865 "FStar.SMTEncoding.Encode.fst"
let _83_1396 = env
in {bindings = _83_1396.bindings; depth = _83_1396.depth; tcenv = _83_1396.tcenv; warn = _83_1396.warn; cache = _83_1396.cache; nolabels = true; use_zfuel_name = _83_1396.use_zfuel_name; encode_non_total_function_typ = _83_1396.encode_non_total_function_typ})
in (
# 866 "FStar.SMTEncoding.Encode.fst"
let _83_1401 = (let _172_780 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _172_780 env))
in (match (_83_1401) with
| (pre, decls'') -> begin
(
# 867 "FStar.SMTEncoding.Encode.fst"
let _83_1404 = (let _172_781 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _172_781 env))
in (match (_83_1404) with
| (post, decls''') -> begin
(
# 868 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _172_786 = (let _172_785 = (let _172_784 = (let _172_783 = (let _172_782 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_172_782, post))
in (FStar_SMTEncoding_Term.mkImp _172_783))
in (pats, vars, _172_784))
in (FStar_SMTEncoding_Term.mkForall _172_785))
in (_172_786, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 872 "FStar.SMTEncoding.Encode.fst"
let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_792 = (FStar_Syntax_Print.tag_of_term phi)
in (let _172_791 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _172_792 _172_791)))
end else begin
()
end)
in (
# 877 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 878 "FStar.SMTEncoding.Encode.fst"
let _83_1420 = (FStar_Util.fold_map (fun decls x -> (
# 878 "FStar.SMTEncoding.Encode.fst"
let _83_1417 = (encode_term (Prims.fst x) env)
in (match (_83_1417) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_83_1420) with
| (decls, args) -> begin
(let _172_808 = (f args)
in (_172_808, decls))
end)))
in (
# 881 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _83_1423 -> (f, []))
in (
# 882 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _172_822 = (FStar_List.hd l)
in (FStar_All.pipe_left f _172_822)))
in (
# 883 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _83_8 -> (match (_83_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _83_1434 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 887 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 888 "FStar.SMTEncoding.Encode.fst"
let _83_1451 = (FStar_List.fold_right (fun _83_1442 _83_1445 -> (match ((_83_1442, _83_1445)) with
| ((t, _83_1441), (phis, decls)) -> begin
(
# 890 "FStar.SMTEncoding.Encode.fst"
let _83_1448 = (encode_formula t env)
in (match (_83_1448) with
| (phi, decls') -> begin
((phi)::phis, (FStar_List.append decls' decls))
end))
end)) l ([], []))
in (match (_83_1451) with
| (phis, decls) -> begin
(let _172_847 = (f phis)
in (_172_847, decls))
end)))
in (
# 895 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _83_9 -> (match (_83_9) with
| _83_1458::_83_1456::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 899 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _83_10 -> (match (_83_10) with
| (lhs, _83_1469)::(rhs, _83_1465)::[] -> begin
(
# 901 "FStar.SMTEncoding.Encode.fst"
let _83_1474 = (encode_formula rhs env)
in (match (_83_1474) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_1477) -> begin
(l1, decls1)
end
| _83_1481 -> begin
(
# 905 "FStar.SMTEncoding.Encode.fst"
let _83_1484 = (encode_formula lhs env)
in (match (_83_1484) with
| (l2, decls2) -> begin
(let _172_852 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_172_852, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _83_1486 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 910 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _83_11 -> (match (_83_11) with
| (guard, _83_1499)::(_then, _83_1495)::(_else, _83_1491)::[] -> begin
(
# 912 "FStar.SMTEncoding.Encode.fst"
let _83_1504 = (encode_formula guard env)
in (match (_83_1504) with
| (g, decls1) -> begin
(
# 913 "FStar.SMTEncoding.Encode.fst"
let _83_1507 = (encode_formula _then env)
in (match (_83_1507) with
| (t, decls2) -> begin
(
# 914 "FStar.SMTEncoding.Encode.fst"
let _83_1510 = (encode_formula _else env)
in (match (_83_1510) with
| (e, decls3) -> begin
(
# 915 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _83_1513 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 920 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _172_864 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _172_864)))
in (
# 921 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _172_917 = (let _172_873 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _172_873))
in (let _172_916 = (let _172_915 = (let _172_879 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _172_879))
in (let _172_914 = (let _172_913 = (let _172_912 = (let _172_888 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _172_888))
in (let _172_911 = (let _172_910 = (let _172_909 = (let _172_897 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _172_897))
in (_172_909)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_172_910)
in (_172_912)::_172_911))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_172_913)
in (_172_915)::_172_914))
in (_172_917)::_172_916))
in (
# 933 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 935 "FStar.SMTEncoding.Encode.fst"
let _83_1531 = (encode_formula phi' env)
in (match (_83_1531) with
| (phi, decls) -> begin
(let _172_920 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_172_920, decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 939 "FStar.SMTEncoding.Encode.fst"
let _83_1538 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_83_1538) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1545; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1542; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 943 "FStar.SMTEncoding.Encode.fst"
let _83_1556 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_83_1556) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 947 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1573::(x, _83_1570)::(t, _83_1566)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(
# 950 "FStar.SMTEncoding.Encode.fst"
let _83_1578 = (encode_term x env)
in (match (_83_1578) with
| (x, decls) -> begin
(
# 951 "FStar.SMTEncoding.Encode.fst"
let _83_1581 = (encode_term t env)
in (match (_83_1581) with
| (t, decls') -> begin
(let _172_921 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_172_921, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1599::_83_1597::(r, _83_1594)::(msg, _83_1590)::(phi, _83_1586)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _172_925 = (let _172_922 = (FStar_Syntax_Subst.compress r)
in _172_922.FStar_Syntax_Syntax.n)
in (let _172_924 = (let _172_923 = (FStar_Syntax_Subst.compress msg)
in _172_923.FStar_Syntax_Syntax.n)
in (_172_925, _172_924)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _83_1607))) -> begin
(
# 957 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _83_1614 -> begin
(fallback phi)
end)
end
| _83_1616 when (head_redex env head) -> begin
(let _172_926 = (whnf env phi)
in (encode_formula _172_926 env))
end
| _83_1618 -> begin
(
# 967 "FStar.SMTEncoding.Encode.fst"
let _83_1621 = (encode_term phi env)
in (match (_83_1621) with
| (tt, decls) -> begin
(let _172_927 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_172_927, decls))
end))
end))
end
| _83_1623 -> begin
(
# 972 "FStar.SMTEncoding.Encode.fst"
let _83_1626 = (encode_term phi env)
in (match (_83_1626) with
| (tt, decls) -> begin
(let _172_928 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_172_928, decls))
end))
end))
in (
# 975 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 976 "FStar.SMTEncoding.Encode.fst"
let _83_1638 = (encode_binders None bs env)
in (match (_83_1638) with
| (vars, guards, env, decls, _83_1637) -> begin
(
# 977 "FStar.SMTEncoding.Encode.fst"
let _83_1651 = (let _172_940 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 978 "FStar.SMTEncoding.Encode.fst"
let _83_1648 = (let _172_939 = (FStar_All.pipe_right p (FStar_List.map (fun _83_1643 -> (match (_83_1643) with
| (t, _83_1642) -> begin
(encode_term t (
# 978 "FStar.SMTEncoding.Encode.fst"
let _83_1644 = env
in {bindings = _83_1644.bindings; depth = _83_1644.depth; tcenv = _83_1644.tcenv; warn = _83_1644.warn; cache = _83_1644.cache; nolabels = _83_1644.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1644.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _172_939 FStar_List.unzip))
in (match (_83_1648) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _172_940 FStar_List.unzip))
in (match (_83_1651) with
| (pats, decls') -> begin
(
# 980 "FStar.SMTEncoding.Encode.fst"
let _83_1654 = (encode_formula body env)
in (match (_83_1654) with
| (body, decls'') -> begin
(let _172_941 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _172_941, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 983 "FStar.SMTEncoding.Encode.fst"
let _83_1655 = (debug phi)
in (
# 985 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _83_1667 -> (match (_83_1667) with
| (l, _83_1666) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_83_1670, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 995 "FStar.SMTEncoding.Encode.fst"
let _83_1680 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_958 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _172_958))
end else begin
()
end
in (
# 998 "FStar.SMTEncoding.Encode.fst"
let _83_1687 = (encode_q_body env vars pats body)
in (match (_83_1687) with
| (vars, pats, guard, body, decls) -> begin
(let _172_961 = (let _172_960 = (let _172_959 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _172_959))
in (FStar_SMTEncoding_Term.mkForall _172_960))
in (_172_961, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 1002 "FStar.SMTEncoding.Encode.fst"
let _83_1699 = (encode_q_body env vars pats body)
in (match (_83_1699) with
| (vars, pats, guard, body, decls) -> begin
(let _172_964 = (let _172_963 = (let _172_962 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _172_962))
in (FStar_SMTEncoding_Term.mkExists _172_963))
in (_172_964, decls))
end))
end)))))))))))))))))

# 1011 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 1011 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1017 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 1018 "FStar.SMTEncoding.Encode.fst"
let _83_1705 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1705) with
| (asym, a) -> begin
(
# 1019 "FStar.SMTEncoding.Encode.fst"
let _83_1708 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1708) with
| (xsym, x) -> begin
(
# 1020 "FStar.SMTEncoding.Encode.fst"
let _83_1711 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1711) with
| (ysym, y) -> begin
(
# 1021 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 1022 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1023 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _172_1007 = (let _172_1006 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _172_1006))
in (FStar_SMTEncoding_Term.mkApp _172_1007))
in (
# 1024 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _172_1009 = (let _172_1008 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _172_1008, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_1009))
in (let _172_1015 = (let _172_1014 = (let _172_1013 = (let _172_1012 = (let _172_1011 = (let _172_1010 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _172_1010))
in (FStar_SMTEncoding_Term.mkForall _172_1011))
in (_172_1012, None))
in FStar_SMTEncoding_Term.Assume (_172_1013))
in (_172_1014)::[])
in (vname_decl)::_172_1015))))
in (
# 1027 "FStar.SMTEncoding.Encode.fst"
let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1028 "FStar.SMTEncoding.Encode.fst"
let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1029 "FStar.SMTEncoding.Encode.fst"
let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1030 "FStar.SMTEncoding.Encode.fst"
let prims = (let _172_1175 = (let _172_1024 = (let _172_1023 = (let _172_1022 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1022))
in (quant axy _172_1023))
in (FStar_Syntax_Const.op_Eq, _172_1024))
in (let _172_1174 = (let _172_1173 = (let _172_1031 = (let _172_1030 = (let _172_1029 = (let _172_1028 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _172_1028))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1029))
in (quant axy _172_1030))
in (FStar_Syntax_Const.op_notEq, _172_1031))
in (let _172_1172 = (let _172_1171 = (let _172_1040 = (let _172_1039 = (let _172_1038 = (let _172_1037 = (let _172_1036 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1035 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1036, _172_1035)))
in (FStar_SMTEncoding_Term.mkLT _172_1037))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1038))
in (quant xy _172_1039))
in (FStar_Syntax_Const.op_LT, _172_1040))
in (let _172_1170 = (let _172_1169 = (let _172_1049 = (let _172_1048 = (let _172_1047 = (let _172_1046 = (let _172_1045 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1044 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1045, _172_1044)))
in (FStar_SMTEncoding_Term.mkLTE _172_1046))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1047))
in (quant xy _172_1048))
in (FStar_Syntax_Const.op_LTE, _172_1049))
in (let _172_1168 = (let _172_1167 = (let _172_1058 = (let _172_1057 = (let _172_1056 = (let _172_1055 = (let _172_1054 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1053 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1054, _172_1053)))
in (FStar_SMTEncoding_Term.mkGT _172_1055))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1056))
in (quant xy _172_1057))
in (FStar_Syntax_Const.op_GT, _172_1058))
in (let _172_1166 = (let _172_1165 = (let _172_1067 = (let _172_1066 = (let _172_1065 = (let _172_1064 = (let _172_1063 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1062 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1063, _172_1062)))
in (FStar_SMTEncoding_Term.mkGTE _172_1064))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1065))
in (quant xy _172_1066))
in (FStar_Syntax_Const.op_GTE, _172_1067))
in (let _172_1164 = (let _172_1163 = (let _172_1076 = (let _172_1075 = (let _172_1074 = (let _172_1073 = (let _172_1072 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1071 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1072, _172_1071)))
in (FStar_SMTEncoding_Term.mkSub _172_1073))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1074))
in (quant xy _172_1075))
in (FStar_Syntax_Const.op_Subtraction, _172_1076))
in (let _172_1162 = (let _172_1161 = (let _172_1083 = (let _172_1082 = (let _172_1081 = (let _172_1080 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _172_1080))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1081))
in (quant qx _172_1082))
in (FStar_Syntax_Const.op_Minus, _172_1083))
in (let _172_1160 = (let _172_1159 = (let _172_1092 = (let _172_1091 = (let _172_1090 = (let _172_1089 = (let _172_1088 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1087 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1088, _172_1087)))
in (FStar_SMTEncoding_Term.mkAdd _172_1089))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1090))
in (quant xy _172_1091))
in (FStar_Syntax_Const.op_Addition, _172_1092))
in (let _172_1158 = (let _172_1157 = (let _172_1101 = (let _172_1100 = (let _172_1099 = (let _172_1098 = (let _172_1097 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1096 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1097, _172_1096)))
in (FStar_SMTEncoding_Term.mkMul _172_1098))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1099))
in (quant xy _172_1100))
in (FStar_Syntax_Const.op_Multiply, _172_1101))
in (let _172_1156 = (let _172_1155 = (let _172_1110 = (let _172_1109 = (let _172_1108 = (let _172_1107 = (let _172_1106 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1105 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1106, _172_1105)))
in (FStar_SMTEncoding_Term.mkDiv _172_1107))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1108))
in (quant xy _172_1109))
in (FStar_Syntax_Const.op_Division, _172_1110))
in (let _172_1154 = (let _172_1153 = (let _172_1119 = (let _172_1118 = (let _172_1117 = (let _172_1116 = (let _172_1115 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1114 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1115, _172_1114)))
in (FStar_SMTEncoding_Term.mkMod _172_1116))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1117))
in (quant xy _172_1118))
in (FStar_Syntax_Const.op_Modulus, _172_1119))
in (let _172_1152 = (let _172_1151 = (let _172_1128 = (let _172_1127 = (let _172_1126 = (let _172_1125 = (let _172_1124 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _172_1123 = (FStar_SMTEncoding_Term.unboxBool y)
in (_172_1124, _172_1123)))
in (FStar_SMTEncoding_Term.mkAnd _172_1125))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1126))
in (quant xy _172_1127))
in (FStar_Syntax_Const.op_And, _172_1128))
in (let _172_1150 = (let _172_1149 = (let _172_1137 = (let _172_1136 = (let _172_1135 = (let _172_1134 = (let _172_1133 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _172_1132 = (FStar_SMTEncoding_Term.unboxBool y)
in (_172_1133, _172_1132)))
in (FStar_SMTEncoding_Term.mkOr _172_1134))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1135))
in (quant xy _172_1136))
in (FStar_Syntax_Const.op_Or, _172_1137))
in (let _172_1148 = (let _172_1147 = (let _172_1144 = (let _172_1143 = (let _172_1142 = (let _172_1141 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _172_1141))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1142))
in (quant qx _172_1143))
in (FStar_Syntax_Const.op_Negation, _172_1144))
in (_172_1147)::[])
in (_172_1149)::_172_1148))
in (_172_1151)::_172_1150))
in (_172_1153)::_172_1152))
in (_172_1155)::_172_1154))
in (_172_1157)::_172_1156))
in (_172_1159)::_172_1158))
in (_172_1161)::_172_1160))
in (_172_1163)::_172_1162))
in (_172_1165)::_172_1164))
in (_172_1167)::_172_1166))
in (_172_1169)::_172_1168))
in (_172_1171)::_172_1170))
in (_172_1173)::_172_1172))
in (_172_1175)::_172_1174))
in (
# 1047 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _172_1207 = (FStar_All.pipe_right prims (FStar_List.filter (fun _83_1731 -> (match (_83_1731) with
| (l', _83_1730) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _172_1207 (FStar_List.collect (fun _83_1735 -> (match (_83_1735) with
| (_83_1733, b) -> begin
(b v)
end))))))
in (
# 1049 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _83_1741 -> (match (_83_1741) with
| (l', _83_1740) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1054 "FStar.SMTEncoding.Encode.fst"
let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (
# 1055 "FStar.SMTEncoding.Encode.fst"
let _83_1747 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1747) with
| (xxsym, xx) -> begin
(
# 1056 "FStar.SMTEncoding.Encode.fst"
let _83_1750 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_1750) with
| (ffsym, ff) -> begin
(
# 1057 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _172_1233 = (let _172_1232 = (let _172_1231 = (let _172_1230 = (let _172_1229 = (let _172_1228 = (let _172_1227 = (let _172_1226 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _172_1226))
in (FStar_SMTEncoding_Term.mkEq _172_1227))
in (xx_has_type, _172_1228))
in (FStar_SMTEncoding_Term.mkImp _172_1229))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _172_1230))
in (FStar_SMTEncoding_Term.mkForall _172_1231))
in (_172_1232, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_172_1233)))
end))
end)))

# 1061 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1062 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1063 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1065 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1066 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1068 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun env nm tt -> (
# 1069 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _172_1254 = (let _172_1245 = (let _172_1244 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_172_1244, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_172_1245))
in (let _172_1253 = (let _172_1252 = (let _172_1251 = (let _172_1250 = (let _172_1249 = (let _172_1248 = (let _172_1247 = (let _172_1246 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _172_1246))
in (FStar_SMTEncoding_Term.mkImp _172_1247))
in (((typing_pred)::[])::[], (xx)::[], _172_1248))
in (mkForall_fuel _172_1249))
in (_172_1250, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1251))
in (_172_1252)::[])
in (_172_1254)::_172_1253))))
in (
# 1072 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun env nm tt -> (
# 1073 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1074 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1075 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _172_1277 = (let _172_1266 = (let _172_1265 = (let _172_1264 = (let _172_1263 = (let _172_1262 = (let _172_1261 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _172_1261))
in (FStar_SMTEncoding_Term.mkImp _172_1262))
in (((typing_pred)::[])::[], (xx)::[], _172_1263))
in (mkForall_fuel _172_1264))
in (_172_1265, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1266))
in (let _172_1276 = (let _172_1275 = (let _172_1274 = (let _172_1273 = (let _172_1272 = (let _172_1271 = (let _172_1268 = (let _172_1267 = (FStar_SMTEncoding_Term.boxBool b)
in (_172_1267)::[])
in (_172_1268)::[])
in (let _172_1270 = (let _172_1269 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1269 tt))
in (_172_1271, (bb)::[], _172_1270)))
in (FStar_SMTEncoding_Term.mkForall _172_1272))
in (_172_1273, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_172_1274))
in (_172_1275)::[])
in (_172_1277)::_172_1276))))))
in (
# 1078 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun env nm tt -> (
# 1079 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1080 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1081 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1082 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1083 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1084 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1085 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _172_1291 = (let _172_1290 = (let _172_1289 = (let _172_1288 = (let _172_1287 = (let _172_1286 = (FStar_SMTEncoding_Term.boxInt a)
in (let _172_1285 = (let _172_1284 = (FStar_SMTEncoding_Term.boxInt b)
in (_172_1284)::[])
in (_172_1286)::_172_1285))
in (tt)::_172_1287)
in (tt)::_172_1288)
in ("Prims.Precedes", _172_1289))
in (FStar_SMTEncoding_Term.mkApp _172_1290))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _172_1291))
in (
# 1086 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _172_1292 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _172_1292))
in (let _172_1334 = (let _172_1298 = (let _172_1297 = (let _172_1296 = (let _172_1295 = (let _172_1294 = (let _172_1293 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _172_1293))
in (FStar_SMTEncoding_Term.mkImp _172_1294))
in (((typing_pred)::[])::[], (xx)::[], _172_1295))
in (mkForall_fuel _172_1296))
in (_172_1297, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1298))
in (let _172_1333 = (let _172_1332 = (let _172_1306 = (let _172_1305 = (let _172_1304 = (let _172_1303 = (let _172_1300 = (let _172_1299 = (FStar_SMTEncoding_Term.boxInt b)
in (_172_1299)::[])
in (_172_1300)::[])
in (let _172_1302 = (let _172_1301 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1301 tt))
in (_172_1303, (bb)::[], _172_1302)))
in (FStar_SMTEncoding_Term.mkForall _172_1304))
in (_172_1305, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_172_1306))
in (let _172_1331 = (let _172_1330 = (let _172_1329 = (let _172_1328 = (let _172_1327 = (let _172_1326 = (let _172_1325 = (let _172_1324 = (let _172_1323 = (let _172_1322 = (let _172_1321 = (let _172_1320 = (let _172_1309 = (let _172_1308 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1307 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_172_1308, _172_1307)))
in (FStar_SMTEncoding_Term.mkGT _172_1309))
in (let _172_1319 = (let _172_1318 = (let _172_1312 = (let _172_1311 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _172_1310 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_172_1311, _172_1310)))
in (FStar_SMTEncoding_Term.mkGTE _172_1312))
in (let _172_1317 = (let _172_1316 = (let _172_1315 = (let _172_1314 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _172_1313 = (FStar_SMTEncoding_Term.unboxInt x)
in (_172_1314, _172_1313)))
in (FStar_SMTEncoding_Term.mkLT _172_1315))
in (_172_1316)::[])
in (_172_1318)::_172_1317))
in (_172_1320)::_172_1319))
in (typing_pred_y)::_172_1321)
in (typing_pred)::_172_1322)
in (FStar_SMTEncoding_Term.mk_and_l _172_1323))
in (_172_1324, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _172_1325))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _172_1326))
in (mkForall_fuel _172_1327))
in (_172_1328, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_172_1329))
in (_172_1330)::[])
in (_172_1332)::_172_1331))
in (_172_1334)::_172_1333)))))))))))
in (
# 1098 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun env nm tt -> (let _172_1345 = (let _172_1344 = (let _172_1343 = (let _172_1342 = (let _172_1341 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _172_1341))
in (FStar_SMTEncoding_Term.mkEq _172_1342))
in (_172_1343, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_172_1344))
in (_172_1345)::[]))
in (
# 1100 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun env nm tt -> (
# 1101 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1102 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1103 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _172_1368 = (let _172_1357 = (let _172_1356 = (let _172_1355 = (let _172_1354 = (let _172_1353 = (let _172_1352 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _172_1352))
in (FStar_SMTEncoding_Term.mkImp _172_1353))
in (((typing_pred)::[])::[], (xx)::[], _172_1354))
in (mkForall_fuel _172_1355))
in (_172_1356, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1357))
in (let _172_1367 = (let _172_1366 = (let _172_1365 = (let _172_1364 = (let _172_1363 = (let _172_1362 = (let _172_1359 = (let _172_1358 = (FStar_SMTEncoding_Term.boxString b)
in (_172_1358)::[])
in (_172_1359)::[])
in (let _172_1361 = (let _172_1360 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1360 tt))
in (_172_1362, (bb)::[], _172_1361)))
in (FStar_SMTEncoding_Term.mkForall _172_1363))
in (_172_1364, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_172_1365))
in (_172_1366)::[])
in (_172_1368)::_172_1367))))))
in (
# 1106 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun env reft_name _83_1793 -> (
# 1107 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1109 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1110 "FStar.SMTEncoding.Encode.fst"
let refa = (let _172_1377 = (let _172_1376 = (let _172_1375 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_172_1375)::[])
in (reft_name, _172_1376))
in (FStar_SMTEncoding_Term.mkApp _172_1377))
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let refb = (let _172_1380 = (let _172_1379 = (let _172_1378 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_172_1378)::[])
in (reft_name, _172_1379))
in (FStar_SMTEncoding_Term.mkApp _172_1380))
in (
# 1112 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1113 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _172_1399 = (let _172_1386 = (let _172_1385 = (let _172_1384 = (let _172_1383 = (let _172_1382 = (let _172_1381 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _172_1381))
in (FStar_SMTEncoding_Term.mkImp _172_1382))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _172_1383))
in (mkForall_fuel _172_1384))
in (_172_1385, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1386))
in (let _172_1398 = (let _172_1397 = (let _172_1396 = (let _172_1395 = (let _172_1394 = (let _172_1393 = (let _172_1392 = (let _172_1391 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _172_1390 = (let _172_1389 = (let _172_1388 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _172_1387 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_172_1388, _172_1387)))
in (FStar_SMTEncoding_Term.mkEq _172_1389))
in (_172_1391, _172_1390)))
in (FStar_SMTEncoding_Term.mkImp _172_1392))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _172_1393))
in (mkForall_fuel' 2 _172_1394))
in (_172_1395, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_172_1396))
in (_172_1397)::[])
in (_172_1399)::_172_1398))))))))))
in (
# 1116 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun env nm false_tm -> (
# 1117 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _172_1408 = (let _172_1407 = (let _172_1406 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_172_1406, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1407))
in (_172_1408)::[])))
in (
# 1119 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun env conj _83_1810 -> (
# 1120 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1121 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1122 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1123 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let valid = (let _172_1417 = (let _172_1416 = (let _172_1415 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_172_1415)::[])
in ("Valid", _172_1416))
in (FStar_SMTEncoding_Term.mkApp _172_1417))
in (
# 1125 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1424 = (let _172_1423 = (let _172_1422 = (let _172_1421 = (let _172_1420 = (let _172_1419 = (let _172_1418 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_172_1418, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1419))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1420))
in (FStar_SMTEncoding_Term.mkForall _172_1421))
in (_172_1422, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1423))
in (_172_1424)::[])))))))))
in (
# 1128 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun env disj _83_1822 -> (
# 1129 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1130 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1131 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1132 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let valid = (let _172_1433 = (let _172_1432 = (let _172_1431 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_172_1431)::[])
in ("Valid", _172_1432))
in (FStar_SMTEncoding_Term.mkApp _172_1433))
in (
# 1134 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1135 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1440 = (let _172_1439 = (let _172_1438 = (let _172_1437 = (let _172_1436 = (let _172_1435 = (let _172_1434 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_172_1434, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1435))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1436))
in (FStar_SMTEncoding_Term.mkForall _172_1437))
in (_172_1438, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1439))
in (_172_1440)::[])))))))))
in (
# 1137 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun env eq2 tt -> (
# 1138 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1139 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1140 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1141 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1142 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1143 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1144 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1145 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let valid = (let _172_1449 = (let _172_1448 = (let _172_1447 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_172_1447)::[])
in ("Valid", _172_1448))
in (FStar_SMTEncoding_Term.mkApp _172_1449))
in (let _172_1456 = (let _172_1455 = (let _172_1454 = (let _172_1453 = (let _172_1452 = (let _172_1451 = (let _172_1450 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_172_1450, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1451))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _172_1452))
in (FStar_SMTEncoding_Term.mkForall _172_1453))
in (_172_1454, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1455))
in (_172_1456)::[])))))))))))
in (
# 1148 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun env imp tt -> (
# 1149 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1150 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1151 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1152 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let valid = (let _172_1465 = (let _172_1464 = (let _172_1463 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_172_1463)::[])
in ("Valid", _172_1464))
in (FStar_SMTEncoding_Term.mkApp _172_1465))
in (
# 1154 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1155 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1472 = (let _172_1471 = (let _172_1470 = (let _172_1469 = (let _172_1468 = (let _172_1467 = (let _172_1466 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_172_1466, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1467))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1468))
in (FStar_SMTEncoding_Term.mkForall _172_1469))
in (_172_1470, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1471))
in (_172_1472)::[])))))))))
in (
# 1157 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun env iff tt -> (
# 1158 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1159 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1160 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1161 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1162 "FStar.SMTEncoding.Encode.fst"
let valid = (let _172_1481 = (let _172_1480 = (let _172_1479 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_172_1479)::[])
in ("Valid", _172_1480))
in (FStar_SMTEncoding_Term.mkApp _172_1481))
in (
# 1163 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1164 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1488 = (let _172_1487 = (let _172_1486 = (let _172_1485 = (let _172_1484 = (let _172_1483 = (let _172_1482 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_172_1482, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1483))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1484))
in (FStar_SMTEncoding_Term.mkForall _172_1485))
in (_172_1486, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1487))
in (_172_1488)::[])))))))))
in (
# 1166 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun env for_all tt -> (
# 1167 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1168 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1169 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1170 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1171 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1172 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1173 "FStar.SMTEncoding.Encode.fst"
let valid = (let _172_1497 = (let _172_1496 = (let _172_1495 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_172_1495)::[])
in ("Valid", _172_1496))
in (FStar_SMTEncoding_Term.mkApp _172_1497))
in (
# 1174 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _172_1500 = (let _172_1499 = (let _172_1498 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_172_1498)::[])
in ("Valid", _172_1499))
in (FStar_SMTEncoding_Term.mkApp _172_1500))
in (let _172_1514 = (let _172_1513 = (let _172_1512 = (let _172_1511 = (let _172_1510 = (let _172_1509 = (let _172_1508 = (let _172_1507 = (let _172_1506 = (let _172_1502 = (let _172_1501 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1501)::[])
in (_172_1502)::[])
in (let _172_1505 = (let _172_1504 = (let _172_1503 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1503, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _172_1504))
in (_172_1506, (xx)::[], _172_1505)))
in (FStar_SMTEncoding_Term.mkForall _172_1507))
in (_172_1508, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1509))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1510))
in (FStar_SMTEncoding_Term.mkForall _172_1511))
in (_172_1512, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1513))
in (_172_1514)::[]))))))))))
in (
# 1176 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun env for_some tt -> (
# 1177 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1178 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1179 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1180 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1181 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1182 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1183 "FStar.SMTEncoding.Encode.fst"
let valid = (let _172_1523 = (let _172_1522 = (let _172_1521 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_172_1521)::[])
in ("Valid", _172_1522))
in (FStar_SMTEncoding_Term.mkApp _172_1523))
in (
# 1184 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _172_1526 = (let _172_1525 = (let _172_1524 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_172_1524)::[])
in ("Valid", _172_1525))
in (FStar_SMTEncoding_Term.mkApp _172_1526))
in (let _172_1540 = (let _172_1539 = (let _172_1538 = (let _172_1537 = (let _172_1536 = (let _172_1535 = (let _172_1534 = (let _172_1533 = (let _172_1532 = (let _172_1528 = (let _172_1527 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1527)::[])
in (_172_1528)::[])
in (let _172_1531 = (let _172_1530 = (let _172_1529 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1529, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _172_1530))
in (_172_1532, (xx)::[], _172_1531)))
in (FStar_SMTEncoding_Term.mkExists _172_1533))
in (_172_1534, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1535))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1536))
in (FStar_SMTEncoding_Term.mkForall _172_1537))
in (_172_1538, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1539))
in (_172_1540)::[]))))))))))
in (
# 1186 "FStar.SMTEncoding.Encode.fst"
let mk_range_of_interp = (fun env range_of tt -> (
# 1187 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1188 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1189 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1190 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1191 "FStar.SMTEncoding.Encode.fst"
let range_of_ty = (FStar_SMTEncoding_Term.mkApp (range_of, (a)::(b)::[]))
in (let _172_1551 = (let _172_1550 = (let _172_1549 = (let _172_1548 = (let _172_1547 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_of_ty)
in (((range_of_ty)::[])::[], (aa)::(bb)::[], _172_1547))
in (FStar_SMTEncoding_Term.mkForall _172_1548))
in (_172_1549, Some ("Range_const typing")))
in FStar_SMTEncoding_Term.Assume (_172_1550))
in (_172_1551)::[])))))))
in (
# 1198 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_of_lid, mk_range_of_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _83_1908 -> (match (_83_1908) with
| (l, _83_1907) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_83_1911, f) -> begin
(f env s tt)
end))))))))))))))))))))))

# 1221 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1222 "FStar.SMTEncoding.Encode.fst"
let _83_1917 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_1745 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _172_1745))
end else begin
()
end
in (
# 1225 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1228 "FStar.SMTEncoding.Encode.fst"
let _83_1925 = (encode_sigelt' env se)
in (match (_83_1925) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _172_1748 = (let _172_1747 = (let _172_1746 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1746))
in (_172_1747)::[])
in (_172_1748, e))
end
| _83_1928 -> begin
(let _172_1755 = (let _172_1754 = (let _172_1750 = (let _172_1749 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1749))
in (_172_1750)::g)
in (let _172_1753 = (let _172_1752 = (let _172_1751 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1751))
in (_172_1752)::[])
in (FStar_List.append _172_1754 _172_1753)))
in (_172_1755, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1234 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1240 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1241 "FStar.SMTEncoding.Encode.fst"
let tt = (norm env t)
in (
# 1247 "FStar.SMTEncoding.Encode.fst"
let _83_1941 = (encode_free_var env lid t tt quals)
in (match (_83_1941) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _172_1769 = (let _172_1768 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _172_1768))
in (_172_1769, env))
end else begin
(decls, env)
end
end))))
in (
# 1253 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_1948 lb -> (match (_83_1948) with
| (decls, env) -> begin
(
# 1255 "FStar.SMTEncoding.Encode.fst"
let _83_1952 = (let _172_1778 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _172_1778 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_83_1952) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_1970, _83_1972, _83_1974, _83_1976) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1267 "FStar.SMTEncoding.Encode.fst"
let _83_1982 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_1982) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_1985, t, quals, _83_1989) -> begin
(
# 1271 "FStar.SMTEncoding.Encode.fst"
let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_12 -> (match (_83_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _83_2002 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(
# 1276 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (
# 1277 "FStar.SMTEncoding.Encode.fst"
let _83_2007 = (encode_top_level_val env fv t quals)
in (match (_83_2007) with
| (decls, env) -> begin
(
# 1278 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1279 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _172_1781 = (let _172_1780 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _172_1780))
in (_172_1781, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _83_2013, _83_2015) -> begin
(
# 1285 "FStar.SMTEncoding.Encode.fst"
let _83_2020 = (encode_formula f env)
in (match (_83_2020) with
| (f, decls) -> begin
(
# 1286 "FStar.SMTEncoding.Encode.fst"
let g = (let _172_1786 = (let _172_1785 = (let _172_1784 = (let _172_1783 = (let _172_1782 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _172_1782))
in Some (_172_1783))
in (f, _172_1784))
in FStar_SMTEncoding_Term.Assume (_172_1785))
in (_172_1786)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _83_2025, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_83_2030, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _83_2038; FStar_Syntax_Syntax.lbtyp = _83_2036; FStar_Syntax_Syntax.lbeff = _83_2034; FStar_Syntax_Syntax.lbdef = _83_2032}::[]), _83_2045, _83_2047, _83_2049) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1293 "FStar.SMTEncoding.Encode.fst"
let _83_2055 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2055) with
| (tname, ttok, env) -> begin
(
# 1294 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1295 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1296 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _172_1789 = (let _172_1788 = (let _172_1787 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_172_1787)::[])
in ("Valid", _172_1788))
in (FStar_SMTEncoding_Term.mkApp _172_1789))
in (
# 1297 "FStar.SMTEncoding.Encode.fst"
let decls = (let _172_1797 = (let _172_1796 = (let _172_1795 = (let _172_1794 = (let _172_1793 = (let _172_1792 = (let _172_1791 = (let _172_1790 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _172_1790))
in (FStar_SMTEncoding_Term.mkEq _172_1791))
in (((valid_b2t_x)::[])::[], (xx)::[], _172_1792))
in (FStar_SMTEncoding_Term.mkForall _172_1793))
in (_172_1794, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_172_1795))
in (_172_1796)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_172_1797)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_83_2061, _83_2063, _83_2065, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_13 -> (match (_83_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _83_2075 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _83_2081, _83_2083, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_14 -> (match (_83_14) with
| FStar_Syntax_Syntax.Projector (_83_2089) -> begin
true
end
| _83_2092 -> begin
false
end)))) -> begin
(
# 1311 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1312 "FStar.SMTEncoding.Encode.fst"
let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_83_2096) -> begin
([], env)
end
| None -> begin
(
# 1317 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _83_2104, _83_2106, quals) -> begin
(
# 1323 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1324 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1325 "FStar.SMTEncoding.Encode.fst"
let _83_2118 = (FStar_Util.first_N nbinders formals)
in (match (_83_2118) with
| (formals, extra_formals) -> begin
(
# 1326 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _83_2122 _83_2126 -> (match ((_83_2122, _83_2126)) with
| ((formal, _83_2121), (binder, _83_2125)) -> begin
(let _172_1811 = (let _172_1810 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _172_1810))
in FStar_Syntax_Syntax.NT (_172_1811))
end)) formals binders)
in (
# 1327 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _172_1815 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _83_2130 -> (match (_83_2130) with
| (x, i) -> begin
(let _172_1814 = (
# 1327 "FStar.SMTEncoding.Encode.fst"
let _83_2131 = x
in (let _172_1813 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _83_2131.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_2131.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _172_1813}))
in (_172_1814, i))
end))))
in (FStar_All.pipe_right _172_1815 FStar_Syntax_Util.name_binders))
in (
# 1328 "FStar.SMTEncoding.Encode.fst"
let body = (let _172_1822 = (FStar_Syntax_Subst.compress body)
in (let _172_1821 = (let _172_1816 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _172_1816))
in (let _172_1820 = (let _172_1819 = (let _172_1818 = (FStar_Syntax_Subst.subst subst t)
in _172_1818.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _172_1817 -> Some (_172_1817)) _172_1819))
in (FStar_Syntax_Syntax.extend_app_n _172_1822 _172_1821 _172_1820 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1331 "FStar.SMTEncoding.Encode.fst"
let destruct_bound_function = (fun flid t_norm e -> (
# 1332 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t_norm -> (match ((let _172_1833 = (FStar_Syntax_Util.unascribe e)
in _172_1833.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1335 "FStar.SMTEncoding.Encode.fst"
let _83_2150 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_83_2150) with
| (binders, body, opening) -> begin
(match ((let _172_1834 = (FStar_Syntax_Subst.compress t_norm)
in _172_1834.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1338 "FStar.SMTEncoding.Encode.fst"
let _83_2157 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2157) with
| (formals, c) -> begin
(
# 1339 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1340 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1341 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1343 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1344 "FStar.SMTEncoding.Encode.fst"
let _83_2164 = (FStar_Util.first_N nformals binders)
in (match (_83_2164) with
| (bs0, rest) -> begin
(
# 1345 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1346 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _83_2168 _83_2172 -> (match ((_83_2168, _83_2172)) with
| ((b, _83_2167), (x, _83_2171)) -> begin
(let _172_1838 = (let _172_1837 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _172_1837))
in FStar_Syntax_Syntax.NT (_172_1838))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1348 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1351 "FStar.SMTEncoding.Encode.fst"
let _83_2178 = (eta_expand binders formals body tres)
in (match (_83_2178) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _83_2181) -> begin
(aux true x.FStar_Syntax_Syntax.sort)
end
| _83_2185 when (not (norm)) -> begin
(
# 1359 "FStar.SMTEncoding.Encode.fst"
let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _83_2188 -> begin
(let _172_1841 = (let _172_1840 = (FStar_Syntax_Print.term_to_string e)
in (let _172_1839 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _172_1840 _172_1839)))
in (FStar_All.failwith _172_1841))
end)
end))
end
| _83_2190 -> begin
(match ((let _172_1842 = (FStar_Syntax_Subst.compress t_norm)
in _172_1842.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1369 "FStar.SMTEncoding.Encode.fst"
let _83_2197 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2197) with
| (formals, c) -> begin
(
# 1370 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1371 "FStar.SMTEncoding.Encode.fst"
let _83_2201 = (eta_expand [] formals e tres)
in (match (_83_2201) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _83_2203 -> begin
([], e, [], t_norm)
end)
end))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1379 "FStar.SMTEncoding.Encode.fst"
let _83_2231 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_2218 lb -> (match (_83_2218) with
| (toks, typs, decls, env) -> begin
(
# 1381 "FStar.SMTEncoding.Encode.fst"
let _83_2220 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1382 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1383 "FStar.SMTEncoding.Encode.fst"
let _83_2226 = (let _172_1847 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _172_1847 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_83_2226) with
| (tok, decl, env) -> begin
(let _172_1850 = (let _172_1849 = (let _172_1848 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_172_1848, tok))
in (_172_1849)::toks)
in (_172_1850, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_83_2231) with
| (toks, typs, decls, env) -> begin
(
# 1385 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1386 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1387 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_15 -> (match (_83_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _83_2238 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _172_1853 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _172_1853)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _83_2248; FStar_Syntax_Syntax.lbunivs = _83_2246; FStar_Syntax_Syntax.lbtyp = _83_2244; FStar_Syntax_Syntax.lbeff = _83_2242; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid_fv, (f, ftok))::[]) -> begin
(
# 1394 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1395 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1396 "FStar.SMTEncoding.Encode.fst"
let _83_2268 = (destruct_bound_function flid t_norm e)
in (match (_83_2268) with
| (binders, body, _83_2265, _83_2267) -> begin
(
# 1397 "FStar.SMTEncoding.Encode.fst"
let _83_2275 = (encode_binders None binders env)
in (match (_83_2275) with
| (vars, guards, env', binder_decls, _83_2274) -> begin
(
# 1398 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2278 -> begin
(let _172_1855 = (let _172_1854 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _172_1854))
in (FStar_SMTEncoding_Term.mkApp _172_1855))
end)
in (
# 1399 "FStar.SMTEncoding.Encode.fst"
let _83_2284 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _172_1857 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _172_1856 = (encode_formula body env')
in (_172_1857, _172_1856)))
end else begin
(let _172_1858 = (encode_term body env')
in (app, _172_1858))
end
in (match (_83_2284) with
| (app, (body, decls2)) -> begin
(
# 1403 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _172_1867 = (let _172_1866 = (let _172_1863 = (let _172_1862 = (let _172_1861 = (let _172_1860 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _172_1859 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_172_1860, _172_1859)))
in (FStar_SMTEncoding_Term.mkImp _172_1861))
in (((app)::[])::[], vars, _172_1862))
in (FStar_SMTEncoding_Term.mkForall _172_1863))
in (let _172_1865 = (let _172_1864 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_172_1864))
in (_172_1866, _172_1865)))
in FStar_SMTEncoding_Term.Assume (_172_1867))
in (let _172_1869 = (let _172_1868 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _172_1868))
in (_172_1869, env)))
end)))
end))
end))))
end
| _83_2287 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1409 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _172_1870 = (varops.fresh "fuel")
in (_172_1870, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1410 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1411 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1412 "FStar.SMTEncoding.Encode.fst"
let _83_2305 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _83_2293 _83_2298 -> (match ((_83_2293, _83_2298)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(
# 1413 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1414 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1415 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1416 "FStar.SMTEncoding.Encode.fst"
let env = (let _172_1875 = (let _172_1874 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _172_1873 -> Some (_172_1873)) _172_1874))
in (push_free_var env flid gtok _172_1875))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_83_2305) with
| (gtoks, env) -> begin
(
# 1418 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1419 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _83_2314 t_norm _83_2325 -> (match ((_83_2314, _83_2325)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _83_2324; FStar_Syntax_Syntax.lbunivs = _83_2322; FStar_Syntax_Syntax.lbtyp = _83_2320; FStar_Syntax_Syntax.lbeff = _83_2318; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1420 "FStar.SMTEncoding.Encode.fst"
let _83_2330 = (destruct_bound_function flid t_norm e)
in (match (_83_2330) with
| (binders, body, formals, tres) -> begin
(
# 1421 "FStar.SMTEncoding.Encode.fst"
let _83_2337 = (encode_binders None binders env)
in (match (_83_2337) with
| (vars, guards, env', binder_decls, _83_2336) -> begin
(
# 1422 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _172_1886 = (let _172_1885 = (let _172_1884 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_172_1884)
in (g, _172_1885, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_172_1886))
in (
# 1423 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1424 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1425 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1426 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1427 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _172_1889 = (let _172_1888 = (let _172_1887 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_172_1887)::vars_tm)
in (g, _172_1888))
in (FStar_SMTEncoding_Term.mkApp _172_1889))
in (
# 1428 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _172_1892 = (let _172_1891 = (let _172_1890 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_172_1890)::vars_tm)
in (g, _172_1891))
in (FStar_SMTEncoding_Term.mkApp _172_1892))
in (
# 1429 "FStar.SMTEncoding.Encode.fst"
let _83_2347 = (encode_term body env')
in (match (_83_2347) with
| (body_tm, decls2) -> begin
(
# 1430 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _172_1901 = (let _172_1900 = (let _172_1897 = (let _172_1896 = (let _172_1895 = (let _172_1894 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _172_1893 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_172_1894, _172_1893)))
in (FStar_SMTEncoding_Term.mkImp _172_1895))
in (((gsapp)::[])::[], (fuel)::vars, _172_1896))
in (FStar_SMTEncoding_Term.mkForall _172_1897))
in (let _172_1899 = (let _172_1898 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_172_1898))
in (_172_1900, _172_1899)))
in FStar_SMTEncoding_Term.Assume (_172_1901))
in (
# 1432 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _172_1905 = (let _172_1904 = (let _172_1903 = (let _172_1902 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _172_1902))
in (FStar_SMTEncoding_Term.mkForall _172_1903))
in (_172_1904, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_172_1905))
in (
# 1434 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _172_1914 = (let _172_1913 = (let _172_1912 = (let _172_1911 = (let _172_1910 = (let _172_1909 = (let _172_1908 = (let _172_1907 = (let _172_1906 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_172_1906)::vars_tm)
in (g, _172_1907))
in (FStar_SMTEncoding_Term.mkApp _172_1908))
in (gsapp, _172_1909))
in (FStar_SMTEncoding_Term.mkEq _172_1910))
in (((gsapp)::[])::[], (fuel)::vars, _172_1911))
in (FStar_SMTEncoding_Term.mkForall _172_1912))
in (_172_1913, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_172_1914))
in (
# 1436 "FStar.SMTEncoding.Encode.fst"
let _83_2370 = (
# 1437 "FStar.SMTEncoding.Encode.fst"
let _83_2357 = (encode_binders None formals env0)
in (match (_83_2357) with
| (vars, v_guards, env, binder_decls, _83_2356) -> begin
(
# 1438 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1439 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1440 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1441 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _172_1915 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _172_1915 ((fuel)::vars)))
in (let _172_1919 = (let _172_1918 = (let _172_1917 = (let _172_1916 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _172_1916))
in (FStar_SMTEncoding_Term.mkForall _172_1917))
in (_172_1918, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_172_1919)))
in (
# 1444 "FStar.SMTEncoding.Encode.fst"
let _83_2367 = (
# 1445 "FStar.SMTEncoding.Encode.fst"
let _83_2364 = (encode_term_pred None tres env gapp)
in (match (_83_2364) with
| (g_typing, d3) -> begin
(let _172_1927 = (let _172_1926 = (let _172_1925 = (let _172_1924 = (let _172_1923 = (let _172_1922 = (let _172_1921 = (let _172_1920 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_172_1920, g_typing))
in (FStar_SMTEncoding_Term.mkImp _172_1921))
in (((gapp)::[])::[], (fuel)::vars, _172_1922))
in (FStar_SMTEncoding_Term.mkForall _172_1923))
in (_172_1924, Some ("Typing correspondence of token to term")))
in FStar_SMTEncoding_Term.Assume (_172_1925))
in (_172_1926)::[])
in (d3, _172_1927))
end))
in (match (_83_2367) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_83_2370) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1449 "FStar.SMTEncoding.Encode.fst"
let _83_2386 = (let _172_1930 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _83_2374 _83_2378 -> (match ((_83_2374, _83_2378)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1450 "FStar.SMTEncoding.Encode.fst"
let _83_2382 = (encode_one_binding env0 gtok ty bs)
in (match (_83_2382) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _172_1930))
in (match (_83_2386) with
| (decls, eqns, env0) -> begin
(
# 1452 "FStar.SMTEncoding.Encode.fst"
let _83_2395 = (let _172_1932 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _172_1932 (FStar_List.partition (fun _83_16 -> (match (_83_16) with
| FStar_SMTEncoding_Term.DeclFun (_83_2389) -> begin
true
end
| _83_2392 -> begin
false
end)))))
in (match (_83_2395) with
| (prefix_decls, rest) -> begin
(
# 1455 "FStar.SMTEncoding.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)
with
| Let_rec_unencodeable -> begin
(
# 1458 "FStar.SMTEncoding.Encode.fst"
let msg = (let _172_1935 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _172_1935 (FStar_String.concat " and ")))
in (
# 1459 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _83_2399, _83_2401, _83_2403) -> begin
(
# 1464 "FStar.SMTEncoding.Encode.fst"
let _83_2408 = (encode_signature env ses)
in (match (_83_2408) with
| (g, env) -> begin
(
# 1465 "FStar.SMTEncoding.Encode.fst"
let _83_2420 = (FStar_All.pipe_right g (FStar_List.partition (fun _83_17 -> (match (_83_17) with
| FStar_SMTEncoding_Term.Assume (_83_2411, Some ("inversion axiom")) -> begin
false
end
| _83_2417 -> begin
true
end))))
in (match (_83_2420) with
| (g', inversions) -> begin
(
# 1468 "FStar.SMTEncoding.Encode.fst"
let _83_2429 = (FStar_All.pipe_right g' (FStar_List.partition (fun _83_18 -> (match (_83_18) with
| FStar_SMTEncoding_Term.DeclFun (_83_2423) -> begin
true
end
| _83_2426 -> begin
false
end))))
in (match (_83_2429) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _83_2432, tps, k, _83_2436, datas, quals, _83_2440) -> begin
(
# 1474 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_19 -> (match (_83_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _83_2447 -> begin
false
end))))
in (
# 1475 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1477 "FStar.SMTEncoding.Encode.fst"
let _83_2459 = c
in (match (_83_2459) with
| (name, args, _83_2454, _83_2456, _83_2458) -> begin
(let _172_1943 = (let _172_1942 = (let _172_1941 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _172_1941, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_1942))
in (_172_1943)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1481 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _172_1949 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _172_1949 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1485 "FStar.SMTEncoding.Encode.fst"
let _83_2466 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_2466) with
| (xxsym, xx) -> begin
(
# 1486 "FStar.SMTEncoding.Encode.fst"
let _83_2502 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _83_2469 l -> (match (_83_2469) with
| (out, decls) -> begin
(
# 1487 "FStar.SMTEncoding.Encode.fst"
let _83_2474 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_83_2474) with
| (_83_2472, data_t) -> begin
(
# 1488 "FStar.SMTEncoding.Encode.fst"
let _83_2477 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_83_2477) with
| (args, res) -> begin
(
# 1489 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _172_1952 = (FStar_Syntax_Subst.compress res)
in _172_1952.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_83_2479, indices) -> begin
indices
end
| _83_2484 -> begin
[]
end)
in (
# 1492 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _83_2490 -> (match (_83_2490) with
| (x, _83_2489) -> begin
(let _172_1957 = (let _172_1956 = (let _172_1955 = (mk_term_projector_name l x)
in (_172_1955, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _172_1956))
in (push_term_var env x _172_1957))
end)) env))
in (
# 1495 "FStar.SMTEncoding.Encode.fst"
let _83_2494 = (encode_args indices env)
in (match (_83_2494) with
| (indices, decls') -> begin
(
# 1496 "FStar.SMTEncoding.Encode.fst"
let _83_2495 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1498 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _172_1962 = (FStar_List.map2 (fun v a -> (let _172_1961 = (let _172_1960 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_172_1960, a))
in (FStar_SMTEncoding_Term.mkEq _172_1961))) vars indices)
in (FStar_All.pipe_right _172_1962 FStar_SMTEncoding_Term.mk_and_l))
in (let _172_1967 = (let _172_1966 = (let _172_1965 = (let _172_1964 = (let _172_1963 = (mk_data_tester env l xx)
in (_172_1963, eqs))
in (FStar_SMTEncoding_Term.mkAnd _172_1964))
in (out, _172_1965))
in (FStar_SMTEncoding_Term.mkOr _172_1966))
in (_172_1967, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_83_2502) with
| (data_ax, decls) -> begin
(
# 1500 "FStar.SMTEncoding.Encode.fst"
let _83_2505 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2505) with
| (ffsym, ff) -> begin
(
# 1501 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _172_1968 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _172_1968 xx tapp))
in (let _172_1975 = (let _172_1974 = (let _172_1973 = (let _172_1972 = (let _172_1971 = (let _172_1970 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _172_1969 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _172_1970, _172_1969)))
in (FStar_SMTEncoding_Term.mkForall _172_1971))
in (_172_1972, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_172_1973))
in (_172_1974)::[])
in (FStar_List.append decls _172_1975)))
end))
end))
end))
end)
in (
# 1505 "FStar.SMTEncoding.Encode.fst"
let _83_2515 = (match ((let _172_1976 = (FStar_Syntax_Subst.compress k)
in _172_1976.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _83_2512 -> begin
(tps, k)
end)
in (match (_83_2515) with
| (formals, res) -> begin
(
# 1511 "FStar.SMTEncoding.Encode.fst"
let _83_2518 = (FStar_Syntax_Subst.open_term formals res)
in (match (_83_2518) with
| (formals, res) -> begin
(
# 1512 "FStar.SMTEncoding.Encode.fst"
let _83_2525 = (encode_binders None formals env)
in (match (_83_2525) with
| (vars, guards, env', binder_decls, _83_2524) -> begin
(
# 1514 "FStar.SMTEncoding.Encode.fst"
let _83_2529 = (new_term_constant_and_tok_from_lid env t)
in (match (_83_2529) with
| (tname, ttok, env) -> begin
(
# 1515 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1516 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1517 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _172_1978 = (let _172_1977 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _172_1977))
in (FStar_SMTEncoding_Term.mkApp _172_1978))
in (
# 1518 "FStar.SMTEncoding.Encode.fst"
let _83_2550 = (
# 1519 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _172_1982 = (let _172_1981 = (FStar_All.pipe_right vars (FStar_List.map (fun _83_2535 -> (match (_83_2535) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _172_1980 = (varops.next_id ())
in (tname, _172_1981, FStar_SMTEncoding_Term.Term_sort, _172_1980, false)))
in (constructor_or_logic_type_decl _172_1982))
in (
# 1520 "FStar.SMTEncoding.Encode.fst"
let _83_2547 = (match (vars) with
| [] -> begin
(let _172_1986 = (let _172_1985 = (let _172_1984 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _172_1983 -> Some (_172_1983)) _172_1984))
in (push_free_var env t tname _172_1985))
in ([], _172_1986))
end
| _83_2539 -> begin
(
# 1523 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1524 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _172_1987 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _172_1987))
in (
# 1525 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1526 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1529 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _172_1991 = (let _172_1990 = (let _172_1989 = (let _172_1988 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _172_1988))
in (FStar_SMTEncoding_Term.mkForall' _172_1989))
in (_172_1990, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_172_1991))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_83_2547) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_83_2550) with
| (decls, env) -> begin
(
# 1532 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1533 "FStar.SMTEncoding.Encode.fst"
let _83_2553 = (encode_term_pred None res env' tapp)
in (match (_83_2553) with
| (k, decls) -> begin
(
# 1534 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _172_1995 = (let _172_1994 = (let _172_1993 = (let _172_1992 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_1992))
in (_172_1993, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_172_1994))
in (_172_1995)::[])
end else begin
[]
end
in (let _172_2001 = (let _172_2000 = (let _172_1999 = (let _172_1998 = (let _172_1997 = (let _172_1996 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _172_1996))
in (FStar_SMTEncoding_Term.mkForall _172_1997))
in (_172_1998, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_172_1999))
in (_172_2000)::[])
in (FStar_List.append (FStar_List.append decls karr) _172_2001)))
end))
in (
# 1539 "FStar.SMTEncoding.Encode.fst"
let aux = (let _172_2005 = (let _172_2002 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _172_2002))
in (let _172_2004 = (let _172_2003 = (pretype_axiom tapp vars)
in (_172_2003)::[])
in (FStar_List.append _172_2005 _172_2004)))
in (
# 1544 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2560, _83_2562, _83_2564, _83_2566, _83_2568, _83_2570, _83_2572) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2577, t, _83_2580, n_tps, quals, _83_2584, drange) -> begin
(
# 1552 "FStar.SMTEncoding.Encode.fst"
let _83_2591 = (new_term_constant_and_tok_from_lid env d)
in (match (_83_2591) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1553 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1554 "FStar.SMTEncoding.Encode.fst"
let _83_2595 = (FStar_Syntax_Util.arrow_formals t)
in (match (_83_2595) with
| (formals, t_res) -> begin
(
# 1555 "FStar.SMTEncoding.Encode.fst"
let _83_2598 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2598) with
| (fuel_var, fuel_tm) -> begin
(
# 1556 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1557 "FStar.SMTEncoding.Encode.fst"
let _83_2605 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2605) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1558 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _172_2007 = (mk_term_projector_name d x)
in (_172_2007, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1559 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _172_2009 = (let _172_2008 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _172_2008, true))
in (FStar_All.pipe_right _172_2009 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1560 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1561 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1562 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1563 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1565 "FStar.SMTEncoding.Encode.fst"
let _83_2615 = (encode_term_pred None t env ddtok_tm)
in (match (_83_2615) with
| (tok_typing, decls3) -> begin
(
# 1567 "FStar.SMTEncoding.Encode.fst"
let _83_2622 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2622) with
| (vars', guards', env'', decls_formals, _83_2621) -> begin
(
# 1568 "FStar.SMTEncoding.Encode.fst"
let _83_2627 = (
# 1569 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1570 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_83_2627) with
| (ty_pred', decls_pred) -> begin
(
# 1572 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1573 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _83_2631 -> begin
(let _172_2011 = (let _172_2010 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _172_2010))
in (_172_2011)::[])
end)
in (
# 1577 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _83_2634 -> (match (()) with
| () -> begin
(
# 1578 "FStar.SMTEncoding.Encode.fst"
let _83_2637 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_83_2637) with
| (head, args) -> begin
(match ((let _172_2014 = (FStar_Syntax_Subst.compress head)
in _172_2014.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(
# 1582 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (
# 1583 "FStar.SMTEncoding.Encode.fst"
let _83_2655 = (encode_args args env')
in (match (_83_2655) with
| (encoded_args, arg_decls) -> begin
(
# 1584 "FStar.SMTEncoding.Encode.fst"
let _83_2670 = (FStar_List.fold_left (fun _83_2659 arg -> (match (_83_2659) with
| (env, arg_vars, eqns) -> begin
(
# 1585 "FStar.SMTEncoding.Encode.fst"
let _83_2665 = (let _172_2017 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _172_2017))
in (match (_83_2665) with
| (_83_2662, xv, env) -> begin
(let _172_2019 = (let _172_2018 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_172_2018)::eqns)
in (env, (xv)::arg_vars, _172_2019))
end))
end)) (env', [], []) encoded_args)
in (match (_83_2670) with
| (_83_2667, arg_vars, eqns) -> begin
(
# 1587 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1588 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1589 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1590 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1591 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1592 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1593 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _172_2026 = (let _172_2025 = (let _172_2024 = (let _172_2023 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _172_2022 = (let _172_2021 = (let _172_2020 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _172_2020))
in (FStar_SMTEncoding_Term.mkImp _172_2021))
in (((ty_pred)::[])::[], _172_2023, _172_2022)))
in (FStar_SMTEncoding_Term.mkForall _172_2024))
in (_172_2025, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_172_2026))
in (
# 1598 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1600 "FStar.SMTEncoding.Encode.fst"
let x = (let _172_2027 = (varops.fresh "x")
in (_172_2027, FStar_SMTEncoding_Term.Term_sort))
in (
# 1601 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _172_2037 = (let _172_2036 = (let _172_2035 = (let _172_2034 = (let _172_2029 = (let _172_2028 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_172_2028)::[])
in (_172_2029)::[])
in (let _172_2033 = (let _172_2032 = (let _172_2031 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _172_2030 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_172_2031, _172_2030)))
in (FStar_SMTEncoding_Term.mkImp _172_2032))
in (_172_2034, (x)::[], _172_2033)))
in (FStar_SMTEncoding_Term.mkForall _172_2035))
in (_172_2036, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_172_2037))))
end else begin
(
# 1604 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _172_2040 = (let _172_2039 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _172_2039 dapp))
in (_172_2040)::[])
end
| _83_2684 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _172_2047 = (let _172_2046 = (let _172_2045 = (let _172_2044 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _172_2043 = (let _172_2042 = (let _172_2041 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _172_2041))
in (FStar_SMTEncoding_Term.mkImp _172_2042))
in (((ty_pred)::[])::[], _172_2044, _172_2043)))
in (FStar_SMTEncoding_Term.mkForall _172_2045))
in (_172_2046, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_172_2047)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _83_2688 -> begin
(
# 1612 "FStar.SMTEncoding.Encode.fst"
let _83_2689 = (let _172_2050 = (let _172_2049 = (FStar_Syntax_Print.lid_to_string d)
in (let _172_2048 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _172_2049 _172_2048)))
in (FStar_TypeChecker_Errors.warn drange _172_2050))
in ([], []))
end)
end))
end))
in (
# 1615 "FStar.SMTEncoding.Encode.fst"
let _83_2693 = (encode_elim ())
in (match (_83_2693) with
| (decls2, elim) -> begin
(
# 1616 "FStar.SMTEncoding.Encode.fst"
let g = (let _172_2075 = (let _172_2074 = (let _172_2059 = (let _172_2058 = (let _172_2057 = (let _172_2056 = (let _172_2055 = (let _172_2054 = (let _172_2053 = (let _172_2052 = (let _172_2051 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _172_2051))
in Some (_172_2052))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _172_2053))
in FStar_SMTEncoding_Term.DeclFun (_172_2054))
in (_172_2055)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _172_2056))
in (FStar_List.append _172_2057 proxy_fresh))
in (FStar_List.append _172_2058 decls_formals))
in (FStar_List.append _172_2059 decls_pred))
in (let _172_2073 = (let _172_2072 = (let _172_2071 = (let _172_2063 = (let _172_2062 = (let _172_2061 = (let _172_2060 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _172_2060))
in (FStar_SMTEncoding_Term.mkForall _172_2061))
in (_172_2062, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_172_2063))
in (let _172_2070 = (let _172_2069 = (let _172_2068 = (let _172_2067 = (let _172_2066 = (let _172_2065 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _172_2064 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _172_2065, _172_2064)))
in (FStar_SMTEncoding_Term.mkForall _172_2066))
in (_172_2067, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_172_2068))
in (_172_2069)::[])
in (_172_2071)::_172_2070))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_172_2072)
in (FStar_List.append _172_2074 _172_2073)))
in (FStar_List.append _172_2075 elim))
in ((FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end)))))
and declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(
# 1634 "FStar.SMTEncoding.Encode.fst"
let _83_2702 = (encode_free_var env x t t_norm [])
in (match (_83_2702) with
| (decls, env) -> begin
(
# 1635 "FStar.SMTEncoding.Encode.fst"
let _83_2707 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2707) with
| (n, x', _83_2706) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _83_2711) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (
# 1641 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1642 "FStar.SMTEncoding.Encode.fst"
let _83_2720 = (encode_function_type_as_formula None None t env)
in (match (_83_2720) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (
# 1646 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _172_2088 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _172_2088)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1649 "FStar.SMTEncoding.Encode.fst"
let _83_2730 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2730) with
| (vname, vtok, env) -> begin
(
# 1650 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _172_2089 = (FStar_Syntax_Subst.compress t_norm)
in _172_2089.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _83_2733) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _83_2736 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _83_2739 -> begin
[]
end)
in (
# 1653 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1654 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1657 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1658 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1659 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1661 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1662 "FStar.SMTEncoding.Encode.fst"
let _83_2754 = (
# 1663 "FStar.SMTEncoding.Encode.fst"
let _83_2749 = (curried_arrow_formals_comp t_norm)
in (match (_83_2749) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _172_2091 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _172_2091))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_83_2754) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1667 "FStar.SMTEncoding.Encode.fst"
let _83_2758 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2758) with
| (vname, vtok, env) -> begin
(
# 1668 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2761 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1671 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _83_20 -> (match (_83_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1673 "FStar.SMTEncoding.Encode.fst"
let _83_2777 = (FStar_Util.prefix vars)
in (match (_83_2777) with
| (_83_2772, (xxsym, _83_2775)) -> begin
(
# 1674 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _172_2108 = (let _172_2107 = (let _172_2106 = (let _172_2105 = (let _172_2104 = (let _172_2103 = (let _172_2102 = (let _172_2101 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_2101))
in (vapp, _172_2102))
in (FStar_SMTEncoding_Term.mkEq _172_2103))
in (((vapp)::[])::[], vars, _172_2104))
in (FStar_SMTEncoding_Term.mkForall _172_2105))
in (_172_2106, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_172_2107))
in (_172_2108)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1679 "FStar.SMTEncoding.Encode.fst"
let _83_2789 = (FStar_Util.prefix vars)
in (match (_83_2789) with
| (_83_2784, (xxsym, _83_2787)) -> begin
(
# 1680 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1681 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1682 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _172_2110 = (let _172_2109 = (mk_term_projector_name d f)
in (_172_2109, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _172_2110))
in (let _172_2115 = (let _172_2114 = (let _172_2113 = (let _172_2112 = (let _172_2111 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _172_2111))
in (FStar_SMTEncoding_Term.mkForall _172_2112))
in (_172_2113, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_172_2114))
in (_172_2115)::[]))))
end))
end
| _83_2794 -> begin
[]
end)))))
in (
# 1686 "FStar.SMTEncoding.Encode.fst"
let _83_2801 = (encode_binders None formals env)
in (match (_83_2801) with
| (vars, guards, env', decls1, _83_2800) -> begin
(
# 1687 "FStar.SMTEncoding.Encode.fst"
let _83_2810 = (match (pre_opt) with
| None -> begin
(let _172_2116 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_2116, decls1))
end
| Some (p) -> begin
(
# 1689 "FStar.SMTEncoding.Encode.fst"
let _83_2807 = (encode_formula p env')
in (match (_83_2807) with
| (g, ds) -> begin
(let _172_2117 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_172_2117, (FStar_List.append decls1 ds)))
end))
end)
in (match (_83_2810) with
| (guard, decls1) -> begin
(
# 1690 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1692 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _172_2119 = (let _172_2118 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _172_2118))
in (FStar_SMTEncoding_Term.mkApp _172_2119))
in (
# 1693 "FStar.SMTEncoding.Encode.fst"
let _83_2834 = (
# 1694 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _172_2122 = (let _172_2121 = (FStar_All.pipe_right formals (FStar_List.map (fun _83_2813 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _172_2121, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_2122))
in (
# 1695 "FStar.SMTEncoding.Encode.fst"
let _83_2821 = (
# 1696 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1696 "FStar.SMTEncoding.Encode.fst"
let _83_2816 = env
in {bindings = _83_2816.bindings; depth = _83_2816.depth; tcenv = _83_2816.tcenv; warn = _83_2816.warn; cache = _83_2816.cache; nolabels = _83_2816.nolabels; use_zfuel_name = _83_2816.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_83_2821) with
| (tok_typing, decls2) -> begin
(
# 1700 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1701 "FStar.SMTEncoding.Encode.fst"
let _83_2831 = (match (formals) with
| [] -> begin
(let _172_2126 = (let _172_2125 = (let _172_2124 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _172_2123 -> Some (_172_2123)) _172_2124))
in (push_free_var env lid vname _172_2125))
in ((FStar_List.append decls2 ((tok_typing)::[])), _172_2126))
end
| _83_2825 -> begin
(
# 1704 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1705 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _172_2127 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _172_2127))
in (
# 1706 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _172_2131 = (let _172_2130 = (let _172_2129 = (let _172_2128 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _172_2128))
in (FStar_SMTEncoding_Term.mkForall _172_2129))
in (_172_2130, Some ("Name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_172_2131))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_83_2831) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_83_2834) with
| (decls2, env) -> begin
(
# 1709 "FStar.SMTEncoding.Encode.fst"
let _83_2842 = (
# 1710 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1711 "FStar.SMTEncoding.Encode.fst"
let _83_2838 = (encode_term res_t env')
in (match (_83_2838) with
| (encoded_res_t, decls) -> begin
(let _172_2132 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _172_2132, decls))
end)))
in (match (_83_2842) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1713 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _172_2136 = (let _172_2135 = (let _172_2134 = (let _172_2133 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _172_2133))
in (FStar_SMTEncoding_Term.mkForall _172_2134))
in (_172_2135, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_172_2136))
in (
# 1714 "FStar.SMTEncoding.Encode.fst"
let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _172_2142 = (let _172_2139 = (let _172_2138 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _172_2137 = (varops.next_id ())
in (vname, _172_2138, FStar_SMTEncoding_Term.Term_sort, _172_2137)))
in (FStar_SMTEncoding_Term.fresh_constructor _172_2139))
in (let _172_2141 = (let _172_2140 = (pretype_axiom vapp vars)
in (_172_2140)::[])
in (_172_2142)::_172_2141))
end else begin
[]
end
in (
# 1719 "FStar.SMTEncoding.Encode.fst"
let g = (let _172_2144 = (let _172_2143 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_172_2143)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _172_2144))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _83_2850 se -> (match (_83_2850) with
| (g, env) -> begin
(
# 1725 "FStar.SMTEncoding.Encode.fst"
let _83_2854 = (encode_sigelt env se)
in (match (_83_2854) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1728 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1753 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _83_2861 -> (match (_83_2861) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_83_2863) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1758 "FStar.SMTEncoding.Encode.fst"
let _83_2870 = (new_term_constant env x)
in (match (_83_2870) with
| (xxsym, xx, env') -> begin
(
# 1759 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1760 "FStar.SMTEncoding.Encode.fst"
let _83_2872 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _172_2159 = (FStar_Syntax_Print.bv_to_string x)
in (let _172_2158 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _172_2157 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _172_2159 _172_2158 _172_2157))))
end else begin
()
end
in (
# 1762 "FStar.SMTEncoding.Encode.fst"
let _83_2876 = (encode_term_pred None t1 env xx)
in (match (_83_2876) with
| (t, decls') -> begin
(
# 1763 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _172_2163 = (let _172_2162 = (FStar_Syntax_Print.bv_to_string x)
in (let _172_2161 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _172_2160 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _172_2162 _172_2161 _172_2160))))
in Some (_172_2163))
end else begin
None
end
in (
# 1767 "FStar.SMTEncoding.Encode.fst"
let g = (let _172_2168 = (let _172_2167 = (let _172_2166 = (let _172_2165 = (FStar_All.pipe_left (fun _172_2164 -> Some (_172_2164)) (Prims.strcat "Encoding " xxsym))
in (t, _172_2165))
in FStar_SMTEncoding_Term.Assume (_172_2166))
in (_172_2167)::[])
in (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') _172_2168))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_83_2881, t)) -> begin
(
# 1773 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1774 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (
# 1776 "FStar.SMTEncoding.Encode.fst"
let _83_2890 = (encode_free_var env fv t t_norm [])
in (match (_83_2890) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1781 "FStar.SMTEncoding.Encode.fst"
let _83_2904 = (encode_sigelt env se)
in (match (_83_2904) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1786 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1787 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _83_2911 -> (match (_83_2911) with
| (l, _83_2908, _83_2910) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1788 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _83_2918 -> (match (_83_2918) with
| (l, _83_2915, _83_2917) -> begin
(let _172_2176 = (FStar_All.pipe_left (fun _172_2172 -> FStar_SMTEncoding_Term.Echo (_172_2172)) (Prims.fst l))
in (let _172_2175 = (let _172_2174 = (let _172_2173 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_172_2173))
in (_172_2174)::[])
in (_172_2176)::_172_2175))
end))))
in (prefix, suffix))))

# 1792 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1793 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _172_2181 = (let _172_2180 = (let _172_2179 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _172_2179; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_172_2180)::[])
in (FStar_ST.op_Colon_Equals last_env _172_2181)))

# 1796 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_83_2924 -> begin
(
# 1798 "FStar.SMTEncoding.Encode.fst"
let _83_2927 = e
in {bindings = _83_2927.bindings; depth = _83_2927.depth; tcenv = tcenv; warn = _83_2927.warn; cache = _83_2927.cache; nolabels = _83_2927.nolabels; use_zfuel_name = _83_2927.use_zfuel_name; encode_non_total_function_typ = _83_2927.encode_non_total_function_typ})
end))

# 1799 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _83_2933::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1802 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _83_2935 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1805 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1806 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1806 "FStar.SMTEncoding.Encode.fst"
let _83_2941 = hd
in {bindings = _83_2941.bindings; depth = _83_2941.depth; tcenv = _83_2941.tcenv; warn = _83_2941.warn; cache = refs; nolabels = _83_2941.nolabels; use_zfuel_name = _83_2941.use_zfuel_name; encode_non_total_function_typ = _83_2941.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1808 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _83_2944 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _83_2948::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1811 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _83_2950 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1812 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _83_2951 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1813 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _83_2952 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_83_2955::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _83_2960 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1819 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1820 "FStar.SMTEncoding.Encode.fst"
let _83_2962 = (init_env tcenv)
in (
# 1821 "FStar.SMTEncoding.Encode.fst"
let _83_2964 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1823 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1824 "FStar.SMTEncoding.Encode.fst"
let _83_2967 = (push_env ())
in (
# 1825 "FStar.SMTEncoding.Encode.fst"
let _83_2969 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1827 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1828 "FStar.SMTEncoding.Encode.fst"
let _83_2972 = (let _172_2202 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _172_2202))
in (
# 1829 "FStar.SMTEncoding.Encode.fst"
let _83_2974 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1831 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1832 "FStar.SMTEncoding.Encode.fst"
let _83_2977 = (mark_env ())
in (
# 1833 "FStar.SMTEncoding.Encode.fst"
let _83_2979 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1835 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1836 "FStar.SMTEncoding.Encode.fst"
let _83_2982 = (reset_mark_env ())
in (
# 1837 "FStar.SMTEncoding.Encode.fst"
let _83_2984 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1839 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1840 "FStar.SMTEncoding.Encode.fst"
let _83_2987 = (commit_mark_env ())
in (
# 1841 "FStar.SMTEncoding.Encode.fst"
let _83_2989 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1843 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1844 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _172_2218 = (let _172_2217 = (let _172_2216 = (let _172_2215 = (let _172_2214 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _172_2214 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _172_2215 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _172_2216))
in FStar_SMTEncoding_Term.Caption (_172_2217))
in (_172_2218)::decls)
end else begin
decls
end)
in (
# 1848 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1849 "FStar.SMTEncoding.Encode.fst"
let _83_2998 = (encode_sigelt env se)
in (match (_83_2998) with
| (decls, env) -> begin
(
# 1850 "FStar.SMTEncoding.Encode.fst"
let _83_2999 = (set_env env)
in (let _172_2219 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _172_2219)))
end)))))

# 1853 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1854 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1855 "FStar.SMTEncoding.Encode.fst"
let _83_3004 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _172_2224 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _172_2224))
end else begin
()
end
in (
# 1857 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1858 "FStar.SMTEncoding.Encode.fst"
let _83_3011 = (encode_signature (
# 1858 "FStar.SMTEncoding.Encode.fst"
let _83_3007 = env
in {bindings = _83_3007.bindings; depth = _83_3007.depth; tcenv = _83_3007.tcenv; warn = false; cache = _83_3007.cache; nolabels = _83_3007.nolabels; use_zfuel_name = _83_3007.use_zfuel_name; encode_non_total_function_typ = _83_3007.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_83_3011) with
| (decls, env) -> begin
(
# 1859 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1861 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1864 "FStar.SMTEncoding.Encode.fst"
let _83_3017 = (set_env (
# 1864 "FStar.SMTEncoding.Encode.fst"
let _83_3015 = env
in {bindings = _83_3015.bindings; depth = _83_3015.depth; tcenv = _83_3015.tcenv; warn = true; cache = _83_3015.cache; nolabels = _83_3015.nolabels; use_zfuel_name = _83_3015.use_zfuel_name; encode_non_total_function_typ = _83_3015.encode_non_total_function_typ}))
in (
# 1865 "FStar.SMTEncoding.Encode.fst"
let _83_3019 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1866 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1869 "FStar.SMTEncoding.Encode.fst"
let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (
# 1870 "FStar.SMTEncoding.Encode.fst"
let _83_3025 = (let _172_2243 = (let _172_2242 = (let _172_2241 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _172_2241))
in (FStar_Util.format1 "Starting query at %s" _172_2242))
in (push _172_2243))
in (
# 1871 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _83_3028 -> (match (()) with
| () -> begin
(let _172_2248 = (let _172_2247 = (let _172_2246 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _172_2246))
in (FStar_Util.format1 "Ending query at %s" _172_2247))
in (pop _172_2248))
end))
in (
# 1872 "FStar.SMTEncoding.Encode.fst"
let _83_3082 = (
# 1873 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1874 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1875 "FStar.SMTEncoding.Encode.fst"
let _83_3052 = (
# 1876 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1878 "FStar.SMTEncoding.Encode.fst"
let _83_3041 = (aux rest)
in (match (_83_3041) with
| (out, rest) -> begin
(
# 1879 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _172_2254 = (let _172_2253 = (FStar_Syntax_Syntax.mk_binder (
# 1880 "FStar.SMTEncoding.Encode.fst"
let _83_3043 = x
in {FStar_Syntax_Syntax.ppname = _83_3043.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_3043.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_172_2253)::out)
in (_172_2254, rest)))
end))
end
| _83_3046 -> begin
([], bindings)
end))
in (
# 1882 "FStar.SMTEncoding.Encode.fst"
let _83_3049 = (aux bindings)
in (match (_83_3049) with
| (closing, bindings) -> begin
(let _172_2255 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_172_2255, bindings))
end)))
in (match (_83_3052) with
| (q, bindings) -> begin
(
# 1884 "FStar.SMTEncoding.Encode.fst"
let _83_3061 = (let _172_2257 = (FStar_List.filter (fun _83_21 -> (match (_83_21) with
| FStar_TypeChecker_Env.Binding_sig (_83_3055) -> begin
false
end
| _83_3058 -> begin
true
end)) bindings)
in (encode_env_bindings env _172_2257))
in (match (_83_3061) with
| (env_decls, env) -> begin
(
# 1885 "FStar.SMTEncoding.Encode.fst"
let _83_3062 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _172_2258 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _172_2258))
end else begin
()
end
in (
# 1888 "FStar.SMTEncoding.Encode.fst"
let _83_3066 = (encode_formula q env)
in (match (_83_3066) with
| (phi, qdecls) -> begin
(
# 1889 "FStar.SMTEncoding.Encode.fst"
let _83_3071 = (let _172_2259 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _172_2259 phi))
in (match (_83_3071) with
| (phi, labels, _83_3070) -> begin
(
# 1890 "FStar.SMTEncoding.Encode.fst"
let _83_3074 = (encode_labels labels)
in (match (_83_3074) with
| (label_prefix, label_suffix) -> begin
(
# 1891 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1895 "FStar.SMTEncoding.Encode.fst"
let qry = (let _172_2261 = (let _172_2260 = (FStar_SMTEncoding_Term.mkNot phi)
in (_172_2260, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_172_2261))
in (
# 1896 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_83_3082) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _83_3089); FStar_SMTEncoding_Term.hash = _83_3086; FStar_SMTEncoding_Term.freevars = _83_3084}, _83_3094) -> begin
(
# 1899 "FStar.SMTEncoding.Encode.fst"
let _83_3097 = (pop ())
in ())
end
| _83_3100 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1900 "FStar.SMTEncoding.Encode.fst"
let _83_3101 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _83_3105) -> begin
(
# 1902 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1903 "FStar.SMTEncoding.Encode.fst"
let _83_3109 = (FStar_SMTEncoding_ErrorReporting.askZ3_and_report_errors tcenv fresh labels prefix qry suffix)
in (pop ())))
end
| _83_3112 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1909 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1910 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1911 "FStar.SMTEncoding.Encode.fst"
let _83_3116 = (push "query")
in (
# 1912 "FStar.SMTEncoding.Encode.fst"
let _83_3121 = (encode_formula q env)
in (match (_83_3121) with
| (f, _83_3120) -> begin
(
# 1913 "FStar.SMTEncoding.Encode.fst"
let _83_3122 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_3126) -> begin
true
end
| _83_3130 -> begin
false
end))
end)))))

# 1918 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1932 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _83_3131 -> ()); FStar_TypeChecker_Env.push = (fun _83_3133 -> ()); FStar_TypeChecker_Env.pop = (fun _83_3135 -> ()); FStar_TypeChecker_Env.mark = (fun _83_3137 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _83_3139 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _83_3141 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _83_3143 _83_3145 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _83_3147 _83_3149 -> ()); FStar_TypeChecker_Env.solve = (fun _83_3151 _83_3153 _83_3155 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _83_3157 _83_3159 -> false); FStar_TypeChecker_Env.finish = (fun _83_3161 -> ()); FStar_TypeChecker_Env.refresh = (fun _83_3162 -> ())}





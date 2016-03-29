
open Prims
# 32 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 34 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _73_27 -> (match (_73_27) with
| (a, b) -> begin
(a, b, c)
end))

# 35 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _73_1 -> (match (_73_1) with
| (FStar_Util.Inl (_73_31), _73_34) -> begin
false
end
| _73_37 -> begin
true
end)) args))

# 36 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _152_13 = (let _152_12 = (let _152_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _152_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_12))
in Some (_152_13))
end))

# 39 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 42 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _73_46 = a
in (let _152_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _152_20; FStar_Syntax_Syntax.index = _73_46.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _73_46.FStar_Syntax_Syntax.sort}))
in (let _152_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _152_21))))

# 45 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _73_53 -> (match (()) with
| () -> begin
(let _152_31 = (let _152_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _152_30 lid.FStar_Ident.str))
in (FStar_All.failwith _152_31))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _73_57 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_73_57) with
| (_73_55, t) -> begin
(match ((let _152_32 = (FStar_Syntax_Subst.compress t)
in _152_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _73_65 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_73_65) with
| (binders, _73_64) -> begin
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
| _73_68 -> begin
(fail ())
end)
end))))

# 56 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _152_38 = (let _152_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _152_37))
in (FStar_All.pipe_left escape _152_38)))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _152_44 = (let _152_43 = (mk_term_projector_name lid a)
in (_152_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _152_44)))

# 59 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _152_50 = (let _152_49 = (mk_term_projector_name_by_pos lid i)
in (_152_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _152_50)))

# 61 "FStar.SMTEncoding.Encode.fst"
let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

# 62 "FStar.SMTEncoding.Encode.fst"
type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}

# 65 "FStar.SMTEncoding.Encode.fst"
let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

# 76 "FStar.SMTEncoding.Encode.fst"
let varops : varops_t = (
# 78 "FStar.SMTEncoding.Encode.fst"
let initial_ctr = 100
in (
# 79 "FStar.SMTEncoding.Encode.fst"
let ctr = (FStar_Util.mk_ref initial_ctr)
in (
# 80 "FStar.SMTEncoding.Encode.fst"
let new_scope = (fun _73_92 -> (match (()) with
| () -> begin
(let _152_154 = (FStar_Util.smap_create 100)
in (let _152_153 = (FStar_Util.smap_create 100)
in (_152_154, _152_153)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _152_156 = (let _152_155 = (new_scope ())
in (_152_155)::[])
in (FStar_Util.mk_ref _152_156))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _152_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _152_160 (fun _73_100 -> (match (_73_100) with
| (names, _73_99) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_73_103) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _73_105 = (FStar_Util.incr ctr)
in (let _152_162 = (let _152_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _152_161))
in (Prims.strcat (Prims.strcat y "__") _152_162)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _152_164 = (let _152_163 = (FStar_ST.read scopes)
in (FStar_List.hd _152_163))
in (FStar_All.pipe_left Prims.fst _152_164))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _73_109 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _152_171 = (let _152_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _152_169 "__"))
in (let _152_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _152_171 _152_170))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _73_117 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _73_118 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _152_179 = (let _152_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _152_178))
in (FStar_Util.format2 "%s_%s" pfx _152_179)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _152_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _152_183 (fun _73_127 -> (match (_73_127) with
| (_73_125, strings) -> begin
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
let f = (let _152_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _152_184))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _152_186 = (let _152_185 = (FStar_ST.read scopes)
in (FStar_List.hd _152_185))
in (FStar_All.pipe_left Prims.snd _152_186))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _73_134 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _73_137 -> (match (()) with
| () -> begin
(let _152_191 = (let _152_190 = (new_scope ())
in (let _152_189 = (FStar_ST.read scopes)
in (_152_190)::_152_189))
in (FStar_ST.op_Colon_Equals scopes _152_191))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _73_139 -> (match (()) with
| () -> begin
(let _152_195 = (let _152_194 = (FStar_ST.read scopes)
in (FStar_List.tl _152_194))
in (FStar_ST.op_Colon_Equals scopes _152_195))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _73_141 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _73_143 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _73_145 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _73_158 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _73_163 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _73_166 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 120 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _73_168 = x
in (let _152_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _152_210; FStar_Syntax_Syntax.index = _73_168.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _73_168.FStar_Syntax_Syntax.sort})))

# 122 "FStar.SMTEncoding.Encode.fst"
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
| Binding_var (_73_172) -> begin
_73_172
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_73_175) -> begin
_73_175
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 131 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 141 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _152_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _73_2 -> (match (_73_2) with
| Binding_var (x, _73_190) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _73_195, _73_197, _73_199) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _152_268 (FStar_String.concat ", "))))

# 145 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 147 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _152_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_152_278))
end else begin
None
end)

# 152 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _152_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _152_283))))

# 154 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _152_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _152_288))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _73_213 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _73_213.tcenv; warn = _73_213.warn; cache = _73_213.cache; nolabels = _73_213.nolabels; use_zfuel_name = _73_213.use_zfuel_name; encode_non_total_function_typ = _73_213.encode_non_total_function_typ})))))

# 161 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _73_219 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _73_219.depth; tcenv = _73_219.tcenv; warn = _73_219.warn; cache = _73_219.cache; nolabels = _73_219.nolabels; use_zfuel_name = _73_219.use_zfuel_name; encode_non_total_function_typ = _73_219.encode_non_total_function_typ})))))

# 165 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _73_224 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _73_224.depth; tcenv = _73_224.tcenv; warn = _73_224.warn; cache = _73_224.cache; nolabels = _73_224.nolabels; use_zfuel_name = _73_224.use_zfuel_name; encode_non_total_function_typ = _73_224.encode_non_total_function_typ}))

# 167 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _73_3 -> (match (_73_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _73_234 -> begin
None
end)))) with
| None -> begin
(let _152_305 = (let _152_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _152_304))
in (FStar_All.failwith _152_305))
end
| Some (b, t) -> begin
t
end))

# 171 "FStar.SMTEncoding.Encode.fst"
let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (
# 175 "FStar.SMTEncoding.Encode.fst"
let fname = (varops.new_fvar x)
in (
# 176 "FStar.SMTEncoding.Encode.fst"
let ftok = (Prims.strcat fname "@tok")
in (let _152_316 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _73_244 = env
in (let _152_315 = (let _152_314 = (let _152_313 = (let _152_312 = (let _152_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _152_310 -> Some (_152_310)) _152_311))
in (x, fname, _152_312, None))
in Binding_fvar (_152_313))
in (_152_314)::env.bindings)
in {bindings = _152_315; depth = _73_244.depth; tcenv = _73_244.tcenv; warn = _73_244.warn; cache = _73_244.cache; nolabels = _73_244.nolabels; use_zfuel_name = _73_244.use_zfuel_name; encode_non_total_function_typ = _73_244.encode_non_total_function_typ}))
in (fname, ftok, _152_316)))))

# 178 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _73_4 -> (match (_73_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _73_256 -> begin
None
end))))

# 180 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _152_327 = (let _152_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _152_326))
in (FStar_All.failwith _152_327))
end
| Some (s) -> begin
s
end))

# 184 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _73_266 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _73_266.depth; tcenv = _73_266.tcenv; warn = _73_266.warn; cache = _73_266.cache; nolabels = _73_266.nolabels; use_zfuel_name = _73_266.use_zfuel_name; encode_non_total_function_typ = _73_266.encode_non_total_function_typ}))

# 186 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _73_275 = (lookup_lid env x)
in (match (_73_275) with
| (t1, t2, _73_274) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _152_344 = (let _152_343 = (let _152_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_152_342)::[])
in (f, _152_343))
in (FStar_SMTEncoding_Term.mkApp _152_344))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _73_277 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _73_277.depth; tcenv = _73_277.tcenv; warn = _73_277.warn; cache = _73_277.cache; nolabels = _73_277.nolabels; use_zfuel_name = _73_277.use_zfuel_name; encode_non_total_function_typ = _73_277.encode_non_total_function_typ}))
end)))

# 190 "FStar.SMTEncoding.Encode.fst"
let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| _73_290 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_73_294, fuel::[]) -> begin
if (let _152_350 = (let _152_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _152_349 Prims.fst))
in (FStar_Util.starts_with _152_350 "fuel")) then begin
(let _152_353 = (let _152_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _152_352 fuel))
in (FStar_All.pipe_left (fun _152_351 -> Some (_152_351)) _152_353))
end else begin
Some (t)
end
end
| _73_300 -> begin
Some (t)
end)
end
| _73_302 -> begin
None
end)
end)
end))

# 207 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _152_357 = (let _152_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _152_356))
in (FStar_All.failwith _152_357))
end))

# 211 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _73_315 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_73_315) with
| (x, _73_312, _73_314) -> begin
x
end)))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _73_321 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_73_321) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _73_325; FStar_SMTEncoding_Term.freevars = _73_323}) when env.use_zfuel_name -> begin
(g, zf)
end
| _73_333 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _73_343 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 223 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _73_5 -> (match (_73_5) with
| Binding_fvar (_73_348, nm', tok, _73_352) when (nm = nm') -> begin
tok
end
| _73_356 -> begin
None
end))))

# 228 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _73_361 -> (match (_73_361) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _73_363 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _73_366 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_73_366) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _73_376 -> begin
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
(let _152_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _152_374))
end
| _73_389 -> begin
(let _152_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _152_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _73_392 -> begin
body
end)
in (
# 251 "FStar.SMTEncoding.Encode.fst"
let vars = ((fsym, FStar_SMTEncoding_Term.Fuel_sort))::vars
in (FStar_SMTEncoding_Term.mkForall (pats, vars, body))))))
end))
end)
end))

# 252 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' 1)

# 254 "FStar.SMTEncoding.Encode.fst"
let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (
# 257 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _152_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _152_381 FStar_Option.isNone))
end
| _73_431 -> begin
false
end)))

# 267 "FStar.SMTEncoding.Encode.fst"
let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _152_386 = (FStar_Syntax_Util.un_uinst t)
in _152_386.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_73_435) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _152_387 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _152_387 FStar_Option.isSome))
end
| _73_440 -> begin
false
end))

# 272 "FStar.SMTEncoding.Encode.fst"
let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)

# 276 "FStar.SMTEncoding.Encode.fst"
let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))

# 277 "FStar.SMTEncoding.Encode.fst"
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _152_400 = (let _152_398 = (FStar_Syntax_Syntax.null_binder t)
in (_152_398)::[])
in (let _152_399 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _152_400 _152_399 None))))

# 282 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _152_407 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _152_407))
end
| s -> begin
(
# 287 "FStar.SMTEncoding.Encode.fst"
let _73_452 = ()
in (let _152_408 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _152_408)))
end)) e)))

# 287 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 288 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _73_6 -> (match (_73_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _73_462 -> begin
false
end))

# 293 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 296 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _73_473; FStar_SMTEncoding_Term.freevars = _73_471}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _73_491) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _73_498 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_73_500, []) -> begin
(
# 307 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _73_506 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

# 312 "FStar.SMTEncoding.Encode.fst"
type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)

# 338 "FStar.SMTEncoding.Encode.fst"
type labels =
label Prims.list

# 339 "FStar.SMTEncoding.Encode.fst"
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

# 346 "FStar.SMTEncoding.Encode.fst"
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _73_7 -> (match (_73_7) with
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
(let _152_462 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _152_462))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _152_463 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _152_463))
end
| FStar_Const.Const_int (i) -> begin
(let _152_464 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _152_464))
end
| FStar_Const.Const_int32 (i) -> begin
(let _152_468 = (let _152_467 = (let _152_466 = (let _152_465 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _152_465))
in (_152_466)::[])
in ("FStar.Int32.Int32", _152_467))
in (FStar_SMTEncoding_Term.mkApp _152_468))
end
| FStar_Const.Const_string (bytes, _73_528) -> begin
(let _152_469 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _152_469))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _152_471 = (let _152_470 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _152_470))
in (FStar_All.failwith _152_471))
end))

# 359 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 362 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 363 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_73_542) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_73_545) -> begin
(let _152_480 = (FStar_Syntax_Util.unrefine t)
in (aux true _152_480))
end
| _73_548 -> begin
if norm then begin
(let _152_481 = (whnf env t)
in (aux false _152_481))
end else begin
(let _152_484 = (let _152_483 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _152_482 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _152_483 _152_482)))
in (FStar_All.failwith _152_484))
end
end)))
in (aux true t0)))

# 370 "FStar.SMTEncoding.Encode.fst"
let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (
# 373 "FStar.SMTEncoding.Encode.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _73_556 -> begin
(let _152_487 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _152_487))
end)))

# 376 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 386 "FStar.SMTEncoding.Encode.fst"
let _73_560 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _152_535 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _152_535))
end else begin
()
end
in (
# 388 "FStar.SMTEncoding.Encode.fst"
let _73_588 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _73_567 b -> (match (_73_567) with
| (vars, guards, env, decls, names) -> begin
(
# 389 "FStar.SMTEncoding.Encode.fst"
let _73_582 = (
# 390 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 391 "FStar.SMTEncoding.Encode.fst"
let _73_573 = (gen_term_var env x)
in (match (_73_573) with
| (xxsym, xx, env') -> begin
(
# 392 "FStar.SMTEncoding.Encode.fst"
let _73_576 = (let _152_538 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _152_538 env xx))
in (match (_73_576) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_73_582) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_73_588) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 407 "FStar.SMTEncoding.Encode.fst"
let _73_595 = (encode_term t env)
in (match (_73_595) with
| (t, decls) -> begin
(let _152_543 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_152_543, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 411 "FStar.SMTEncoding.Encode.fst"
let _73_602 = (encode_term t env)
in (match (_73_602) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _152_548 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_152_548, decls))
end
| Some (f) -> begin
(let _152_549 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_152_549, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 419 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 420 "FStar.SMTEncoding.Encode.fst"
let _73_609 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _152_554 = (FStar_Syntax_Print.tag_of_term t)
in (let _152_553 = (FStar_Syntax_Print.tag_of_term t0)
in (let _152_552 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _152_554 _152_553 _152_552))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _152_559 = (let _152_558 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _152_557 = (FStar_Syntax_Print.tag_of_term t0)
in (let _152_556 = (FStar_Syntax_Print.term_to_string t0)
in (let _152_555 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _152_558 _152_557 _152_556 _152_555)))))
in (FStar_All.failwith _152_559))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _152_561 = (let _152_560 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _152_560))
in (FStar_All.failwith _152_561))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _73_620) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _73_625) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 436 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _152_562 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_152_562, []))
end
| FStar_Syntax_Syntax.Tm_type (_73_634) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _73_638) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _152_563 = (encode_const c)
in (_152_563, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 452 "FStar.SMTEncoding.Encode.fst"
let _73_649 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_73_649) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 456 "FStar.SMTEncoding.Encode.fst"
let _73_656 = (encode_binders None binders env)
in (match (_73_656) with
| (vars, guards, env', decls, _73_655) -> begin
(
# 457 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _152_564 = (varops.fresh "f")
in (_152_564, FStar_SMTEncoding_Term.Term_sort))
in (
# 458 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 459 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 460 "FStar.SMTEncoding.Encode.fst"
let _73_662 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_73_662) with
| (pre_opt, res_t) -> begin
(
# 461 "FStar.SMTEncoding.Encode.fst"
let _73_665 = (encode_term_pred None res_t env' app)
in (match (_73_665) with
| (res_pred, decls') -> begin
(
# 462 "FStar.SMTEncoding.Encode.fst"
let _73_674 = (match (pre_opt) with
| None -> begin
(let _152_565 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_152_565, decls))
end
| Some (pre) -> begin
(
# 465 "FStar.SMTEncoding.Encode.fst"
let _73_671 = (encode_formula pre env')
in (match (_73_671) with
| (guard, decls0) -> begin
(let _152_566 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_152_566, (FStar_List.append decls decls0)))
end))
end)
in (match (_73_674) with
| (guards, guard_decls) -> begin
(
# 467 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _152_568 = (let _152_567 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _152_567))
in (FStar_SMTEncoding_Term.mkForall _152_568))
in (
# 472 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _152_570 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _152_570 (FStar_List.filter (fun _73_679 -> (match (_73_679) with
| (x, _73_678) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 473 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _73_685) -> begin
(let _152_573 = (let _152_572 = (let _152_571 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _152_571))
in (FStar_SMTEncoding_Term.mkApp _152_572))
in (_152_573, []))
end
| None -> begin
(
# 479 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Tm_arrow")
in (
# 480 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 481 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _152_574 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_152_574))
end else begin
None
end
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let t = (let _152_576 = (let _152_575 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _152_575))
in (FStar_SMTEncoding_Term.mkApp _152_576))
in (
# 489 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 491 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _152_578 = (let _152_577 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_152_577, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_152_578))
in (
# 493 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 495 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _152_585 = (let _152_584 = (let _152_583 = (let _152_582 = (let _152_581 = (let _152_580 = (let _152_579 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _152_579))
in (f_has_t, _152_580))
in (FStar_SMTEncoding_Term.mkImp _152_581))
in (((f_has_t)::[])::[], (fsym)::cvars, _152_582))
in (mkForall_fuel _152_583))
in (_152_584, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_152_585))
in (
# 496 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _152_589 = (let _152_588 = (let _152_587 = (let _152_586 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _152_586))
in (FStar_SMTEncoding_Term.mkForall _152_587))
in (_152_588, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_152_589))
in (
# 499 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 500 "FStar.SMTEncoding.Encode.fst"
let _73_701 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 504 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Non_total_Tm_arrow")
in (
# 505 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 506 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (
# 507 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (let _152_591 = (let _152_590 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_152_590, Some ("Typing for non-total arrows")))
in FStar_SMTEncoding_Term.Assume (_152_591))
in (
# 508 "FStar.SMTEncoding.Encode.fst"
let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (
# 509 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 510 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 511 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _152_598 = (let _152_597 = (let _152_596 = (let _152_595 = (let _152_594 = (let _152_593 = (let _152_592 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _152_592))
in (f_has_t, _152_593))
in (FStar_SMTEncoding_Term.mkImp _152_594))
in (((f_has_t)::[])::[], (fsym)::[], _152_595))
in (mkForall_fuel _152_596))
in (_152_597, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_152_598))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_73_712) -> begin
(
# 518 "FStar.SMTEncoding.Encode.fst"
let _73_732 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _73_719; FStar_Syntax_Syntax.pos = _73_717; FStar_Syntax_Syntax.vars = _73_715} -> begin
(
# 520 "FStar.SMTEncoding.Encode.fst"
let _73_727 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_73_727) with
| (b, f) -> begin
(let _152_600 = (let _152_599 = (FStar_List.hd b)
in (Prims.fst _152_599))
in (_152_600, f))
end))
end
| _73_729 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_73_732) with
| (x, f) -> begin
(
# 524 "FStar.SMTEncoding.Encode.fst"
let _73_735 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_73_735) with
| (base_t, decls) -> begin
(
# 525 "FStar.SMTEncoding.Encode.fst"
let _73_739 = (gen_term_var env x)
in (match (_73_739) with
| (x, xtm, env') -> begin
(
# 526 "FStar.SMTEncoding.Encode.fst"
let _73_742 = (encode_formula f env')
in (match (_73_742) with
| (refinement, decls') -> begin
(
# 528 "FStar.SMTEncoding.Encode.fst"
let _73_745 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_73_745) with
| (fsym, fterm) -> begin
(
# 530 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _152_602 = (let _152_601 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_152_601, refinement))
in (FStar_SMTEncoding_Term.mkAnd _152_602))
in (
# 532 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _152_604 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _152_604 (FStar_List.filter (fun _73_750 -> (match (_73_750) with
| (y, _73_749) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 533 "FStar.SMTEncoding.Encode.fst"
let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (
# 534 "FStar.SMTEncoding.Encode.fst"
let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (
# 535 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _73_757, _73_759) -> begin
(let _152_607 = (let _152_606 = (let _152_605 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _152_605))
in (FStar_SMTEncoding_Term.mkApp _152_606))
in (_152_607, []))
end
| None -> begin
(
# 542 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Tm_refine")
in (
# 543 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 544 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 545 "FStar.SMTEncoding.Encode.fst"
let t = (let _152_609 = (let _152_608 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _152_608))
in (FStar_SMTEncoding_Term.mkApp _152_609))
in (
# 547 "FStar.SMTEncoding.Encode.fst"
let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 548 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 550 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (
# 551 "FStar.SMTEncoding.Encode.fst"
let assumption = (let _152_611 = (let _152_610 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _152_610))
in (FStar_SMTEncoding_Term.mkForall _152_611))
in (
# 553 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _152_618 = (let _152_617 = (let _152_616 = (let _152_615 = (let _152_614 = (let _152_613 = (let _152_612 = (FStar_Syntax_Print.term_to_string t0)
in Some (_152_612))
in (assumption, _152_613))
in FStar_SMTEncoding_Term.Assume (_152_614))
in (_152_615)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, Some ("refinement kinding"))))::_152_616)
in (tdecl)::_152_617)
in (FStar_List.append (FStar_List.append decls decls') _152_618))
in (
# 558 "FStar.SMTEncoding.Encode.fst"
let _73_772 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
# 563 "FStar.SMTEncoding.Encode.fst"
let ttm = (let _152_619 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _152_619))
in (
# 564 "FStar.SMTEncoding.Encode.fst"
let _73_781 = (encode_term_pred None k env ttm)
in (match (_73_781) with
| (t_has_k, decls) -> begin
(
# 565 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, Some ("Uvar typing")))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_73_784) -> begin
(
# 569 "FStar.SMTEncoding.Encode.fst"
let _73_788 = (FStar_Syntax_Util.head_and_args t0)
in (match (_73_788) with
| (head, args_e) -> begin
(match ((let _152_621 = (let _152_620 = (FStar_Syntax_Subst.compress head)
in _152_620.FStar_Syntax_Syntax.n)
in (_152_621, args_e))) with
| (_73_790, _73_792) when (head_redex env head) -> begin
(let _152_622 = (whnf env t)
in (encode_term _152_622 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), _::(v1, _)::(v2, _)::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let _73_832 = (encode_term v1 env)
in (match (_73_832) with
| (v1, decls1) -> begin
(
# 577 "FStar.SMTEncoding.Encode.fst"
let _73_835 = (encode_term v2 env)
in (match (_73_835) with
| (v2, decls2) -> begin
(let _152_623 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_152_623, (FStar_List.append decls1 decls2)))
end))
end))
end
| _73_837 -> begin
(
# 581 "FStar.SMTEncoding.Encode.fst"
let _73_840 = (encode_args args_e env)
in (match (_73_840) with
| (args, decls) -> begin
(
# 583 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 584 "FStar.SMTEncoding.Encode.fst"
let _73_845 = (encode_term head env)
in (match (_73_845) with
| (head, decls') -> begin
(
# 585 "FStar.SMTEncoding.Encode.fst"
let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(
# 589 "FStar.SMTEncoding.Encode.fst"
let _73_854 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_73_854) with
| (formals, rest) -> begin
(
# 590 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _73_858 _73_862 -> (match ((_73_858, _73_862)) with
| ((bv, _73_857), (a, _73_861)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 591 "FStar.SMTEncoding.Encode.fst"
let ty = (let _152_628 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _152_628 (FStar_Syntax_Subst.subst subst)))
in (
# 592 "FStar.SMTEncoding.Encode.fst"
let _73_867 = (encode_term_pred None ty env app_tm)
in (match (_73_867) with
| (has_type, decls'') -> begin
(
# 593 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 594 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _152_630 = (let _152_629 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_152_629, Some ("Partial app typing")))
in FStar_SMTEncoding_Term.Assume (_152_630))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 598 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 599 "FStar.SMTEncoding.Encode.fst"
let _73_874 = (lookup_free_var_sym env fv)
in (match (_73_874) with
| (fname, fuel_args) -> begin
(
# 600 "FStar.SMTEncoding.Encode.fst"
let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (
# 603 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Subst.compress head)
in (
# 605 "FStar.SMTEncoding.Encode.fst"
let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _152_634 = (let _152_633 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _152_633 Prims.snd))
in Some (_152_634))
end
| FStar_Syntax_Syntax.Tm_ascribed (_73_906, FStar_Util.Inl (t), _73_910) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_73_914, FStar_Util.Inr (c), _73_918) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _73_922 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 617 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _152_635 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _152_635))
in (
# 618 "FStar.SMTEncoding.Encode.fst"
let _73_930 = (curried_arrow_formals_comp head_type)
in (match (_73_930) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _73_946 -> begin
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
# 632 "FStar.SMTEncoding.Encode.fst"
let _73_955 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_73_955) with
| (bs, body, opening) -> begin
(
# 633 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _73_957 -> (match (()) with
| () -> begin
(
# 634 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 635 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, Some ("Imprecise function encoding")))
in (let _152_638 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_152_638, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 640 "FStar.SMTEncoding.Encode.fst"
let _73_961 = (let _152_640 = (let _152_639 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _152_639))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _152_640))
in (fallback ()))
end
| Some (lc) -> begin
if (let _152_641 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _152_641)) then begin
(fallback ())
end else begin
(
# 646 "FStar.SMTEncoding.Encode.fst"
let c0 = (lc.FStar_Syntax_Syntax.comp ())
in (
# 647 "FStar.SMTEncoding.Encode.fst"
let c = (FStar_Syntax_Subst.subst_comp opening c0)
in (
# 650 "FStar.SMTEncoding.Encode.fst"
let _73_973 = (encode_binders None bs env)
in (match (_73_973) with
| (vars, guards, envbody, decls, _73_972) -> begin
(
# 651 "FStar.SMTEncoding.Encode.fst"
let _73_976 = (encode_term body envbody)
in (match (_73_976) with
| (body, decls') -> begin
(
# 652 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _152_645 = (let _152_644 = (let _152_643 = (let _152_642 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_152_642, body))
in (FStar_SMTEncoding_Term.mkImp _152_643))
in ([], vars, _152_644))
in (FStar_SMTEncoding_Term.mkForall _152_645))
in (
# 653 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 654 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _73_982, _73_984) -> begin
(let _152_648 = (let _152_647 = (let _152_646 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _152_646))
in (FStar_SMTEncoding_Term.mkApp _152_647))
in (_152_648, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(
# 663 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 664 "FStar.SMTEncoding.Encode.fst"
let fsym = (varops.fresh "Exp_abs")
in (
# 665 "FStar.SMTEncoding.Encode.fst"
let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let f = (let _152_650 = (let _152_649 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _152_649))
in (FStar_SMTEncoding_Term.mkApp _152_650))
in (
# 667 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 669 "FStar.SMTEncoding.Encode.fst"
let _73_999 = (encode_term_pred None tfun env f)
in (match (_73_999) with
| (f_has_t, decls'') -> begin
(
# 670 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _152_652 = (let _152_651 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_152_651, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_152_652))
in (
# 672 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _152_659 = (let _152_658 = (let _152_657 = (let _152_656 = (let _152_655 = (let _152_654 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _152_653 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_152_654, _152_653)))
in (FStar_SMTEncoding_Term.mkImp _152_655))
in (((app)::[])::[], (FStar_List.append vars cvars), _152_656))
in (FStar_SMTEncoding_Term.mkForall _152_657))
in (_152_658, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_152_659))
in (
# 674 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 675 "FStar.SMTEncoding.Encode.fst"
let _73_1003 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end))))))))
end)
end))))
end))
end))))
end
end))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_73_1006, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_73_1018); FStar_Syntax_Syntax.lbunivs = _73_1016; FStar_Syntax_Syntax.lbtyp = _73_1014; FStar_Syntax_Syntax.lbeff = _73_1012; FStar_Syntax_Syntax.lbdef = _73_1010}::_73_1008), _73_1024) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _73_1033; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _73_1030; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_73_1043) -> begin
(
# 688 "FStar.SMTEncoding.Encode.fst"
let _73_1045 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 689 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 690 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _152_660 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_152_660, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 697 "FStar.SMTEncoding.Encode.fst"
let _73_1061 = (encode_term e1 env)
in (match (_73_1061) with
| (ee1, decls1) -> begin
(
# 698 "FStar.SMTEncoding.Encode.fst"
let _73_1064 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_73_1064) with
| (xs, e2) -> begin
(
# 699 "FStar.SMTEncoding.Encode.fst"
let _73_1068 = (FStar_List.hd xs)
in (match (_73_1068) with
| (x, _73_1067) -> begin
(
# 700 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 701 "FStar.SMTEncoding.Encode.fst"
let _73_1072 = (encode_body e2 env')
in (match (_73_1072) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 705 "FStar.SMTEncoding.Encode.fst"
let _73_1080 = (encode_term e env)
in (match (_73_1080) with
| (scr, decls) -> begin
(
# 706 "FStar.SMTEncoding.Encode.fst"
let _73_1117 = (FStar_List.fold_right (fun b _73_1084 -> (match (_73_1084) with
| (else_case, decls) -> begin
(
# 707 "FStar.SMTEncoding.Encode.fst"
let _73_1088 = (FStar_Syntax_Subst.open_branch b)
in (match (_73_1088) with
| (p, w, br) -> begin
(
# 708 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _73_1092 _73_1095 -> (match ((_73_1092, _73_1095)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 710 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 711 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 712 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _73_1101 -> (match (_73_1101) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 713 "FStar.SMTEncoding.Encode.fst"
let _73_1111 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 716 "FStar.SMTEncoding.Encode.fst"
let _73_1108 = (encode_term w env)
in (match (_73_1108) with
| (w, decls2) -> begin
(let _152_694 = (let _152_693 = (let _152_692 = (let _152_691 = (let _152_690 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _152_690))
in (FStar_SMTEncoding_Term.mkEq _152_691))
in (guard, _152_692))
in (FStar_SMTEncoding_Term.mkAnd _152_693))
in (_152_694, decls2))
end))
end)
in (match (_73_1111) with
| (guard, decls2) -> begin
(
# 718 "FStar.SMTEncoding.Encode.fst"
let _73_1114 = (encode_br br env)
in (match (_73_1114) with
| (br, decls3) -> begin
(let _152_695 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_152_695, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_73_1117) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _73_1123 -> begin
(let _152_698 = (encode_one_pat env pat)
in (_152_698)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 732 "FStar.SMTEncoding.Encode.fst"
let _73_1126 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _152_701 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _152_701))
end else begin
()
end
in (
# 733 "FStar.SMTEncoding.Encode.fst"
let _73_1130 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_73_1130) with
| (vars, pat_term) -> begin
(
# 735 "FStar.SMTEncoding.Encode.fst"
let _73_1142 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _73_1133 v -> (match (_73_1133) with
| (env, vars) -> begin
(
# 736 "FStar.SMTEncoding.Encode.fst"
let _73_1139 = (gen_term_var env v)
in (match (_73_1139) with
| (xx, _73_1137, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_73_1142) with
| (env, vars) -> begin
(
# 739 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_73_1147) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _152_709 = (let _152_708 = (encode_const c)
in (scrutinee, _152_708))
in (FStar_SMTEncoding_Term.mkEq _152_709))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(
# 747 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (
# 748 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _73_1169 -> (match (_73_1169) with
| (arg, _73_1168) -> begin
(
# 749 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _152_712 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _152_712)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 753 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_73_1176) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_73_1186) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _152_720 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _73_1196 -> (match (_73_1196) with
| (arg, _73_1195) -> begin
(
# 765 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _152_719 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _152_719)))
end))))
in (FStar_All.pipe_right _152_720 FStar_List.flatten))
end))
in (
# 769 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _73_1199 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (
# 771 "FStar.SMTEncoding.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (
# 781 "FStar.SMTEncoding.Encode.fst"
let _73_1215 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _73_1205 _73_1209 -> (match ((_73_1205, _73_1209)) with
| ((tms, decls), (t, _73_1208)) -> begin
(
# 782 "FStar.SMTEncoding.Encode.fst"
let _73_1212 = (encode_term t env)
in (match (_73_1212) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_73_1215) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 789 "FStar.SMTEncoding.Encode.fst"
let _73_1224 = (let _152_733 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _152_733))
in (match (_73_1224) with
| (head, args) -> begin
(match ((let _152_735 = (let _152_734 = (FStar_Syntax_Util.un_uinst head)
in _152_734.FStar_Syntax_Syntax.n)
in (_152_735, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _73_1228) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _73_1241::(hd, _73_1238)::(tl, _73_1234)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _152_736 = (list_elements tl)
in (hd)::_152_736)
end
| _73_1245 -> begin
(
# 794 "FStar.SMTEncoding.Encode.fst"
let _73_1246 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 796 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 797 "FStar.SMTEncoding.Encode.fst"
let _73_1252 = (let _152_739 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _152_739 FStar_Syntax_Util.head_and_args))
in (match (_73_1252) with
| (head, args) -> begin
(match ((let _152_741 = (let _152_740 = (FStar_Syntax_Util.un_uinst head)
in _152_740.FStar_Syntax_Syntax.n)
in (_152_741, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_73_1260, _73_1262)::(e, _73_1257)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _73_1270)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _73_1275 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (
# 803 "FStar.SMTEncoding.Encode.fst"
let lemma_pats = (fun p -> (
# 804 "FStar.SMTEncoding.Encode.fst"
let elts = (list_elements p)
in (
# 805 "FStar.SMTEncoding.Encode.fst"
let smt_pat_or = (fun t -> (
# 806 "FStar.SMTEncoding.Encode.fst"
let _73_1283 = (let _152_746 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _152_746 FStar_Syntax_Util.head_and_args))
in (match (_73_1283) with
| (head, args) -> begin
(match ((let _152_748 = (let _152_747 = (FStar_Syntax_Util.un_uinst head)
in _152_747.FStar_Syntax_Syntax.n)
in (_152_748, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _73_1288)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _73_1293 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _152_751 = (list_elements e)
in (FStar_All.pipe_right _152_751 (FStar_List.map (fun branch -> (let _152_750 = (list_elements branch)
in (FStar_All.pipe_right _152_750 (FStar_List.map one_pat)))))))
end
| _73_1300 -> begin
(let _152_752 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_152_752)::[])
end)
end
| _73_1302 -> begin
(let _152_753 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_152_753)::[])
end))))
in (
# 820 "FStar.SMTEncoding.Encode.fst"
let _73_1336 = (match ((let _152_754 = (FStar_Syntax_Subst.compress t)
in _152_754.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 822 "FStar.SMTEncoding.Encode.fst"
let _73_1309 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_73_1309) with
| (binders, c) -> begin
(
# 823 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _73_1321)::(post, _73_1317)::(pats, _73_1313)::[] -> begin
(
# 826 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _152_755 = (lemma_pats pats')
in (binders, pre, post, _152_755)))
end
| _73_1329 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _73_1331 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_73_1336) with
| (binders, pre, post, patterns) -> begin
(
# 834 "FStar.SMTEncoding.Encode.fst"
let _73_1343 = (encode_binders None binders env)
in (match (_73_1343) with
| (vars, guards, env, decls, _73_1342) -> begin
(
# 837 "FStar.SMTEncoding.Encode.fst"
let _73_1356 = (let _152_759 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 838 "FStar.SMTEncoding.Encode.fst"
let _73_1353 = (let _152_758 = (FStar_All.pipe_right branch (FStar_List.map (fun _73_1348 -> (match (_73_1348) with
| (t, _73_1347) -> begin
(encode_term t (
# 838 "FStar.SMTEncoding.Encode.fst"
let _73_1349 = env
in {bindings = _73_1349.bindings; depth = _73_1349.depth; tcenv = _73_1349.tcenv; warn = _73_1349.warn; cache = _73_1349.cache; nolabels = _73_1349.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _73_1349.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _152_758 FStar_List.unzip))
in (match (_73_1353) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _152_759 FStar_List.unzip))
in (match (_73_1356) with
| (pats, decls') -> begin
(
# 841 "FStar.SMTEncoding.Encode.fst"
let decls' = (FStar_List.flatten decls')
in (
# 843 "FStar.SMTEncoding.Encode.fst"
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _152_762 = (let _152_761 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _152_761 e))
in (_152_762)::p))))
end
| _73_1366 -> begin
(
# 851 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _152_768 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_152_768)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _152_770 = (let _152_769 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _152_769 tl))
in (aux _152_770 vars))
end
| _73_1378 -> begin
pats
end))
in (let _152_771 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _152_771 vars)))
end)
end)
in (
# 858 "FStar.SMTEncoding.Encode.fst"
let env = (
# 858 "FStar.SMTEncoding.Encode.fst"
let _73_1380 = env
in {bindings = _73_1380.bindings; depth = _73_1380.depth; tcenv = _73_1380.tcenv; warn = _73_1380.warn; cache = _73_1380.cache; nolabels = true; use_zfuel_name = _73_1380.use_zfuel_name; encode_non_total_function_typ = _73_1380.encode_non_total_function_typ})
in (
# 859 "FStar.SMTEncoding.Encode.fst"
let _73_1385 = (let _152_772 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _152_772 env))
in (match (_73_1385) with
| (pre, decls'') -> begin
(
# 860 "FStar.SMTEncoding.Encode.fst"
let _73_1388 = (let _152_773 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _152_773 env))
in (match (_73_1388) with
| (post, decls''') -> begin
(
# 861 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _152_778 = (let _152_777 = (let _152_776 = (let _152_775 = (let _152_774 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_152_774, post))
in (FStar_SMTEncoding_Term.mkImp _152_775))
in (pats, vars, _152_776))
in (FStar_SMTEncoding_Term.mkForall _152_777))
in (_152_778, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 865 "FStar.SMTEncoding.Encode.fst"
let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _152_784 = (FStar_Syntax_Print.tag_of_term phi)
in (let _152_783 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _152_784 _152_783)))
end else begin
()
end)
in (
# 870 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 871 "FStar.SMTEncoding.Encode.fst"
let _73_1404 = (FStar_Util.fold_map (fun decls x -> (
# 871 "FStar.SMTEncoding.Encode.fst"
let _73_1401 = (encode_term (Prims.fst x) env)
in (match (_73_1401) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_73_1404) with
| (decls, args) -> begin
(let _152_800 = (f args)
in (_152_800, decls))
end)))
in (
# 874 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _73_1407 -> (f, []))
in (
# 875 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _152_814 = (FStar_List.hd l)
in (FStar_All.pipe_left f _152_814)))
in (
# 876 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _73_8 -> (match (_73_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _73_1418 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 880 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 881 "FStar.SMTEncoding.Encode.fst"
let _73_1435 = (FStar_List.fold_right (fun _73_1426 _73_1429 -> (match ((_73_1426, _73_1429)) with
| ((t, _73_1425), (phis, decls)) -> begin
(
# 883 "FStar.SMTEncoding.Encode.fst"
let _73_1432 = (encode_formula t env)
in (match (_73_1432) with
| (phi, decls') -> begin
((phi)::phis, (FStar_List.append decls' decls))
end))
end)) l ([], []))
in (match (_73_1435) with
| (phis, decls) -> begin
(let _152_839 = (f phis)
in (_152_839, decls))
end)))
in (
# 888 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _73_9 -> (match (_73_9) with
| _73_1442::_73_1440::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 892 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _73_10 -> (match (_73_10) with
| (lhs, _73_1453)::(rhs, _73_1449)::[] -> begin
(
# 894 "FStar.SMTEncoding.Encode.fst"
let _73_1458 = (encode_formula rhs env)
in (match (_73_1458) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _73_1461) -> begin
(l1, decls1)
end
| _73_1465 -> begin
(
# 898 "FStar.SMTEncoding.Encode.fst"
let _73_1468 = (encode_formula lhs env)
in (match (_73_1468) with
| (l2, decls2) -> begin
(let _152_844 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_152_844, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _73_1470 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 903 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _73_11 -> (match (_73_11) with
| (guard, _73_1483)::(_then, _73_1479)::(_else, _73_1475)::[] -> begin
(
# 905 "FStar.SMTEncoding.Encode.fst"
let _73_1488 = (encode_formula guard env)
in (match (_73_1488) with
| (g, decls1) -> begin
(
# 906 "FStar.SMTEncoding.Encode.fst"
let _73_1491 = (encode_formula _then env)
in (match (_73_1491) with
| (t, decls2) -> begin
(
# 907 "FStar.SMTEncoding.Encode.fst"
let _73_1494 = (encode_formula _else env)
in (match (_73_1494) with
| (e, decls3) -> begin
(
# 908 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _73_1497 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 913 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _152_856 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _152_856)))
in (
# 914 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _152_909 = (let _152_865 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _152_865))
in (let _152_908 = (let _152_907 = (let _152_871 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _152_871))
in (let _152_906 = (let _152_905 = (let _152_904 = (let _152_880 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _152_880))
in (let _152_903 = (let _152_902 = (let _152_901 = (let _152_889 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _152_889))
in (_152_901)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_152_902)
in (_152_904)::_152_903))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_152_905)
in (_152_907)::_152_906))
in (_152_909)::_152_908))
in (
# 926 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 928 "FStar.SMTEncoding.Encode.fst"
let _73_1515 = (encode_formula phi' env)
in (match (_73_1515) with
| (phi, decls) -> begin
(let _152_912 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_152_912, decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 932 "FStar.SMTEncoding.Encode.fst"
let _73_1522 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_73_1522) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _73_1529; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _73_1526; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 936 "FStar.SMTEncoding.Encode.fst"
let _73_1540 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_73_1540) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 940 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _73_1557::(x, _73_1554)::(t, _73_1550)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(
# 943 "FStar.SMTEncoding.Encode.fst"
let _73_1562 = (encode_term x env)
in (match (_73_1562) with
| (x, decls) -> begin
(
# 944 "FStar.SMTEncoding.Encode.fst"
let _73_1565 = (encode_term t env)
in (match (_73_1565) with
| (t, decls') -> begin
(let _152_913 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_152_913, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _73_1583::_73_1581::(r, _73_1578)::(msg, _73_1574)::(phi, _73_1570)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _152_917 = (let _152_914 = (FStar_Syntax_Subst.compress r)
in _152_914.FStar_Syntax_Syntax.n)
in (let _152_916 = (let _152_915 = (FStar_Syntax_Subst.compress msg)
in _152_915.FStar_Syntax_Syntax.n)
in (_152_917, _152_916)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _73_1591))) -> begin
(
# 950 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _73_1598 -> begin
(fallback phi)
end)
end
| _73_1600 when (head_redex env head) -> begin
(let _152_918 = (whnf env phi)
in (encode_formula _152_918 env))
end
| _73_1602 -> begin
(
# 960 "FStar.SMTEncoding.Encode.fst"
let _73_1605 = (encode_term phi env)
in (match (_73_1605) with
| (tt, decls) -> begin
(let _152_919 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_152_919, decls))
end))
end))
end
| _73_1607 -> begin
(
# 965 "FStar.SMTEncoding.Encode.fst"
let _73_1610 = (encode_term phi env)
in (match (_73_1610) with
| (tt, decls) -> begin
(let _152_920 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_152_920, decls))
end))
end))
in (
# 968 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 969 "FStar.SMTEncoding.Encode.fst"
let _73_1622 = (encode_binders None bs env)
in (match (_73_1622) with
| (vars, guards, env, decls, _73_1621) -> begin
(
# 970 "FStar.SMTEncoding.Encode.fst"
let _73_1635 = (let _152_932 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 971 "FStar.SMTEncoding.Encode.fst"
let _73_1632 = (let _152_931 = (FStar_All.pipe_right p (FStar_List.map (fun _73_1627 -> (match (_73_1627) with
| (t, _73_1626) -> begin
(encode_term t (
# 971 "FStar.SMTEncoding.Encode.fst"
let _73_1628 = env
in {bindings = _73_1628.bindings; depth = _73_1628.depth; tcenv = _73_1628.tcenv; warn = _73_1628.warn; cache = _73_1628.cache; nolabels = _73_1628.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _73_1628.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _152_931 FStar_List.unzip))
in (match (_73_1632) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _152_932 FStar_List.unzip))
in (match (_73_1635) with
| (pats, decls') -> begin
(
# 973 "FStar.SMTEncoding.Encode.fst"
let _73_1638 = (encode_formula body env)
in (match (_73_1638) with
| (body, decls'') -> begin
(let _152_933 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _152_933, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 976 "FStar.SMTEncoding.Encode.fst"
let _73_1639 = (debug phi)
in (
# 978 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _73_1651 -> (match (_73_1651) with
| (l, _73_1650) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_73_1654, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 988 "FStar.SMTEncoding.Encode.fst"
let _73_1664 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _152_950 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _152_950))
end else begin
()
end
in (
# 991 "FStar.SMTEncoding.Encode.fst"
let _73_1671 = (encode_q_body env vars pats body)
in (match (_73_1671) with
| (vars, pats, guard, body, decls) -> begin
(let _152_953 = (let _152_952 = (let _152_951 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _152_951))
in (FStar_SMTEncoding_Term.mkForall _152_952))
in (_152_953, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 995 "FStar.SMTEncoding.Encode.fst"
let _73_1683 = (encode_q_body env vars pats body)
in (match (_73_1683) with
| (vars, pats, guard, body, decls) -> begin
(let _152_956 = (let _152_955 = (let _152_954 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _152_954))
in (FStar_SMTEncoding_Term.mkExists _152_955))
in (_152_956, decls))
end))
end)))))))))))))))))

# 996 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 1004 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1007 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 1011 "FStar.SMTEncoding.Encode.fst"
let _73_1689 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_73_1689) with
| (asym, a) -> begin
(
# 1012 "FStar.SMTEncoding.Encode.fst"
let _73_1692 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_73_1692) with
| (xsym, x) -> begin
(
# 1013 "FStar.SMTEncoding.Encode.fst"
let _73_1695 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_73_1695) with
| (ysym, y) -> begin
(
# 1014 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 1015 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1016 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _152_999 = (let _152_998 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _152_998))
in (FStar_SMTEncoding_Term.mkApp _152_999))
in (
# 1017 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _152_1001 = (let _152_1000 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _152_1000, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_152_1001))
in (let _152_1007 = (let _152_1006 = (let _152_1005 = (let _152_1004 = (let _152_1003 = (let _152_1002 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _152_1002))
in (FStar_SMTEncoding_Term.mkForall _152_1003))
in (_152_1004, None))
in FStar_SMTEncoding_Term.Assume (_152_1005))
in (_152_1006)::[])
in (vname_decl)::_152_1007))))
in (
# 1020 "FStar.SMTEncoding.Encode.fst"
let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1021 "FStar.SMTEncoding.Encode.fst"
let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1022 "FStar.SMTEncoding.Encode.fst"
let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1023 "FStar.SMTEncoding.Encode.fst"
let prims = (let _152_1167 = (let _152_1016 = (let _152_1015 = (let _152_1014 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1014))
in (quant axy _152_1015))
in (FStar_Syntax_Const.op_Eq, _152_1016))
in (let _152_1166 = (let _152_1165 = (let _152_1023 = (let _152_1022 = (let _152_1021 = (let _152_1020 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _152_1020))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1021))
in (quant axy _152_1022))
in (FStar_Syntax_Const.op_notEq, _152_1023))
in (let _152_1164 = (let _152_1163 = (let _152_1032 = (let _152_1031 = (let _152_1030 = (let _152_1029 = (let _152_1028 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1027 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1028, _152_1027)))
in (FStar_SMTEncoding_Term.mkLT _152_1029))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1030))
in (quant xy _152_1031))
in (FStar_Syntax_Const.op_LT, _152_1032))
in (let _152_1162 = (let _152_1161 = (let _152_1041 = (let _152_1040 = (let _152_1039 = (let _152_1038 = (let _152_1037 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1036 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1037, _152_1036)))
in (FStar_SMTEncoding_Term.mkLTE _152_1038))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1039))
in (quant xy _152_1040))
in (FStar_Syntax_Const.op_LTE, _152_1041))
in (let _152_1160 = (let _152_1159 = (let _152_1050 = (let _152_1049 = (let _152_1048 = (let _152_1047 = (let _152_1046 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1045 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1046, _152_1045)))
in (FStar_SMTEncoding_Term.mkGT _152_1047))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1048))
in (quant xy _152_1049))
in (FStar_Syntax_Const.op_GT, _152_1050))
in (let _152_1158 = (let _152_1157 = (let _152_1059 = (let _152_1058 = (let _152_1057 = (let _152_1056 = (let _152_1055 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1054 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1055, _152_1054)))
in (FStar_SMTEncoding_Term.mkGTE _152_1056))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1057))
in (quant xy _152_1058))
in (FStar_Syntax_Const.op_GTE, _152_1059))
in (let _152_1156 = (let _152_1155 = (let _152_1068 = (let _152_1067 = (let _152_1066 = (let _152_1065 = (let _152_1064 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1063 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1064, _152_1063)))
in (FStar_SMTEncoding_Term.mkSub _152_1065))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _152_1066))
in (quant xy _152_1067))
in (FStar_Syntax_Const.op_Subtraction, _152_1068))
in (let _152_1154 = (let _152_1153 = (let _152_1075 = (let _152_1074 = (let _152_1073 = (let _152_1072 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _152_1072))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _152_1073))
in (quant qx _152_1074))
in (FStar_Syntax_Const.op_Minus, _152_1075))
in (let _152_1152 = (let _152_1151 = (let _152_1084 = (let _152_1083 = (let _152_1082 = (let _152_1081 = (let _152_1080 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1079 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1080, _152_1079)))
in (FStar_SMTEncoding_Term.mkAdd _152_1081))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _152_1082))
in (quant xy _152_1083))
in (FStar_Syntax_Const.op_Addition, _152_1084))
in (let _152_1150 = (let _152_1149 = (let _152_1093 = (let _152_1092 = (let _152_1091 = (let _152_1090 = (let _152_1089 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1088 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1089, _152_1088)))
in (FStar_SMTEncoding_Term.mkMul _152_1090))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _152_1091))
in (quant xy _152_1092))
in (FStar_Syntax_Const.op_Multiply, _152_1093))
in (let _152_1148 = (let _152_1147 = (let _152_1102 = (let _152_1101 = (let _152_1100 = (let _152_1099 = (let _152_1098 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1097 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1098, _152_1097)))
in (FStar_SMTEncoding_Term.mkDiv _152_1099))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _152_1100))
in (quant xy _152_1101))
in (FStar_Syntax_Const.op_Division, _152_1102))
in (let _152_1146 = (let _152_1145 = (let _152_1111 = (let _152_1110 = (let _152_1109 = (let _152_1108 = (let _152_1107 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1106 = (FStar_SMTEncoding_Term.unboxInt y)
in (_152_1107, _152_1106)))
in (FStar_SMTEncoding_Term.mkMod _152_1108))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _152_1109))
in (quant xy _152_1110))
in (FStar_Syntax_Const.op_Modulus, _152_1111))
in (let _152_1144 = (let _152_1143 = (let _152_1120 = (let _152_1119 = (let _152_1118 = (let _152_1117 = (let _152_1116 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _152_1115 = (FStar_SMTEncoding_Term.unboxBool y)
in (_152_1116, _152_1115)))
in (FStar_SMTEncoding_Term.mkAnd _152_1117))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1118))
in (quant xy _152_1119))
in (FStar_Syntax_Const.op_And, _152_1120))
in (let _152_1142 = (let _152_1141 = (let _152_1129 = (let _152_1128 = (let _152_1127 = (let _152_1126 = (let _152_1125 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _152_1124 = (FStar_SMTEncoding_Term.unboxBool y)
in (_152_1125, _152_1124)))
in (FStar_SMTEncoding_Term.mkOr _152_1126))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1127))
in (quant xy _152_1128))
in (FStar_Syntax_Const.op_Or, _152_1129))
in (let _152_1140 = (let _152_1139 = (let _152_1136 = (let _152_1135 = (let _152_1134 = (let _152_1133 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _152_1133))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_1134))
in (quant qx _152_1135))
in (FStar_Syntax_Const.op_Negation, _152_1136))
in (_152_1139)::[])
in (_152_1141)::_152_1140))
in (_152_1143)::_152_1142))
in (_152_1145)::_152_1144))
in (_152_1147)::_152_1146))
in (_152_1149)::_152_1148))
in (_152_1151)::_152_1150))
in (_152_1153)::_152_1152))
in (_152_1155)::_152_1154))
in (_152_1157)::_152_1156))
in (_152_1159)::_152_1158))
in (_152_1161)::_152_1160))
in (_152_1163)::_152_1162))
in (_152_1165)::_152_1164))
in (_152_1167)::_152_1166))
in (
# 1040 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _152_1199 = (FStar_All.pipe_right prims (FStar_List.filter (fun _73_1715 -> (match (_73_1715) with
| (l', _73_1714) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _152_1199 (FStar_List.collect (fun _73_1719 -> (match (_73_1719) with
| (_73_1717, b) -> begin
(b v)
end))))))
in (
# 1042 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _73_1725 -> (match (_73_1725) with
| (l', _73_1724) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1045 "FStar.SMTEncoding.Encode.fst"
let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (
# 1048 "FStar.SMTEncoding.Encode.fst"
let _73_1731 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_73_1731) with
| (xxsym, xx) -> begin
(
# 1049 "FStar.SMTEncoding.Encode.fst"
let _73_1734 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_73_1734) with
| (ffsym, ff) -> begin
(
# 1050 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _152_1225 = (let _152_1224 = (let _152_1223 = (let _152_1222 = (let _152_1221 = (let _152_1220 = (let _152_1219 = (let _152_1218 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _152_1218))
in (FStar_SMTEncoding_Term.mkEq _152_1219))
in (xx_has_type, _152_1220))
in (FStar_SMTEncoding_Term.mkImp _152_1221))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _152_1222))
in (FStar_SMTEncoding_Term.mkForall _152_1223))
in (_152_1224, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_152_1225)))
end))
end)))

# 1052 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1055 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1056 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1058 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1059 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1061 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun env nm tt -> (
# 1062 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _152_1246 = (let _152_1237 = (let _152_1236 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_152_1236, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_152_1237))
in (let _152_1245 = (let _152_1244 = (let _152_1243 = (let _152_1242 = (let _152_1241 = (let _152_1240 = (let _152_1239 = (let _152_1238 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _152_1238))
in (FStar_SMTEncoding_Term.mkImp _152_1239))
in (((typing_pred)::[])::[], (xx)::[], _152_1240))
in (mkForall_fuel _152_1241))
in (_152_1242, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_152_1243))
in (_152_1244)::[])
in (_152_1246)::_152_1245))))
in (
# 1065 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun env nm tt -> (
# 1066 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1067 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1068 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _152_1269 = (let _152_1258 = (let _152_1257 = (let _152_1256 = (let _152_1255 = (let _152_1254 = (let _152_1253 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _152_1253))
in (FStar_SMTEncoding_Term.mkImp _152_1254))
in (((typing_pred)::[])::[], (xx)::[], _152_1255))
in (mkForall_fuel _152_1256))
in (_152_1257, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_152_1258))
in (let _152_1268 = (let _152_1267 = (let _152_1266 = (let _152_1265 = (let _152_1264 = (let _152_1263 = (let _152_1260 = (let _152_1259 = (FStar_SMTEncoding_Term.boxBool b)
in (_152_1259)::[])
in (_152_1260)::[])
in (let _152_1262 = (let _152_1261 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _152_1261 tt))
in (_152_1263, (bb)::[], _152_1262)))
in (FStar_SMTEncoding_Term.mkForall _152_1264))
in (_152_1265, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_152_1266))
in (_152_1267)::[])
in (_152_1269)::_152_1268))))))
in (
# 1071 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun env nm tt -> (
# 1072 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1073 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1074 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1075 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1076 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1077 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1078 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _152_1283 = (let _152_1282 = (let _152_1281 = (let _152_1280 = (let _152_1279 = (let _152_1278 = (FStar_SMTEncoding_Term.boxInt a)
in (let _152_1277 = (let _152_1276 = (FStar_SMTEncoding_Term.boxInt b)
in (_152_1276)::[])
in (_152_1278)::_152_1277))
in (tt)::_152_1279)
in (tt)::_152_1280)
in ("Prims.Precedes", _152_1281))
in (FStar_SMTEncoding_Term.mkApp _152_1282))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _152_1283))
in (
# 1079 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _152_1284 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _152_1284))
in (let _152_1326 = (let _152_1290 = (let _152_1289 = (let _152_1288 = (let _152_1287 = (let _152_1286 = (let _152_1285 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _152_1285))
in (FStar_SMTEncoding_Term.mkImp _152_1286))
in (((typing_pred)::[])::[], (xx)::[], _152_1287))
in (mkForall_fuel _152_1288))
in (_152_1289, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_152_1290))
in (let _152_1325 = (let _152_1324 = (let _152_1298 = (let _152_1297 = (let _152_1296 = (let _152_1295 = (let _152_1292 = (let _152_1291 = (FStar_SMTEncoding_Term.boxInt b)
in (_152_1291)::[])
in (_152_1292)::[])
in (let _152_1294 = (let _152_1293 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _152_1293 tt))
in (_152_1295, (bb)::[], _152_1294)))
in (FStar_SMTEncoding_Term.mkForall _152_1296))
in (_152_1297, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_152_1298))
in (let _152_1323 = (let _152_1322 = (let _152_1321 = (let _152_1320 = (let _152_1319 = (let _152_1318 = (let _152_1317 = (let _152_1316 = (let _152_1315 = (let _152_1314 = (let _152_1313 = (let _152_1312 = (let _152_1301 = (let _152_1300 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _152_1299 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_152_1300, _152_1299)))
in (FStar_SMTEncoding_Term.mkGT _152_1301))
in (let _152_1311 = (let _152_1310 = (let _152_1304 = (let _152_1303 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _152_1302 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_152_1303, _152_1302)))
in (FStar_SMTEncoding_Term.mkGTE _152_1304))
in (let _152_1309 = (let _152_1308 = (let _152_1307 = (let _152_1306 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _152_1305 = (FStar_SMTEncoding_Term.unboxInt x)
in (_152_1306, _152_1305)))
in (FStar_SMTEncoding_Term.mkLT _152_1307))
in (_152_1308)::[])
in (_152_1310)::_152_1309))
in (_152_1312)::_152_1311))
in (typing_pred_y)::_152_1313)
in (typing_pred)::_152_1314)
in (FStar_SMTEncoding_Term.mk_and_l _152_1315))
in (_152_1316, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _152_1317))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _152_1318))
in (mkForall_fuel _152_1319))
in (_152_1320, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_152_1321))
in (_152_1322)::[])
in (_152_1324)::_152_1323))
in (_152_1326)::_152_1325)))))))))))
in (
# 1091 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun env nm tt -> (let _152_1337 = (let _152_1336 = (let _152_1335 = (let _152_1334 = (let _152_1333 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _152_1333))
in (FStar_SMTEncoding_Term.mkEq _152_1334))
in (_152_1335, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_152_1336))
in (_152_1337)::[]))
in (
# 1093 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun env nm tt -> (
# 1094 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1096 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _152_1360 = (let _152_1349 = (let _152_1348 = (let _152_1347 = (let _152_1346 = (let _152_1345 = (let _152_1344 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _152_1344))
in (FStar_SMTEncoding_Term.mkImp _152_1345))
in (((typing_pred)::[])::[], (xx)::[], _152_1346))
in (mkForall_fuel _152_1347))
in (_152_1348, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_152_1349))
in (let _152_1359 = (let _152_1358 = (let _152_1357 = (let _152_1356 = (let _152_1355 = (let _152_1354 = (let _152_1351 = (let _152_1350 = (FStar_SMTEncoding_Term.boxString b)
in (_152_1350)::[])
in (_152_1351)::[])
in (let _152_1353 = (let _152_1352 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _152_1352 tt))
in (_152_1354, (bb)::[], _152_1353)))
in (FStar_SMTEncoding_Term.mkForall _152_1355))
in (_152_1356, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_152_1357))
in (_152_1358)::[])
in (_152_1360)::_152_1359))))))
in (
# 1099 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun env reft_name _73_1777 -> (
# 1100 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1101 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1102 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1103 "FStar.SMTEncoding.Encode.fst"
let refa = (let _152_1369 = (let _152_1368 = (let _152_1367 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_152_1367)::[])
in (reft_name, _152_1368))
in (FStar_SMTEncoding_Term.mkApp _152_1369))
in (
# 1104 "FStar.SMTEncoding.Encode.fst"
let refb = (let _152_1372 = (let _152_1371 = (let _152_1370 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_152_1370)::[])
in (reft_name, _152_1371))
in (FStar_SMTEncoding_Term.mkApp _152_1372))
in (
# 1105 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1106 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _152_1391 = (let _152_1378 = (let _152_1377 = (let _152_1376 = (let _152_1375 = (let _152_1374 = (let _152_1373 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _152_1373))
in (FStar_SMTEncoding_Term.mkImp _152_1374))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _152_1375))
in (mkForall_fuel _152_1376))
in (_152_1377, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_152_1378))
in (let _152_1390 = (let _152_1389 = (let _152_1388 = (let _152_1387 = (let _152_1386 = (let _152_1385 = (let _152_1384 = (let _152_1383 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _152_1382 = (let _152_1381 = (let _152_1380 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _152_1379 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_152_1380, _152_1379)))
in (FStar_SMTEncoding_Term.mkEq _152_1381))
in (_152_1383, _152_1382)))
in (FStar_SMTEncoding_Term.mkImp _152_1384))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _152_1385))
in (mkForall_fuel' 2 _152_1386))
in (_152_1387, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_152_1388))
in (_152_1389)::[])
in (_152_1391)::_152_1390))))))))))
in (
# 1109 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun env nm false_tm -> (
# 1110 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _152_1400 = (let _152_1399 = (let _152_1398 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_152_1398, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_152_1399))
in (_152_1400)::[])))
in (
# 1112 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun env conj _73_1794 -> (
# 1113 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1114 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1115 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1116 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1117 "FStar.SMTEncoding.Encode.fst"
let valid = (let _152_1409 = (let _152_1408 = (let _152_1407 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_152_1407)::[])
in ("Valid", _152_1408))
in (FStar_SMTEncoding_Term.mkApp _152_1409))
in (
# 1118 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1119 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _152_1416 = (let _152_1415 = (let _152_1414 = (let _152_1413 = (let _152_1412 = (let _152_1411 = (let _152_1410 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_152_1410, valid))
in (FStar_SMTEncoding_Term.mkIff _152_1411))
in (((valid)::[])::[], (aa)::(bb)::[], _152_1412))
in (FStar_SMTEncoding_Term.mkForall _152_1413))
in (_152_1414, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_152_1415))
in (_152_1416)::[])))))))))
in (
# 1121 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun env disj _73_1806 -> (
# 1122 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1123 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1125 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let valid = (let _152_1425 = (let _152_1424 = (let _152_1423 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_152_1423)::[])
in ("Valid", _152_1424))
in (FStar_SMTEncoding_Term.mkApp _152_1425))
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1128 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _152_1432 = (let _152_1431 = (let _152_1430 = (let _152_1429 = (let _152_1428 = (let _152_1427 = (let _152_1426 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_152_1426, valid))
in (FStar_SMTEncoding_Term.mkIff _152_1427))
in (((valid)::[])::[], (aa)::(bb)::[], _152_1428))
in (FStar_SMTEncoding_Term.mkForall _152_1429))
in (_152_1430, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_152_1431))
in (_152_1432)::[])))))))))
in (
# 1130 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun env eq2 tt -> (
# 1131 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1132 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1134 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1135 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1136 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1137 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1138 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1139 "FStar.SMTEncoding.Encode.fst"
let valid = (let _152_1441 = (let _152_1440 = (let _152_1439 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_152_1439)::[])
in ("Valid", _152_1440))
in (FStar_SMTEncoding_Term.mkApp _152_1441))
in (let _152_1448 = (let _152_1447 = (let _152_1446 = (let _152_1445 = (let _152_1444 = (let _152_1443 = (let _152_1442 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_152_1442, valid))
in (FStar_SMTEncoding_Term.mkIff _152_1443))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _152_1444))
in (FStar_SMTEncoding_Term.mkForall _152_1445))
in (_152_1446, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_152_1447))
in (_152_1448)::[])))))))))))
in (
# 1141 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun env imp tt -> (
# 1142 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1143 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1144 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1145 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let valid = (let _152_1457 = (let _152_1456 = (let _152_1455 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_152_1455)::[])
in ("Valid", _152_1456))
in (FStar_SMTEncoding_Term.mkApp _152_1457))
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1148 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _152_1464 = (let _152_1463 = (let _152_1462 = (let _152_1461 = (let _152_1460 = (let _152_1459 = (let _152_1458 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_152_1458, valid))
in (FStar_SMTEncoding_Term.mkIff _152_1459))
in (((valid)::[])::[], (aa)::(bb)::[], _152_1460))
in (FStar_SMTEncoding_Term.mkForall _152_1461))
in (_152_1462, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_152_1463))
in (_152_1464)::[])))))))))
in (
# 1150 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun env iff tt -> (
# 1151 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1152 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1154 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1155 "FStar.SMTEncoding.Encode.fst"
let valid = (let _152_1473 = (let _152_1472 = (let _152_1471 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_152_1471)::[])
in ("Valid", _152_1472))
in (FStar_SMTEncoding_Term.mkApp _152_1473))
in (
# 1156 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1157 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _152_1480 = (let _152_1479 = (let _152_1478 = (let _152_1477 = (let _152_1476 = (let _152_1475 = (let _152_1474 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_152_1474, valid))
in (FStar_SMTEncoding_Term.mkIff _152_1475))
in (((valid)::[])::[], (aa)::(bb)::[], _152_1476))
in (FStar_SMTEncoding_Term.mkForall _152_1477))
in (_152_1478, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_152_1479))
in (_152_1480)::[])))))))))
in (
# 1159 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun env for_all tt -> (
# 1160 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1161 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1162 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1163 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1164 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1165 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1166 "FStar.SMTEncoding.Encode.fst"
let valid = (let _152_1489 = (let _152_1488 = (let _152_1487 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_152_1487)::[])
in ("Valid", _152_1488))
in (FStar_SMTEncoding_Term.mkApp _152_1489))
in (
# 1167 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _152_1492 = (let _152_1491 = (let _152_1490 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_152_1490)::[])
in ("Valid", _152_1491))
in (FStar_SMTEncoding_Term.mkApp _152_1492))
in (let _152_1506 = (let _152_1505 = (let _152_1504 = (let _152_1503 = (let _152_1502 = (let _152_1501 = (let _152_1500 = (let _152_1499 = (let _152_1498 = (let _152_1494 = (let _152_1493 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_152_1493)::[])
in (_152_1494)::[])
in (let _152_1497 = (let _152_1496 = (let _152_1495 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_152_1495, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _152_1496))
in (_152_1498, (xx)::[], _152_1497)))
in (FStar_SMTEncoding_Term.mkForall _152_1499))
in (_152_1500, valid))
in (FStar_SMTEncoding_Term.mkIff _152_1501))
in (((valid)::[])::[], (aa)::(bb)::[], _152_1502))
in (FStar_SMTEncoding_Term.mkForall _152_1503))
in (_152_1504, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_152_1505))
in (_152_1506)::[]))))))))))
in (
# 1169 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun env for_some tt -> (
# 1170 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1171 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1172 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1173 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1174 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1175 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1176 "FStar.SMTEncoding.Encode.fst"
let valid = (let _152_1515 = (let _152_1514 = (let _152_1513 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_152_1513)::[])
in ("Valid", _152_1514))
in (FStar_SMTEncoding_Term.mkApp _152_1515))
in (
# 1177 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _152_1518 = (let _152_1517 = (let _152_1516 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_152_1516)::[])
in ("Valid", _152_1517))
in (FStar_SMTEncoding_Term.mkApp _152_1518))
in (let _152_1532 = (let _152_1531 = (let _152_1530 = (let _152_1529 = (let _152_1528 = (let _152_1527 = (let _152_1526 = (let _152_1525 = (let _152_1524 = (let _152_1520 = (let _152_1519 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_152_1519)::[])
in (_152_1520)::[])
in (let _152_1523 = (let _152_1522 = (let _152_1521 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_152_1521, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _152_1522))
in (_152_1524, (xx)::[], _152_1523)))
in (FStar_SMTEncoding_Term.mkExists _152_1525))
in (_152_1526, valid))
in (FStar_SMTEncoding_Term.mkIff _152_1527))
in (((valid)::[])::[], (aa)::(bb)::[], _152_1528))
in (FStar_SMTEncoding_Term.mkForall _152_1529))
in (_152_1530, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_152_1531))
in (_152_1532)::[]))))))))))
in (
# 1179 "FStar.SMTEncoding.Encode.fst"
let mk_range_of_interp = (fun env range_of tt -> (
# 1180 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1181 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1182 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1183 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1184 "FStar.SMTEncoding.Encode.fst"
let range_of_ty = (FStar_SMTEncoding_Term.mkApp (range_of, (a)::(b)::[]))
in (let _152_1543 = (let _152_1542 = (let _152_1541 = (let _152_1540 = (let _152_1539 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_of_ty)
in (((range_of_ty)::[])::[], (aa)::(bb)::[], _152_1539))
in (FStar_SMTEncoding_Term.mkForall _152_1540))
in (_152_1541, Some ("Range_const typing")))
in FStar_SMTEncoding_Term.Assume (_152_1542))
in (_152_1543)::[])))))))
in (
# 1191 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_of_lid, mk_range_of_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _73_1892 -> (match (_73_1892) with
| (l, _73_1891) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_73_1895, f) -> begin
(f env s tt)
end))))))))))))))))))))))

# 1212 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1215 "FStar.SMTEncoding.Encode.fst"
let _73_1901 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _152_1755 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _152_1755))
end else begin
()
end
in (
# 1218 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1221 "FStar.SMTEncoding.Encode.fst"
let _73_1909 = (encode_sigelt' env se)
in (match (_73_1909) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _152_1758 = (let _152_1757 = (let _152_1756 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_152_1756))
in (_152_1757)::[])
in (_152_1758, e))
end
| _73_1912 -> begin
(let _152_1765 = (let _152_1764 = (let _152_1760 = (let _152_1759 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_152_1759))
in (_152_1760)::g)
in (let _152_1763 = (let _152_1762 = (let _152_1761 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_152_1761))
in (_152_1762)::[])
in (FStar_List.append _152_1764 _152_1763)))
in (_152_1765, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1227 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1233 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1234 "FStar.SMTEncoding.Encode.fst"
let tt = (norm env t)
in (
# 1240 "FStar.SMTEncoding.Encode.fst"
let _73_1925 = (encode_free_var env lid t tt quals)
in (match (_73_1925) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _152_1779 = (let _152_1778 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _152_1778))
in (_152_1779, env))
end else begin
(decls, env)
end
end))))
in (
# 1246 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _73_1932 lb -> (match (_73_1932) with
| (decls, env) -> begin
(
# 1248 "FStar.SMTEncoding.Encode.fst"
let _73_1936 = (let _152_1788 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _152_1788 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_73_1936) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_1954, _73_1956, _73_1958, _73_1960) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1260 "FStar.SMTEncoding.Encode.fst"
let _73_1966 = (new_term_constant_and_tok_from_lid env lid)
in (match (_73_1966) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _73_1969, t, quals, _73_1973) -> begin
(
# 1264 "FStar.SMTEncoding.Encode.fst"
let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_12 -> (match (_73_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _73_1986 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(
# 1269 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (
# 1270 "FStar.SMTEncoding.Encode.fst"
let _73_1991 = (encode_top_level_val env fv t quals)
in (match (_73_1991) with
| (decls, env) -> begin
(
# 1271 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1272 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _152_1791 = (let _152_1790 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _152_1790))
in (_152_1791, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _73_1997, _73_1999) -> begin
(
# 1278 "FStar.SMTEncoding.Encode.fst"
let _73_2004 = (encode_formula f env)
in (match (_73_2004) with
| (f, decls) -> begin
(
# 1279 "FStar.SMTEncoding.Encode.fst"
let g = (let _152_1796 = (let _152_1795 = (let _152_1794 = (let _152_1793 = (let _152_1792 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _152_1792))
in Some (_152_1793))
in (f, _152_1794))
in FStar_SMTEncoding_Term.Assume (_152_1795))
in (_152_1796)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _73_2009, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_73_2014, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _73_2022; FStar_Syntax_Syntax.lbtyp = _73_2020; FStar_Syntax_Syntax.lbeff = _73_2018; FStar_Syntax_Syntax.lbdef = _73_2016}::[]), _73_2029, _73_2031, _73_2033) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1286 "FStar.SMTEncoding.Encode.fst"
let _73_2039 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_73_2039) with
| (tname, ttok, env) -> begin
(
# 1287 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1288 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1289 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _152_1799 = (let _152_1798 = (let _152_1797 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_152_1797)::[])
in ("Valid", _152_1798))
in (FStar_SMTEncoding_Term.mkApp _152_1799))
in (
# 1290 "FStar.SMTEncoding.Encode.fst"
let decls = (let _152_1807 = (let _152_1806 = (let _152_1805 = (let _152_1804 = (let _152_1803 = (let _152_1802 = (let _152_1801 = (let _152_1800 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _152_1800))
in (FStar_SMTEncoding_Term.mkEq _152_1801))
in (((valid_b2t_x)::[])::[], (xx)::[], _152_1802))
in (FStar_SMTEncoding_Term.mkForall _152_1803))
in (_152_1804, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_152_1805))
in (_152_1806)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_152_1807)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_73_2045, _73_2047, _73_2049, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_13 -> (match (_73_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _73_2059 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _73_2065, _73_2067, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_14 -> (match (_73_14) with
| FStar_Syntax_Syntax.Projector (_73_2073) -> begin
true
end
| _73_2076 -> begin
false
end)))) -> begin
(
# 1304 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1305 "FStar.SMTEncoding.Encode.fst"
let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_73_2080) -> begin
([], env)
end
| None -> begin
(
# 1310 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _73_2088, _73_2090, quals) -> begin
(
# 1316 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1317 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1318 "FStar.SMTEncoding.Encode.fst"
let _73_2102 = (FStar_Util.first_N nbinders formals)
in (match (_73_2102) with
| (formals, extra_formals) -> begin
(
# 1319 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _73_2106 _73_2110 -> (match ((_73_2106, _73_2110)) with
| ((formal, _73_2105), (binder, _73_2109)) -> begin
(let _152_1821 = (let _152_1820 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _152_1820))
in FStar_Syntax_Syntax.NT (_152_1821))
end)) formals binders)
in (
# 1320 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _152_1825 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _73_2114 -> (match (_73_2114) with
| (x, i) -> begin
(let _152_1824 = (
# 1320 "FStar.SMTEncoding.Encode.fst"
let _73_2115 = x
in (let _152_1823 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _73_2115.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _73_2115.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_1823}))
in (_152_1824, i))
end))))
in (FStar_All.pipe_right _152_1825 FStar_Syntax_Util.name_binders))
in (
# 1321 "FStar.SMTEncoding.Encode.fst"
let body = (let _152_1832 = (FStar_Syntax_Subst.compress body)
in (let _152_1831 = (let _152_1826 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _152_1826))
in (let _152_1830 = (let _152_1829 = (let _152_1828 = (FStar_Syntax_Subst.subst subst t)
in _152_1828.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _152_1827 -> Some (_152_1827)) _152_1829))
in (FStar_Syntax_Syntax.extend_app_n _152_1832 _152_1831 _152_1830 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1324 "FStar.SMTEncoding.Encode.fst"
let destruct_bound_function = (fun flid t_norm e -> (
# 1325 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t_norm -> (match ((let _152_1843 = (FStar_Syntax_Util.unascribe e)
in _152_1843.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1328 "FStar.SMTEncoding.Encode.fst"
let _73_2134 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_73_2134) with
| (binders, body, opening) -> begin
(match ((let _152_1844 = (FStar_Syntax_Subst.compress t_norm)
in _152_1844.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1331 "FStar.SMTEncoding.Encode.fst"
let _73_2141 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_73_2141) with
| (formals, c) -> begin
(
# 1332 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1333 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1334 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1336 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1337 "FStar.SMTEncoding.Encode.fst"
let _73_2148 = (FStar_Util.first_N nformals binders)
in (match (_73_2148) with
| (bs0, rest) -> begin
(
# 1338 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1339 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _73_2152 _73_2156 -> (match ((_73_2152, _73_2156)) with
| ((b, _73_2151), (x, _73_2155)) -> begin
(let _152_1848 = (let _152_1847 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _152_1847))
in FStar_Syntax_Syntax.NT (_152_1848))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1341 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1344 "FStar.SMTEncoding.Encode.fst"
let _73_2162 = (eta_expand binders formals body tres)
in (match (_73_2162) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _73_2165) -> begin
(aux true x.FStar_Syntax_Syntax.sort)
end
| _73_2169 when (not (norm)) -> begin
(
# 1352 "FStar.SMTEncoding.Encode.fst"
let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _73_2172 -> begin
(let _152_1851 = (let _152_1850 = (FStar_Syntax_Print.term_to_string e)
in (let _152_1849 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _152_1850 _152_1849)))
in (FStar_All.failwith _152_1851))
end)
end))
end
| _73_2174 -> begin
(match ((let _152_1852 = (FStar_Syntax_Subst.compress t_norm)
in _152_1852.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1362 "FStar.SMTEncoding.Encode.fst"
let _73_2181 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_73_2181) with
| (formals, c) -> begin
(
# 1363 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1364 "FStar.SMTEncoding.Encode.fst"
let _73_2185 = (eta_expand [] formals e tres)
in (match (_73_2185) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _73_2187 -> begin
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
# 1372 "FStar.SMTEncoding.Encode.fst"
let _73_2215 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _73_2202 lb -> (match (_73_2202) with
| (toks, typs, decls, env) -> begin
(
# 1374 "FStar.SMTEncoding.Encode.fst"
let _73_2204 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1375 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1376 "FStar.SMTEncoding.Encode.fst"
let _73_2210 = (let _152_1857 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _152_1857 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_73_2210) with
| (tok, decl, env) -> begin
(let _152_1860 = (let _152_1859 = (let _152_1858 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_152_1858, tok))
in (_152_1859)::toks)
in (_152_1860, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_73_2215) with
| (toks, typs, decls, env) -> begin
(
# 1378 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1379 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1380 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_15 -> (match (_73_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _73_2222 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _152_1863 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _152_1863)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _73_2232; FStar_Syntax_Syntax.lbunivs = _73_2230; FStar_Syntax_Syntax.lbtyp = _73_2228; FStar_Syntax_Syntax.lbeff = _73_2226; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid_fv, (f, ftok))::[]) -> begin
(
# 1387 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1388 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1389 "FStar.SMTEncoding.Encode.fst"
let _73_2252 = (destruct_bound_function flid t_norm e)
in (match (_73_2252) with
| (binders, body, _73_2249, _73_2251) -> begin
(
# 1390 "FStar.SMTEncoding.Encode.fst"
let _73_2259 = (encode_binders None binders env)
in (match (_73_2259) with
| (vars, guards, env', binder_decls, _73_2258) -> begin
(
# 1391 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _73_2262 -> begin
(let _152_1865 = (let _152_1864 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _152_1864))
in (FStar_SMTEncoding_Term.mkApp _152_1865))
end)
in (
# 1392 "FStar.SMTEncoding.Encode.fst"
let _73_2268 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _152_1867 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _152_1866 = (encode_formula body env')
in (_152_1867, _152_1866)))
end else begin
(let _152_1868 = (encode_term body env')
in (app, _152_1868))
end
in (match (_73_2268) with
| (app, (body, decls2)) -> begin
(
# 1396 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _152_1877 = (let _152_1876 = (let _152_1873 = (let _152_1872 = (let _152_1871 = (let _152_1870 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _152_1869 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_152_1870, _152_1869)))
in (FStar_SMTEncoding_Term.mkImp _152_1871))
in (((app)::[])::[], vars, _152_1872))
in (FStar_SMTEncoding_Term.mkForall _152_1873))
in (let _152_1875 = (let _152_1874 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_152_1874))
in (_152_1876, _152_1875)))
in FStar_SMTEncoding_Term.Assume (_152_1877))
in (let _152_1879 = (let _152_1878 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _152_1878))
in (_152_1879, env)))
end)))
end))
end))))
end
| _73_2271 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1402 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _152_1880 = (varops.fresh "fuel")
in (_152_1880, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1403 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1404 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1405 "FStar.SMTEncoding.Encode.fst"
let _73_2289 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _73_2277 _73_2282 -> (match ((_73_2277, _73_2282)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(
# 1406 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1407 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1408 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1409 "FStar.SMTEncoding.Encode.fst"
let env = (let _152_1885 = (let _152_1884 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _152_1883 -> Some (_152_1883)) _152_1884))
in (push_free_var env flid gtok _152_1885))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_73_2289) with
| (gtoks, env) -> begin
(
# 1411 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1412 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _73_2298 t_norm _73_2309 -> (match ((_73_2298, _73_2309)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _73_2308; FStar_Syntax_Syntax.lbunivs = _73_2306; FStar_Syntax_Syntax.lbtyp = _73_2304; FStar_Syntax_Syntax.lbeff = _73_2302; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1413 "FStar.SMTEncoding.Encode.fst"
let _73_2314 = (destruct_bound_function flid t_norm e)
in (match (_73_2314) with
| (binders, body, formals, tres) -> begin
(
# 1414 "FStar.SMTEncoding.Encode.fst"
let _73_2321 = (encode_binders None binders env)
in (match (_73_2321) with
| (vars, guards, env', binder_decls, _73_2320) -> begin
(
# 1415 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _152_1896 = (let _152_1895 = (let _152_1894 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_152_1894)
in (g, _152_1895, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_152_1896))
in (
# 1416 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1417 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1418 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1419 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1420 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _152_1899 = (let _152_1898 = (let _152_1897 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_152_1897)::vars_tm)
in (g, _152_1898))
in (FStar_SMTEncoding_Term.mkApp _152_1899))
in (
# 1421 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _152_1902 = (let _152_1901 = (let _152_1900 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_152_1900)::vars_tm)
in (g, _152_1901))
in (FStar_SMTEncoding_Term.mkApp _152_1902))
in (
# 1422 "FStar.SMTEncoding.Encode.fst"
let _73_2331 = (encode_term body env')
in (match (_73_2331) with
| (body_tm, decls2) -> begin
(
# 1423 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _152_1911 = (let _152_1910 = (let _152_1907 = (let _152_1906 = (let _152_1905 = (let _152_1904 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _152_1903 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_152_1904, _152_1903)))
in (FStar_SMTEncoding_Term.mkImp _152_1905))
in (((gsapp)::[])::[], (fuel)::vars, _152_1906))
in (FStar_SMTEncoding_Term.mkForall _152_1907))
in (let _152_1909 = (let _152_1908 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_152_1908))
in (_152_1910, _152_1909)))
in FStar_SMTEncoding_Term.Assume (_152_1911))
in (
# 1425 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _152_1915 = (let _152_1914 = (let _152_1913 = (let _152_1912 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _152_1912))
in (FStar_SMTEncoding_Term.mkForall _152_1913))
in (_152_1914, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_152_1915))
in (
# 1427 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _152_1924 = (let _152_1923 = (let _152_1922 = (let _152_1921 = (let _152_1920 = (let _152_1919 = (let _152_1918 = (let _152_1917 = (let _152_1916 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_152_1916)::vars_tm)
in (g, _152_1917))
in (FStar_SMTEncoding_Term.mkApp _152_1918))
in (gsapp, _152_1919))
in (FStar_SMTEncoding_Term.mkEq _152_1920))
in (((gsapp)::[])::[], (fuel)::vars, _152_1921))
in (FStar_SMTEncoding_Term.mkForall _152_1922))
in (_152_1923, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_152_1924))
in (
# 1429 "FStar.SMTEncoding.Encode.fst"
let _73_2354 = (
# 1430 "FStar.SMTEncoding.Encode.fst"
let _73_2341 = (encode_binders None formals env0)
in (match (_73_2341) with
| (vars, v_guards, env, binder_decls, _73_2340) -> begin
(
# 1431 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1432 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1433 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1434 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _152_1925 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _152_1925 ((fuel)::vars)))
in (let _152_1929 = (let _152_1928 = (let _152_1927 = (let _152_1926 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _152_1926))
in (FStar_SMTEncoding_Term.mkForall _152_1927))
in (_152_1928, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_152_1929)))
in (
# 1437 "FStar.SMTEncoding.Encode.fst"
let _73_2351 = (
# 1438 "FStar.SMTEncoding.Encode.fst"
let _73_2348 = (encode_term_pred None tres env gapp)
in (match (_73_2348) with
| (g_typing, d3) -> begin
(let _152_1937 = (let _152_1936 = (let _152_1935 = (let _152_1934 = (let _152_1933 = (let _152_1932 = (let _152_1931 = (let _152_1930 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_152_1930, g_typing))
in (FStar_SMTEncoding_Term.mkImp _152_1931))
in (((gapp)::[])::[], (fuel)::vars, _152_1932))
in (FStar_SMTEncoding_Term.mkForall _152_1933))
in (_152_1934, Some ("Typing correspondence of token to term")))
in FStar_SMTEncoding_Term.Assume (_152_1935))
in (_152_1936)::[])
in (d3, _152_1937))
end))
in (match (_73_2351) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_73_2354) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1442 "FStar.SMTEncoding.Encode.fst"
let _73_2370 = (let _152_1940 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _73_2358 _73_2362 -> (match ((_73_2358, _73_2362)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1443 "FStar.SMTEncoding.Encode.fst"
let _73_2366 = (encode_one_binding env0 gtok ty bs)
in (match (_73_2366) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _152_1940))
in (match (_73_2370) with
| (decls, eqns, env0) -> begin
(
# 1445 "FStar.SMTEncoding.Encode.fst"
let _73_2379 = (let _152_1942 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _152_1942 (FStar_List.partition (fun _73_16 -> (match (_73_16) with
| FStar_SMTEncoding_Term.DeclFun (_73_2373) -> begin
true
end
| _73_2376 -> begin
false
end)))))
in (match (_73_2379) with
| (prefix_decls, rest) -> begin
(
# 1448 "FStar.SMTEncoding.Encode.fst"
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
# 1451 "FStar.SMTEncoding.Encode.fst"
let msg = (let _152_1945 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _152_1945 (FStar_String.concat " and ")))
in (
# 1452 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _73_2383, _73_2385, _73_2387) -> begin
(
# 1457 "FStar.SMTEncoding.Encode.fst"
let _73_2392 = (encode_signature env ses)
in (match (_73_2392) with
| (g, env) -> begin
(
# 1458 "FStar.SMTEncoding.Encode.fst"
let _73_2404 = (FStar_All.pipe_right g (FStar_List.partition (fun _73_17 -> (match (_73_17) with
| FStar_SMTEncoding_Term.Assume (_73_2395, Some ("inversion axiom")) -> begin
false
end
| _73_2401 -> begin
true
end))))
in (match (_73_2404) with
| (g', inversions) -> begin
(
# 1461 "FStar.SMTEncoding.Encode.fst"
let _73_2413 = (FStar_All.pipe_right g' (FStar_List.partition (fun _73_18 -> (match (_73_18) with
| FStar_SMTEncoding_Term.DeclFun (_73_2407) -> begin
true
end
| _73_2410 -> begin
false
end))))
in (match (_73_2413) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _73_2416, tps, k, _73_2420, datas, quals, _73_2424) -> begin
(
# 1467 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _73_19 -> (match (_73_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _73_2431 -> begin
false
end))))
in (
# 1468 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1470 "FStar.SMTEncoding.Encode.fst"
let _73_2443 = c
in (match (_73_2443) with
| (name, args, _73_2438, _73_2440, _73_2442) -> begin
(let _152_1953 = (let _152_1952 = (let _152_1951 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _152_1951, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_152_1952))
in (_152_1953)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1474 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _152_1959 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _152_1959 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1478 "FStar.SMTEncoding.Encode.fst"
let _73_2450 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_73_2450) with
| (xxsym, xx) -> begin
(
# 1479 "FStar.SMTEncoding.Encode.fst"
let _73_2486 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _73_2453 l -> (match (_73_2453) with
| (out, decls) -> begin
(
# 1480 "FStar.SMTEncoding.Encode.fst"
let _73_2458 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_73_2458) with
| (_73_2456, data_t) -> begin
(
# 1481 "FStar.SMTEncoding.Encode.fst"
let _73_2461 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_73_2461) with
| (args, res) -> begin
(
# 1482 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _152_1962 = (FStar_Syntax_Subst.compress res)
in _152_1962.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_73_2463, indices) -> begin
indices
end
| _73_2468 -> begin
[]
end)
in (
# 1485 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _73_2474 -> (match (_73_2474) with
| (x, _73_2473) -> begin
(let _152_1967 = (let _152_1966 = (let _152_1965 = (mk_term_projector_name l x)
in (_152_1965, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _152_1966))
in (push_term_var env x _152_1967))
end)) env))
in (
# 1488 "FStar.SMTEncoding.Encode.fst"
let _73_2478 = (encode_args indices env)
in (match (_73_2478) with
| (indices, decls') -> begin
(
# 1489 "FStar.SMTEncoding.Encode.fst"
let _73_2479 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1491 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _152_1972 = (FStar_List.map2 (fun v a -> (let _152_1971 = (let _152_1970 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_152_1970, a))
in (FStar_SMTEncoding_Term.mkEq _152_1971))) vars indices)
in (FStar_All.pipe_right _152_1972 FStar_SMTEncoding_Term.mk_and_l))
in (let _152_1977 = (let _152_1976 = (let _152_1975 = (let _152_1974 = (let _152_1973 = (mk_data_tester env l xx)
in (_152_1973, eqs))
in (FStar_SMTEncoding_Term.mkAnd _152_1974))
in (out, _152_1975))
in (FStar_SMTEncoding_Term.mkOr _152_1976))
in (_152_1977, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_73_2486) with
| (data_ax, decls) -> begin
(
# 1493 "FStar.SMTEncoding.Encode.fst"
let _73_2489 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_73_2489) with
| (ffsym, ff) -> begin
(
# 1494 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _152_1978 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _152_1978 xx tapp))
in (let _152_1985 = (let _152_1984 = (let _152_1983 = (let _152_1982 = (let _152_1981 = (let _152_1980 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _152_1979 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _152_1980, _152_1979)))
in (FStar_SMTEncoding_Term.mkForall _152_1981))
in (_152_1982, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_152_1983))
in (_152_1984)::[])
in (FStar_List.append decls _152_1985)))
end))
end))
end))
end)
in (
# 1498 "FStar.SMTEncoding.Encode.fst"
let _73_2499 = (match ((let _152_1986 = (FStar_Syntax_Subst.compress k)
in _152_1986.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _73_2496 -> begin
(tps, k)
end)
in (match (_73_2499) with
| (formals, res) -> begin
(
# 1504 "FStar.SMTEncoding.Encode.fst"
let _73_2502 = (FStar_Syntax_Subst.open_term formals res)
in (match (_73_2502) with
| (formals, res) -> begin
(
# 1505 "FStar.SMTEncoding.Encode.fst"
let _73_2509 = (encode_binders None formals env)
in (match (_73_2509) with
| (vars, guards, env', binder_decls, _73_2508) -> begin
(
# 1507 "FStar.SMTEncoding.Encode.fst"
let _73_2513 = (new_term_constant_and_tok_from_lid env t)
in (match (_73_2513) with
| (tname, ttok, env) -> begin
(
# 1508 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1509 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1510 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _152_1988 = (let _152_1987 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _152_1987))
in (FStar_SMTEncoding_Term.mkApp _152_1988))
in (
# 1511 "FStar.SMTEncoding.Encode.fst"
let _73_2534 = (
# 1512 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _152_1992 = (let _152_1991 = (FStar_All.pipe_right vars (FStar_List.map (fun _73_2519 -> (match (_73_2519) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _152_1990 = (varops.next_id ())
in (tname, _152_1991, FStar_SMTEncoding_Term.Term_sort, _152_1990, false)))
in (constructor_or_logic_type_decl _152_1992))
in (
# 1513 "FStar.SMTEncoding.Encode.fst"
let _73_2531 = (match (vars) with
| [] -> begin
(let _152_1996 = (let _152_1995 = (let _152_1994 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _152_1993 -> Some (_152_1993)) _152_1994))
in (push_free_var env t tname _152_1995))
in ([], _152_1996))
end
| _73_2523 -> begin
(
# 1516 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1517 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _152_1997 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _152_1997))
in (
# 1518 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1519 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1522 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _152_2001 = (let _152_2000 = (let _152_1999 = (let _152_1998 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _152_1998))
in (FStar_SMTEncoding_Term.mkForall' _152_1999))
in (_152_2000, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_152_2001))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_73_2531) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_73_2534) with
| (decls, env) -> begin
(
# 1525 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1526 "FStar.SMTEncoding.Encode.fst"
let _73_2537 = (encode_term_pred None res env' tapp)
in (match (_73_2537) with
| (k, decls) -> begin
(
# 1527 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _152_2005 = (let _152_2004 = (let _152_2003 = (let _152_2002 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _152_2002))
in (_152_2003, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_152_2004))
in (_152_2005)::[])
end else begin
[]
end
in (let _152_2011 = (let _152_2010 = (let _152_2009 = (let _152_2008 = (let _152_2007 = (let _152_2006 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _152_2006))
in (FStar_SMTEncoding_Term.mkForall _152_2007))
in (_152_2008, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_152_2009))
in (_152_2010)::[])
in (FStar_List.append (FStar_List.append decls karr) _152_2011)))
end))
in (
# 1532 "FStar.SMTEncoding.Encode.fst"
let aux = (let _152_2015 = (let _152_2012 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _152_2012))
in (let _152_2014 = (let _152_2013 = (pretype_axiom tapp vars)
in (_152_2013)::[])
in (FStar_List.append _152_2015 _152_2014)))
in (
# 1537 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _73_2544, _73_2546, _73_2548, _73_2550, _73_2552, _73_2554, _73_2556) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _73_2561, t, _73_2564, n_tps, quals, _73_2568, drange) -> begin
(
# 1545 "FStar.SMTEncoding.Encode.fst"
let _73_2575 = (new_term_constant_and_tok_from_lid env d)
in (match (_73_2575) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1546 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1547 "FStar.SMTEncoding.Encode.fst"
let _73_2579 = (FStar_Syntax_Util.arrow_formals t)
in (match (_73_2579) with
| (formals, t_res) -> begin
(
# 1548 "FStar.SMTEncoding.Encode.fst"
let _73_2582 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_73_2582) with
| (fuel_var, fuel_tm) -> begin
(
# 1549 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1550 "FStar.SMTEncoding.Encode.fst"
let _73_2589 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_73_2589) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1551 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _152_2017 = (mk_term_projector_name d x)
in (_152_2017, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1552 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _152_2019 = (let _152_2018 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _152_2018, true))
in (FStar_All.pipe_right _152_2019 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1553 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1554 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1555 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1556 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1558 "FStar.SMTEncoding.Encode.fst"
let _73_2599 = (encode_term_pred None t env ddtok_tm)
in (match (_73_2599) with
| (tok_typing, decls3) -> begin
(
# 1560 "FStar.SMTEncoding.Encode.fst"
let _73_2606 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_73_2606) with
| (vars', guards', env'', decls_formals, _73_2605) -> begin
(
# 1561 "FStar.SMTEncoding.Encode.fst"
let _73_2611 = (
# 1562 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1563 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_73_2611) with
| (ty_pred', decls_pred) -> begin
(
# 1565 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1566 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _73_2615 -> begin
(let _152_2021 = (let _152_2020 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _152_2020))
in (_152_2021)::[])
end)
in (
# 1570 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _73_2618 -> (match (()) with
| () -> begin
(
# 1571 "FStar.SMTEncoding.Encode.fst"
let _73_2621 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_73_2621) with
| (head, args) -> begin
(match ((let _152_2024 = (FStar_Syntax_Subst.compress head)
in _152_2024.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(
# 1575 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (
# 1576 "FStar.SMTEncoding.Encode.fst"
let _73_2639 = (encode_args args env')
in (match (_73_2639) with
| (encoded_args, arg_decls) -> begin
(
# 1577 "FStar.SMTEncoding.Encode.fst"
let _73_2654 = (FStar_List.fold_left (fun _73_2643 arg -> (match (_73_2643) with
| (env, arg_vars, eqns) -> begin
(
# 1578 "FStar.SMTEncoding.Encode.fst"
let _73_2649 = (let _152_2027 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _152_2027))
in (match (_73_2649) with
| (_73_2646, xv, env) -> begin
(let _152_2029 = (let _152_2028 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_152_2028)::eqns)
in (env, (xv)::arg_vars, _152_2029))
end))
end)) (env', [], []) encoded_args)
in (match (_73_2654) with
| (_73_2651, arg_vars, eqns) -> begin
(
# 1580 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1581 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1582 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1583 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1584 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1585 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1586 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _152_2036 = (let _152_2035 = (let _152_2034 = (let _152_2033 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _152_2032 = (let _152_2031 = (let _152_2030 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _152_2030))
in (FStar_SMTEncoding_Term.mkImp _152_2031))
in (((ty_pred)::[])::[], _152_2033, _152_2032)))
in (FStar_SMTEncoding_Term.mkForall _152_2034))
in (_152_2035, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_152_2036))
in (
# 1591 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1593 "FStar.SMTEncoding.Encode.fst"
let x = (let _152_2037 = (varops.fresh "x")
in (_152_2037, FStar_SMTEncoding_Term.Term_sort))
in (
# 1594 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _152_2047 = (let _152_2046 = (let _152_2045 = (let _152_2044 = (let _152_2039 = (let _152_2038 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_152_2038)::[])
in (_152_2039)::[])
in (let _152_2043 = (let _152_2042 = (let _152_2041 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _152_2040 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_152_2041, _152_2040)))
in (FStar_SMTEncoding_Term.mkImp _152_2042))
in (_152_2044, (x)::[], _152_2043)))
in (FStar_SMTEncoding_Term.mkForall _152_2045))
in (_152_2046, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_152_2047))))
end else begin
(
# 1597 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _152_2050 = (let _152_2049 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _152_2049 dapp))
in (_152_2050)::[])
end
| _73_2668 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _152_2057 = (let _152_2056 = (let _152_2055 = (let _152_2054 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _152_2053 = (let _152_2052 = (let _152_2051 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _152_2051))
in (FStar_SMTEncoding_Term.mkImp _152_2052))
in (((ty_pred)::[])::[], _152_2054, _152_2053)))
in (FStar_SMTEncoding_Term.mkForall _152_2055))
in (_152_2056, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_152_2057)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _73_2672 -> begin
(
# 1605 "FStar.SMTEncoding.Encode.fst"
let _73_2673 = (let _152_2060 = (let _152_2059 = (FStar_Syntax_Print.lid_to_string d)
in (let _152_2058 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _152_2059 _152_2058)))
in (FStar_TypeChecker_Errors.warn drange _152_2060))
in ([], []))
end)
end))
end))
in (
# 1608 "FStar.SMTEncoding.Encode.fst"
let _73_2677 = (encode_elim ())
in (match (_73_2677) with
| (decls2, elim) -> begin
(
# 1609 "FStar.SMTEncoding.Encode.fst"
let g = (let _152_2085 = (let _152_2084 = (let _152_2069 = (let _152_2068 = (let _152_2067 = (let _152_2066 = (let _152_2065 = (let _152_2064 = (let _152_2063 = (let _152_2062 = (let _152_2061 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _152_2061))
in Some (_152_2062))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _152_2063))
in FStar_SMTEncoding_Term.DeclFun (_152_2064))
in (_152_2065)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _152_2066))
in (FStar_List.append _152_2067 proxy_fresh))
in (FStar_List.append _152_2068 decls_formals))
in (FStar_List.append _152_2069 decls_pred))
in (let _152_2083 = (let _152_2082 = (let _152_2081 = (let _152_2073 = (let _152_2072 = (let _152_2071 = (let _152_2070 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _152_2070))
in (FStar_SMTEncoding_Term.mkForall _152_2071))
in (_152_2072, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_152_2073))
in (let _152_2080 = (let _152_2079 = (let _152_2078 = (let _152_2077 = (let _152_2076 = (let _152_2075 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _152_2074 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _152_2075, _152_2074)))
in (FStar_SMTEncoding_Term.mkForall _152_2076))
in (_152_2077, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_152_2078))
in (_152_2079)::[])
in (_152_2081)::_152_2080))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_152_2082)
in (FStar_List.append _152_2084 _152_2083)))
in (FStar_List.append _152_2085 elim))
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
# 1627 "FStar.SMTEncoding.Encode.fst"
let _73_2686 = (encode_free_var env x t t_norm [])
in (match (_73_2686) with
| (decls, env) -> begin
(
# 1628 "FStar.SMTEncoding.Encode.fst"
let _73_2691 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_73_2691) with
| (n, x', _73_2690) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _73_2695) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (
# 1634 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1635 "FStar.SMTEncoding.Encode.fst"
let _73_2704 = (encode_function_type_as_formula None None t env)
in (match (_73_2704) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (
# 1639 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _152_2098 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _152_2098)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1642 "FStar.SMTEncoding.Encode.fst"
let _73_2714 = (new_term_constant_and_tok_from_lid env lid)
in (match (_73_2714) with
| (vname, vtok, env) -> begin
(
# 1643 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _152_2099 = (FStar_Syntax_Subst.compress t_norm)
in _152_2099.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _73_2717) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _73_2720 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _73_2723 -> begin
[]
end)
in (
# 1646 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1647 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1650 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1651 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1652 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1654 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1655 "FStar.SMTEncoding.Encode.fst"
let _73_2738 = (
# 1656 "FStar.SMTEncoding.Encode.fst"
let _73_2733 = (curried_arrow_formals_comp t_norm)
in (match (_73_2733) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _152_2101 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _152_2101))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_73_2738) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1660 "FStar.SMTEncoding.Encode.fst"
let _73_2742 = (new_term_constant_and_tok_from_lid env lid)
in (match (_73_2742) with
| (vname, vtok, env) -> begin
(
# 1661 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _73_2745 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1664 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _73_20 -> (match (_73_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1666 "FStar.SMTEncoding.Encode.fst"
let _73_2761 = (FStar_Util.prefix vars)
in (match (_73_2761) with
| (_73_2756, (xxsym, _73_2759)) -> begin
(
# 1667 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _152_2118 = (let _152_2117 = (let _152_2116 = (let _152_2115 = (let _152_2114 = (let _152_2113 = (let _152_2112 = (let _152_2111 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _152_2111))
in (vapp, _152_2112))
in (FStar_SMTEncoding_Term.mkEq _152_2113))
in (((vapp)::[])::[], vars, _152_2114))
in (FStar_SMTEncoding_Term.mkForall _152_2115))
in (_152_2116, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_152_2117))
in (_152_2118)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1672 "FStar.SMTEncoding.Encode.fst"
let _73_2773 = (FStar_Util.prefix vars)
in (match (_73_2773) with
| (_73_2768, (xxsym, _73_2771)) -> begin
(
# 1673 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1674 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1675 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _152_2120 = (let _152_2119 = (mk_term_projector_name d f)
in (_152_2119, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _152_2120))
in (let _152_2125 = (let _152_2124 = (let _152_2123 = (let _152_2122 = (let _152_2121 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _152_2121))
in (FStar_SMTEncoding_Term.mkForall _152_2122))
in (_152_2123, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_152_2124))
in (_152_2125)::[]))))
end))
end
| _73_2778 -> begin
[]
end)))))
in (
# 1679 "FStar.SMTEncoding.Encode.fst"
let _73_2785 = (encode_binders None formals env)
in (match (_73_2785) with
| (vars, guards, env', decls1, _73_2784) -> begin
(
# 1680 "FStar.SMTEncoding.Encode.fst"
let _73_2794 = (match (pre_opt) with
| None -> begin
(let _152_2126 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_152_2126, decls1))
end
| Some (p) -> begin
(
# 1682 "FStar.SMTEncoding.Encode.fst"
let _73_2791 = (encode_formula p env')
in (match (_73_2791) with
| (g, ds) -> begin
(let _152_2127 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_152_2127, (FStar_List.append decls1 ds)))
end))
end)
in (match (_73_2794) with
| (guard, decls1) -> begin
(
# 1683 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1685 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _152_2129 = (let _152_2128 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _152_2128))
in (FStar_SMTEncoding_Term.mkApp _152_2129))
in (
# 1686 "FStar.SMTEncoding.Encode.fst"
let _73_2818 = (
# 1687 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _152_2132 = (let _152_2131 = (FStar_All.pipe_right formals (FStar_List.map (fun _73_2797 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _152_2131, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_152_2132))
in (
# 1688 "FStar.SMTEncoding.Encode.fst"
let _73_2805 = (
# 1689 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1689 "FStar.SMTEncoding.Encode.fst"
let _73_2800 = env
in {bindings = _73_2800.bindings; depth = _73_2800.depth; tcenv = _73_2800.tcenv; warn = _73_2800.warn; cache = _73_2800.cache; nolabels = _73_2800.nolabels; use_zfuel_name = _73_2800.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_73_2805) with
| (tok_typing, decls2) -> begin
(
# 1693 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1694 "FStar.SMTEncoding.Encode.fst"
let _73_2815 = (match (formals) with
| [] -> begin
(let _152_2136 = (let _152_2135 = (let _152_2134 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _152_2133 -> Some (_152_2133)) _152_2134))
in (push_free_var env lid vname _152_2135))
in ((FStar_List.append decls2 ((tok_typing)::[])), _152_2136))
end
| _73_2809 -> begin
(
# 1697 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1698 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _152_2137 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _152_2137))
in (
# 1699 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _152_2141 = (let _152_2140 = (let _152_2139 = (let _152_2138 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _152_2138))
in (FStar_SMTEncoding_Term.mkForall _152_2139))
in (_152_2140, Some ("Name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_152_2141))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_73_2815) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_73_2818) with
| (decls2, env) -> begin
(
# 1702 "FStar.SMTEncoding.Encode.fst"
let _73_2826 = (
# 1703 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1704 "FStar.SMTEncoding.Encode.fst"
let _73_2822 = (encode_term res_t env')
in (match (_73_2822) with
| (encoded_res_t, decls) -> begin
(let _152_2142 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _152_2142, decls))
end)))
in (match (_73_2826) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1706 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _152_2146 = (let _152_2145 = (let _152_2144 = (let _152_2143 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _152_2143))
in (FStar_SMTEncoding_Term.mkForall _152_2144))
in (_152_2145, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_152_2146))
in (
# 1707 "FStar.SMTEncoding.Encode.fst"
let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _152_2152 = (let _152_2149 = (let _152_2148 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _152_2147 = (varops.next_id ())
in (vname, _152_2148, FStar_SMTEncoding_Term.Term_sort, _152_2147)))
in (FStar_SMTEncoding_Term.fresh_constructor _152_2149))
in (let _152_2151 = (let _152_2150 = (pretype_axiom vapp vars)
in (_152_2150)::[])
in (_152_2152)::_152_2151))
end else begin
[]
end
in (
# 1712 "FStar.SMTEncoding.Encode.fst"
let g = (let _152_2154 = (let _152_2153 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_152_2153)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _152_2154))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _73_2834 se -> (match (_73_2834) with
| (g, env) -> begin
(
# 1718 "FStar.SMTEncoding.Encode.fst"
let _73_2838 = (encode_sigelt env se)
in (match (_73_2838) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1719 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1746 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _73_2845 -> (match (_73_2845) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_73_2847) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1751 "FStar.SMTEncoding.Encode.fst"
let _73_2854 = (new_term_constant env x)
in (match (_73_2854) with
| (xxsym, xx, env') -> begin
(
# 1752 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1753 "FStar.SMTEncoding.Encode.fst"
let _73_2856 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _152_2169 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_2168 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _152_2167 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _152_2169 _152_2168 _152_2167))))
end else begin
()
end
in (
# 1755 "FStar.SMTEncoding.Encode.fst"
let _73_2860 = (encode_term_pred None t1 env xx)
in (match (_73_2860) with
| (t, decls') -> begin
(
# 1756 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _152_2173 = (let _152_2172 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_2171 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _152_2170 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _152_2172 _152_2171 _152_2170))))
in Some (_152_2173))
end else begin
None
end
in (
# 1760 "FStar.SMTEncoding.Encode.fst"
let g = (let _152_2178 = (let _152_2177 = (let _152_2176 = (let _152_2175 = (FStar_All.pipe_left (fun _152_2174 -> Some (_152_2174)) (Prims.strcat "Encoding " xxsym))
in (t, _152_2175))
in FStar_SMTEncoding_Term.Assume (_152_2176))
in (_152_2177)::[])
in (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') _152_2178))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_73_2865, t)) -> begin
(
# 1766 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1767 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (
# 1769 "FStar.SMTEncoding.Encode.fst"
let _73_2874 = (encode_free_var env fv t t_norm [])
in (match (_73_2874) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1774 "FStar.SMTEncoding.Encode.fst"
let _73_2888 = (encode_sigelt env se)
in (match (_73_2888) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1777 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1780 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _73_2895 -> (match (_73_2895) with
| (l, _73_2892, _73_2894) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1781 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _73_2902 -> (match (_73_2902) with
| (l, _73_2899, _73_2901) -> begin
(let _152_2186 = (FStar_All.pipe_left (fun _152_2182 -> FStar_SMTEncoding_Term.Echo (_152_2182)) (Prims.fst l))
in (let _152_2185 = (let _152_2184 = (let _152_2183 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_152_2183))
in (_152_2184)::[])
in (_152_2186)::_152_2185))
end))))
in (prefix, suffix))))

# 1782 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1785 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _152_2191 = (let _152_2190 = (let _152_2189 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _152_2189; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_152_2190)::[])
in (FStar_ST.op_Colon_Equals last_env _152_2191)))

# 1788 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_73_2908 -> begin
(
# 1791 "FStar.SMTEncoding.Encode.fst"
let _73_2911 = e
in {bindings = _73_2911.bindings; depth = _73_2911.depth; tcenv = tcenv; warn = _73_2911.warn; cache = _73_2911.cache; nolabels = _73_2911.nolabels; use_zfuel_name = _73_2911.use_zfuel_name; encode_non_total_function_typ = _73_2911.encode_non_total_function_typ})
end))

# 1791 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _73_2917::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1794 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _73_2919 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1798 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1799 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1799 "FStar.SMTEncoding.Encode.fst"
let _73_2925 = hd
in {bindings = _73_2925.bindings; depth = _73_2925.depth; tcenv = _73_2925.tcenv; warn = _73_2925.warn; cache = refs; nolabels = _73_2925.nolabels; use_zfuel_name = _73_2925.use_zfuel_name; encode_non_total_function_typ = _73_2925.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1800 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _73_2928 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _73_2932::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1803 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _73_2934 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1804 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _73_2935 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1805 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _73_2936 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_73_2939::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _73_2944 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1809 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1813 "FStar.SMTEncoding.Encode.fst"
let _73_2946 = (init_env tcenv)
in (
# 1814 "FStar.SMTEncoding.Encode.fst"
let _73_2948 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1815 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1817 "FStar.SMTEncoding.Encode.fst"
let _73_2951 = (push_env ())
in (
# 1818 "FStar.SMTEncoding.Encode.fst"
let _73_2953 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1819 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1821 "FStar.SMTEncoding.Encode.fst"
let _73_2956 = (let _152_2212 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _152_2212))
in (
# 1822 "FStar.SMTEncoding.Encode.fst"
let _73_2958 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1823 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1825 "FStar.SMTEncoding.Encode.fst"
let _73_2961 = (mark_env ())
in (
# 1826 "FStar.SMTEncoding.Encode.fst"
let _73_2963 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1827 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1829 "FStar.SMTEncoding.Encode.fst"
let _73_2966 = (reset_mark_env ())
in (
# 1830 "FStar.SMTEncoding.Encode.fst"
let _73_2968 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1831 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1833 "FStar.SMTEncoding.Encode.fst"
let _73_2971 = (commit_mark_env ())
in (
# 1834 "FStar.SMTEncoding.Encode.fst"
let _73_2973 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1835 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1837 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _152_2228 = (let _152_2227 = (let _152_2226 = (let _152_2225 = (let _152_2224 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _152_2224 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _152_2225 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _152_2226))
in FStar_SMTEncoding_Term.Caption (_152_2227))
in (_152_2228)::decls)
end else begin
decls
end)
in (
# 1841 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1842 "FStar.SMTEncoding.Encode.fst"
let _73_2982 = (encode_sigelt env se)
in (match (_73_2982) with
| (decls, env) -> begin
(
# 1843 "FStar.SMTEncoding.Encode.fst"
let _73_2983 = (set_env env)
in (let _152_2229 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _152_2229)))
end)))))

# 1844 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1847 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1848 "FStar.SMTEncoding.Encode.fst"
let _73_2988 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _152_2234 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _152_2234))
end else begin
()
end
in (
# 1850 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1851 "FStar.SMTEncoding.Encode.fst"
let _73_2995 = (encode_signature (
# 1851 "FStar.SMTEncoding.Encode.fst"
let _73_2991 = env
in {bindings = _73_2991.bindings; depth = _73_2991.depth; tcenv = _73_2991.tcenv; warn = false; cache = _73_2991.cache; nolabels = _73_2991.nolabels; use_zfuel_name = _73_2991.use_zfuel_name; encode_non_total_function_typ = _73_2991.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_73_2995) with
| (decls, env) -> begin
(
# 1852 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1854 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1857 "FStar.SMTEncoding.Encode.fst"
let _73_3001 = (set_env (
# 1857 "FStar.SMTEncoding.Encode.fst"
let _73_2999 = env
in {bindings = _73_2999.bindings; depth = _73_2999.depth; tcenv = _73_2999.tcenv; warn = true; cache = _73_2999.cache; nolabels = _73_2999.nolabels; use_zfuel_name = _73_2999.use_zfuel_name; encode_non_total_function_typ = _73_2999.encode_non_total_function_typ}))
in (
# 1858 "FStar.SMTEncoding.Encode.fst"
let _73_3003 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1859 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1860 "FStar.SMTEncoding.Encode.fst"
let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (
# 1863 "FStar.SMTEncoding.Encode.fst"
let _73_3009 = (let _152_2253 = (let _152_2252 = (let _152_2251 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _152_2251))
in (FStar_Util.format1 "Starting query at %s" _152_2252))
in (push _152_2253))
in (
# 1864 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _73_3012 -> (match (()) with
| () -> begin
(let _152_2258 = (let _152_2257 = (let _152_2256 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _152_2256))
in (FStar_Util.format1 "Ending query at %s" _152_2257))
in (pop _152_2258))
end))
in (
# 1865 "FStar.SMTEncoding.Encode.fst"
let _73_3066 = (
# 1866 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1867 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1868 "FStar.SMTEncoding.Encode.fst"
let _73_3036 = (
# 1869 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1871 "FStar.SMTEncoding.Encode.fst"
let _73_3025 = (aux rest)
in (match (_73_3025) with
| (out, rest) -> begin
(
# 1872 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _152_2264 = (let _152_2263 = (FStar_Syntax_Syntax.mk_binder (
# 1873 "FStar.SMTEncoding.Encode.fst"
let _73_3027 = x
in {FStar_Syntax_Syntax.ppname = _73_3027.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _73_3027.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_152_2263)::out)
in (_152_2264, rest)))
end))
end
| _73_3030 -> begin
([], bindings)
end))
in (
# 1875 "FStar.SMTEncoding.Encode.fst"
let _73_3033 = (aux bindings)
in (match (_73_3033) with
| (closing, bindings) -> begin
(let _152_2265 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_152_2265, bindings))
end)))
in (match (_73_3036) with
| (q, bindings) -> begin
(
# 1877 "FStar.SMTEncoding.Encode.fst"
let _73_3045 = (let _152_2267 = (FStar_List.filter (fun _73_21 -> (match (_73_21) with
| FStar_TypeChecker_Env.Binding_sig (_73_3039) -> begin
false
end
| _73_3042 -> begin
true
end)) bindings)
in (encode_env_bindings env _152_2267))
in (match (_73_3045) with
| (env_decls, env) -> begin
(
# 1878 "FStar.SMTEncoding.Encode.fst"
let _73_3046 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _152_2268 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _152_2268))
end else begin
()
end
in (
# 1881 "FStar.SMTEncoding.Encode.fst"
let _73_3050 = (encode_formula q env)
in (match (_73_3050) with
| (phi, qdecls) -> begin
(
# 1882 "FStar.SMTEncoding.Encode.fst"
let _73_3055 = (let _152_2269 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _152_2269 phi))
in (match (_73_3055) with
| (phi, labels, _73_3054) -> begin
(
# 1883 "FStar.SMTEncoding.Encode.fst"
let _73_3058 = (encode_labels labels)
in (match (_73_3058) with
| (label_prefix, label_suffix) -> begin
(
# 1884 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1888 "FStar.SMTEncoding.Encode.fst"
let qry = (let _152_2271 = (let _152_2270 = (FStar_SMTEncoding_Term.mkNot phi)
in (_152_2270, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_152_2271))
in (
# 1889 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_73_3066) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _73_3073); FStar_SMTEncoding_Term.hash = _73_3070; FStar_SMTEncoding_Term.freevars = _73_3068}, _73_3078) -> begin
(
# 1892 "FStar.SMTEncoding.Encode.fst"
let _73_3081 = (pop ())
in ())
end
| _73_3084 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1893 "FStar.SMTEncoding.Encode.fst"
let _73_3085 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _73_3089) -> begin
(
# 1895 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1896 "FStar.SMTEncoding.Encode.fst"
let _73_3093 = (FStar_SMTEncoding_ErrorReporting.askZ3_and_report_errors tcenv fresh labels prefix qry suffix)
in (pop ())))
end
| _73_3096 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1900 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1903 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1904 "FStar.SMTEncoding.Encode.fst"
let _73_3100 = (push "query")
in (
# 1905 "FStar.SMTEncoding.Encode.fst"
let _73_3105 = (encode_formula q env)
in (match (_73_3105) with
| (f, _73_3104) -> begin
(
# 1906 "FStar.SMTEncoding.Encode.fst"
let _73_3106 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _73_3110) -> begin
true
end
| _73_3114 -> begin
false
end))
end)))))

# 1909 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1924 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _73_3115 -> ()); FStar_TypeChecker_Env.push = (fun _73_3117 -> ()); FStar_TypeChecker_Env.pop = (fun _73_3119 -> ()); FStar_TypeChecker_Env.mark = (fun _73_3121 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _73_3123 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _73_3125 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _73_3127 _73_3129 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _73_3131 _73_3133 -> ()); FStar_TypeChecker_Env.solve = (fun _73_3135 _73_3137 _73_3139 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _73_3141 _73_3143 -> false); FStar_TypeChecker_Env.finish = (fun _73_3145 -> ()); FStar_TypeChecker_Env.refresh = (fun _73_3146 -> ())}





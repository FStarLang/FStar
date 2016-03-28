
open Prims
# 32 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 34 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _79_27 -> (match (_79_27) with
| (a, b) -> begin
(a, b, c)
end))

# 35 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _79_1 -> (match (_79_1) with
| (FStar_Util.Inl (_79_31), _79_34) -> begin
false
end
| _79_37 -> begin
true
end)) args))

# 36 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _164_13 = (let _164_12 = (let _164_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _164_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _164_12))
in Some (_164_13))
end))

# 39 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 42 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _79_46 = a
in (let _164_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _164_20; FStar_Syntax_Syntax.index = _79_46.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _79_46.FStar_Syntax_Syntax.sort}))
in (let _164_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _164_21))))

# 45 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _79_53 -> (match (()) with
| () -> begin
(let _164_31 = (let _164_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _164_30 lid.FStar_Ident.str))
in (FStar_All.failwith _164_31))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _79_57 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_79_57) with
| (_79_55, t) -> begin
(match ((let _164_32 = (FStar_Syntax_Subst.compress t)
in _164_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _79_65 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_79_65) with
| (binders, _79_64) -> begin
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
| _79_68 -> begin
(fail ())
end)
end))))

# 56 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _164_38 = (let _164_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _164_37))
in (FStar_All.pipe_left escape _164_38)))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _164_44 = (let _164_43 = (mk_term_projector_name lid a)
in (_164_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _164_44)))

# 59 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _164_50 = (let _164_49 = (mk_term_projector_name_by_pos lid i)
in (_164_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _164_50)))

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
let new_scope = (fun _79_92 -> (match (()) with
| () -> begin
(let _164_154 = (FStar_Util.smap_create 100)
in (let _164_153 = (FStar_Util.smap_create 100)
in (_164_154, _164_153)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _164_156 = (let _164_155 = (new_scope ())
in (_164_155)::[])
in (FStar_Util.mk_ref _164_156))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _164_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _164_160 (fun _79_100 -> (match (_79_100) with
| (names, _79_99) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_79_103) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _79_105 = (FStar_Util.incr ctr)
in (let _164_162 = (let _164_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _164_161))
in (Prims.strcat (Prims.strcat y "__") _164_162)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _164_164 = (let _164_163 = (FStar_ST.read scopes)
in (FStar_List.hd _164_163))
in (FStar_All.pipe_left Prims.fst _164_164))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _79_109 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _164_171 = (let _164_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _164_169 "__"))
in (let _164_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _164_171 _164_170))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _79_117 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _79_118 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _164_179 = (let _164_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _164_178))
in (FStar_Util.format2 "%s_%s" pfx _164_179)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _164_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _164_183 (fun _79_127 -> (match (_79_127) with
| (_79_125, strings) -> begin
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
let f = (let _164_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _164_184))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _164_186 = (let _164_185 = (FStar_ST.read scopes)
in (FStar_List.hd _164_185))
in (FStar_All.pipe_left Prims.snd _164_186))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _79_134 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _79_137 -> (match (()) with
| () -> begin
(let _164_191 = (let _164_190 = (new_scope ())
in (let _164_189 = (FStar_ST.read scopes)
in (_164_190)::_164_189))
in (FStar_ST.op_Colon_Equals scopes _164_191))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _79_139 -> (match (()) with
| () -> begin
(let _164_195 = (let _164_194 = (FStar_ST.read scopes)
in (FStar_List.tl _164_194))
in (FStar_ST.op_Colon_Equals scopes _164_195))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _79_141 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _79_143 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _79_145 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _79_158 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _79_163 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _79_166 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 120 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _79_168 = x
in (let _164_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _164_210; FStar_Syntax_Syntax.index = _79_168.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _79_168.FStar_Syntax_Syntax.sort})))

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
| Binding_var (_79_172) -> begin
_79_172
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_79_175) -> begin
_79_175
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 131 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 141 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _164_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _79_2 -> (match (_79_2) with
| Binding_var (x, _79_190) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _79_195, _79_197, _79_199) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _164_268 (FStar_String.concat ", "))))

# 145 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 147 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _164_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_164_278))
end else begin
None
end)

# 152 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _164_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _164_283))))

# 154 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _164_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _164_288))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _79_213 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _79_213.tcenv; warn = _79_213.warn; cache = _79_213.cache; nolabels = _79_213.nolabels; use_zfuel_name = _79_213.use_zfuel_name; encode_non_total_function_typ = _79_213.encode_non_total_function_typ})))))

# 161 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _79_219 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _79_219.depth; tcenv = _79_219.tcenv; warn = _79_219.warn; cache = _79_219.cache; nolabels = _79_219.nolabels; use_zfuel_name = _79_219.use_zfuel_name; encode_non_total_function_typ = _79_219.encode_non_total_function_typ})))))

# 165 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _79_224 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _79_224.depth; tcenv = _79_224.tcenv; warn = _79_224.warn; cache = _79_224.cache; nolabels = _79_224.nolabels; use_zfuel_name = _79_224.use_zfuel_name; encode_non_total_function_typ = _79_224.encode_non_total_function_typ}))

# 167 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _79_3 -> (match (_79_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _79_234 -> begin
None
end)))) with
| None -> begin
(let _164_305 = (let _164_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _164_304))
in (FStar_All.failwith _164_305))
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
in (let _164_316 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _79_244 = env
in (let _164_315 = (let _164_314 = (let _164_313 = (let _164_312 = (let _164_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _164_310 -> Some (_164_310)) _164_311))
in (x, fname, _164_312, None))
in Binding_fvar (_164_313))
in (_164_314)::env.bindings)
in {bindings = _164_315; depth = _79_244.depth; tcenv = _79_244.tcenv; warn = _79_244.warn; cache = _79_244.cache; nolabels = _79_244.nolabels; use_zfuel_name = _79_244.use_zfuel_name; encode_non_total_function_typ = _79_244.encode_non_total_function_typ}))
in (fname, ftok, _164_316)))))

# 178 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _79_4 -> (match (_79_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _79_256 -> begin
None
end))))

# 180 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _164_327 = (let _164_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _164_326))
in (FStar_All.failwith _164_327))
end
| Some (s) -> begin
s
end))

# 184 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _79_266 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _79_266.depth; tcenv = _79_266.tcenv; warn = _79_266.warn; cache = _79_266.cache; nolabels = _79_266.nolabels; use_zfuel_name = _79_266.use_zfuel_name; encode_non_total_function_typ = _79_266.encode_non_total_function_typ}))

# 186 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _79_275 = (lookup_lid env x)
in (match (_79_275) with
| (t1, t2, _79_274) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _164_344 = (let _164_343 = (let _164_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_164_342)::[])
in (f, _164_343))
in (FStar_SMTEncoding_Term.mkApp _164_344))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _79_277 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _79_277.depth; tcenv = _79_277.tcenv; warn = _79_277.warn; cache = _79_277.cache; nolabels = _79_277.nolabels; use_zfuel_name = _79_277.use_zfuel_name; encode_non_total_function_typ = _79_277.encode_non_total_function_typ}))
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
| _79_290 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_79_294, fuel::[]) -> begin
if (let _164_350 = (let _164_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _164_349 Prims.fst))
in (FStar_Util.starts_with _164_350 "fuel")) then begin
(let _164_353 = (let _164_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _164_352 fuel))
in (FStar_All.pipe_left (fun _164_351 -> Some (_164_351)) _164_353))
end else begin
Some (t)
end
end
| _79_300 -> begin
Some (t)
end)
end
| _79_302 -> begin
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
(let _164_357 = (let _164_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _164_356))
in (FStar_All.failwith _164_357))
end))

# 211 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _79_315 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_79_315) with
| (x, _79_312, _79_314) -> begin
x
end)))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _79_321 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_79_321) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _79_325; FStar_SMTEncoding_Term.freevars = _79_323}) when env.use_zfuel_name -> begin
(g, zf)
end
| _79_333 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _79_343 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 223 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _79_5 -> (match (_79_5) with
| Binding_fvar (_79_348, nm', tok, _79_352) when (nm = nm') -> begin
tok
end
| _79_356 -> begin
None
end))))

# 228 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _79_361 -> (match (_79_361) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _79_363 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _79_366 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_79_366) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _79_376 -> begin
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
(let _164_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _164_374))
end
| _79_389 -> begin
(let _164_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _164_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _79_392 -> begin
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
(let _164_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _164_381 FStar_Option.isNone))
end
| _79_431 -> begin
false
end)))

# 267 "FStar.SMTEncoding.Encode.fst"
let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _164_386 = (FStar_Syntax_Util.un_uinst t)
in _164_386.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_79_435) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _164_387 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _164_387 FStar_Option.isSome))
end
| _79_440 -> begin
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
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _164_400 = (let _164_398 = (FStar_Syntax_Syntax.null_binder t)
in (_164_398)::[])
in (let _164_399 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _164_400 _164_399 None))))

# 282 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _164_407 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _164_407))
end
| s -> begin
(
# 287 "FStar.SMTEncoding.Encode.fst"
let _79_452 = ()
in (let _164_408 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _164_408)))
end)) e)))

# 287 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 288 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _79_6 -> (match (_79_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _79_462 -> begin
false
end))

# 293 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 296 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _79_473; FStar_SMTEncoding_Term.freevars = _79_471}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _79_491) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _79_498 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_79_500, []) -> begin
(
# 307 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _79_506 -> begin
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
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _79_7 -> (match (_79_7) with
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
(let _164_462 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _164_462))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _164_463 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _164_463))
end
| FStar_Const.Const_int (i) -> begin
(let _164_464 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _164_464))
end
| FStar_Const.Const_int32 (i) -> begin
(let _164_468 = (let _164_467 = (let _164_466 = (let _164_465 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _164_465))
in (_164_466)::[])
in ("FStar.Int32.Int32", _164_467))
in (FStar_SMTEncoding_Term.mkApp _164_468))
end
| FStar_Const.Const_string (bytes, _79_528) -> begin
(let _164_469 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _164_469))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _164_471 = (let _164_470 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _164_470))
in (FStar_All.failwith _164_471))
end))

# 359 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 362 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 363 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_79_542) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_79_545) -> begin
(let _164_480 = (FStar_Syntax_Util.unrefine t)
in (aux true _164_480))
end
| _79_548 -> begin
if norm then begin
(let _164_481 = (whnf env t)
in (aux false _164_481))
end else begin
(let _164_484 = (let _164_483 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _164_482 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _164_483 _164_482)))
in (FStar_All.failwith _164_484))
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
| _79_556 -> begin
(let _164_487 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _164_487))
end)))

# 376 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 386 "FStar.SMTEncoding.Encode.fst"
let _79_560 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _164_535 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _164_535))
end else begin
()
end
in (
# 388 "FStar.SMTEncoding.Encode.fst"
let _79_588 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _79_567 b -> (match (_79_567) with
| (vars, guards, env, decls, names) -> begin
(
# 389 "FStar.SMTEncoding.Encode.fst"
let _79_582 = (
# 390 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 391 "FStar.SMTEncoding.Encode.fst"
let _79_573 = (gen_term_var env x)
in (match (_79_573) with
| (xxsym, xx, env') -> begin
(
# 392 "FStar.SMTEncoding.Encode.fst"
let _79_576 = (let _164_538 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _164_538 env xx))
in (match (_79_576) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_79_582) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_79_588) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 407 "FStar.SMTEncoding.Encode.fst"
let _79_595 = (encode_term t env)
in (match (_79_595) with
| (t, decls) -> begin
(let _164_543 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_164_543, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 411 "FStar.SMTEncoding.Encode.fst"
let _79_602 = (encode_term t env)
in (match (_79_602) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _164_548 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_164_548, decls))
end
| Some (f) -> begin
(let _164_549 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_164_549, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 419 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 420 "FStar.SMTEncoding.Encode.fst"
let _79_609 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _164_554 = (FStar_Syntax_Print.tag_of_term t)
in (let _164_553 = (FStar_Syntax_Print.tag_of_term t0)
in (let _164_552 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _164_554 _164_553 _164_552))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _164_559 = (let _164_558 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _164_557 = (FStar_Syntax_Print.tag_of_term t0)
in (let _164_556 = (FStar_Syntax_Print.term_to_string t0)
in (let _164_555 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _164_558 _164_557 _164_556 _164_555)))))
in (FStar_All.failwith _164_559))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _164_561 = (let _164_560 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _164_560))
in (FStar_All.failwith _164_561))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _79_620) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _79_625) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 436 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _164_562 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_164_562, []))
end
| FStar_Syntax_Syntax.Tm_type (_79_634) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _79_638) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _164_563 = (encode_const c)
in (_164_563, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 452 "FStar.SMTEncoding.Encode.fst"
let _79_649 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_79_649) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 456 "FStar.SMTEncoding.Encode.fst"
let _79_656 = (encode_binders None binders env)
in (match (_79_656) with
| (vars, guards, env', decls, _79_655) -> begin
(
# 457 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _164_564 = (varops.fresh "f")
in (_164_564, FStar_SMTEncoding_Term.Term_sort))
in (
# 458 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 459 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 460 "FStar.SMTEncoding.Encode.fst"
let _79_662 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_79_662) with
| (pre_opt, res_t) -> begin
(
# 461 "FStar.SMTEncoding.Encode.fst"
let _79_665 = (encode_term_pred None res_t env' app)
in (match (_79_665) with
| (res_pred, decls') -> begin
(
# 462 "FStar.SMTEncoding.Encode.fst"
let _79_674 = (match (pre_opt) with
| None -> begin
(let _164_565 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_164_565, decls))
end
| Some (pre) -> begin
(
# 465 "FStar.SMTEncoding.Encode.fst"
let _79_671 = (encode_formula pre env')
in (match (_79_671) with
| (guard, decls0) -> begin
(let _164_566 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_164_566, (FStar_List.append decls decls0)))
end))
end)
in (match (_79_674) with
| (guards, guard_decls) -> begin
(
# 467 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _164_568 = (let _164_567 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _164_567))
in (FStar_SMTEncoding_Term.mkForall _164_568))
in (
# 472 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _164_570 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _164_570 (FStar_List.filter (fun _79_679 -> (match (_79_679) with
| (x, _79_678) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 473 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _79_685) -> begin
(let _164_573 = (let _164_572 = (let _164_571 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _164_571))
in (FStar_SMTEncoding_Term.mkApp _164_572))
in (_164_573, []))
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
(let _164_574 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_164_574))
end else begin
None
end
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let t = (let _164_576 = (let _164_575 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _164_575))
in (FStar_SMTEncoding_Term.mkApp _164_576))
in (
# 489 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 491 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _164_578 = (let _164_577 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_164_577, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_164_578))
in (
# 493 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 495 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _164_585 = (let _164_584 = (let _164_583 = (let _164_582 = (let _164_581 = (let _164_580 = (let _164_579 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _164_579))
in (f_has_t, _164_580))
in (FStar_SMTEncoding_Term.mkImp _164_581))
in (((f_has_t)::[])::[], (fsym)::cvars, _164_582))
in (mkForall_fuel _164_583))
in (_164_584, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_164_585))
in (
# 496 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _164_589 = (let _164_588 = (let _164_587 = (let _164_586 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _164_586))
in (FStar_SMTEncoding_Term.mkForall _164_587))
in (_164_588, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_164_589))
in (
# 499 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 500 "FStar.SMTEncoding.Encode.fst"
let _79_701 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
let t_kinding = (let _164_591 = (let _164_590 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_164_590, Some ("Typing for non-total arrows")))
in FStar_SMTEncoding_Term.Assume (_164_591))
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
let t_interp = (let _164_598 = (let _164_597 = (let _164_596 = (let _164_595 = (let _164_594 = (let _164_593 = (let _164_592 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _164_592))
in (f_has_t, _164_593))
in (FStar_SMTEncoding_Term.mkImp _164_594))
in (((f_has_t)::[])::[], (fsym)::[], _164_595))
in (mkForall_fuel _164_596))
in (_164_597, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_164_598))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_79_712) -> begin
(
# 518 "FStar.SMTEncoding.Encode.fst"
let _79_732 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _79_719; FStar_Syntax_Syntax.pos = _79_717; FStar_Syntax_Syntax.vars = _79_715} -> begin
(
# 520 "FStar.SMTEncoding.Encode.fst"
let _79_727 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_79_727) with
| (b, f) -> begin
(let _164_600 = (let _164_599 = (FStar_List.hd b)
in (Prims.fst _164_599))
in (_164_600, f))
end))
end
| _79_729 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_79_732) with
| (x, f) -> begin
(
# 524 "FStar.SMTEncoding.Encode.fst"
let _79_735 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_79_735) with
| (base_t, decls) -> begin
(
# 525 "FStar.SMTEncoding.Encode.fst"
let _79_739 = (gen_term_var env x)
in (match (_79_739) with
| (x, xtm, env') -> begin
(
# 526 "FStar.SMTEncoding.Encode.fst"
let _79_742 = (encode_formula f env')
in (match (_79_742) with
| (refinement, decls') -> begin
(
# 528 "FStar.SMTEncoding.Encode.fst"
let _79_745 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_79_745) with
| (fsym, fterm) -> begin
(
# 530 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _164_602 = (let _164_601 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_164_601, refinement))
in (FStar_SMTEncoding_Term.mkAnd _164_602))
in (
# 532 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _164_604 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _164_604 (FStar_List.filter (fun _79_750 -> (match (_79_750) with
| (y, _79_749) -> begin
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
| Some (t, _79_757, _79_759) -> begin
(let _164_607 = (let _164_606 = (let _164_605 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _164_605))
in (FStar_SMTEncoding_Term.mkApp _164_606))
in (_164_607, []))
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
let t = (let _164_609 = (let _164_608 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _164_608))
in (FStar_SMTEncoding_Term.mkApp _164_609))
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
let assumption = (let _164_611 = (let _164_610 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _164_610))
in (FStar_SMTEncoding_Term.mkForall _164_611))
in (
# 553 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _164_618 = (let _164_617 = (let _164_616 = (let _164_615 = (let _164_614 = (let _164_613 = (let _164_612 = (FStar_Syntax_Print.term_to_string t0)
in Some (_164_612))
in (assumption, _164_613))
in FStar_SMTEncoding_Term.Assume (_164_614))
in (_164_615)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, Some ("refinement kinding"))))::_164_616)
in (tdecl)::_164_617)
in (FStar_List.append (FStar_List.append decls decls') _164_618))
in (
# 558 "FStar.SMTEncoding.Encode.fst"
let _79_772 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
let ttm = (let _164_619 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _164_619))
in (
# 564 "FStar.SMTEncoding.Encode.fst"
let _79_781 = (encode_term_pred None k env ttm)
in (match (_79_781) with
| (t_has_k, decls) -> begin
(
# 565 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, Some ("Uvar typing")))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_79_784) -> begin
(
# 569 "FStar.SMTEncoding.Encode.fst"
let _79_788 = (FStar_Syntax_Util.head_and_args t0)
in (match (_79_788) with
| (head, args_e) -> begin
(match ((let _164_621 = (let _164_620 = (FStar_Syntax_Subst.compress head)
in _164_620.FStar_Syntax_Syntax.n)
in (_164_621, args_e))) with
| (_79_790, _79_792) when (head_redex env head) -> begin
(let _164_622 = (whnf env t)
in (encode_term _164_622 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), _::(v1, _)::(v2, _)::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let _79_832 = (encode_term v1 env)
in (match (_79_832) with
| (v1, decls1) -> begin
(
# 577 "FStar.SMTEncoding.Encode.fst"
let _79_835 = (encode_term v2 env)
in (match (_79_835) with
| (v2, decls2) -> begin
(let _164_623 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_164_623, (FStar_List.append decls1 decls2)))
end))
end))
end
| _79_837 -> begin
(
# 581 "FStar.SMTEncoding.Encode.fst"
let _79_840 = (encode_args args_e env)
in (match (_79_840) with
| (args, decls) -> begin
(
# 583 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 584 "FStar.SMTEncoding.Encode.fst"
let _79_845 = (encode_term head env)
in (match (_79_845) with
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
let _79_854 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_79_854) with
| (formals, rest) -> begin
(
# 590 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _79_858 _79_862 -> (match ((_79_858, _79_862)) with
| ((bv, _79_857), (a, _79_861)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 591 "FStar.SMTEncoding.Encode.fst"
let ty = (let _164_628 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _164_628 (FStar_Syntax_Subst.subst subst)))
in (
# 592 "FStar.SMTEncoding.Encode.fst"
let _79_867 = (encode_term_pred None ty env app_tm)
in (match (_79_867) with
| (has_type, decls'') -> begin
(
# 593 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 594 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _164_630 = (let _164_629 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_164_629, Some ("Partial app typing")))
in FStar_SMTEncoding_Term.Assume (_164_630))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 598 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 599 "FStar.SMTEncoding.Encode.fst"
let _79_874 = (lookup_free_var_sym env fv)
in (match (_79_874) with
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
(let _164_634 = (let _164_633 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _164_633 Prims.snd))
in Some (_164_634))
end
| FStar_Syntax_Syntax.Tm_ascribed (_79_906, t, _79_909) -> begin
Some (t)
end
| _79_913 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 616 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _164_635 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _164_635))
in (
# 617 "FStar.SMTEncoding.Encode.fst"
let _79_921 = (curried_arrow_formals_comp head_type)
in (match (_79_921) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _79_937 -> begin
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
let _79_946 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_79_946) with
| (bs, body, opening) -> begin
(
# 632 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _79_948 -> (match (()) with
| () -> begin
(
# 633 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 634 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, Some ("Imprecise function encoding")))
in (let _164_638 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_164_638, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 639 "FStar.SMTEncoding.Encode.fst"
let _79_952 = (let _164_640 = (let _164_639 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _164_639))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _164_640))
in (fallback ()))
end
| Some (lc) -> begin
if (let _164_641 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _164_641)) then begin
(fallback ())
end else begin
(
# 645 "FStar.SMTEncoding.Encode.fst"
let c0 = (lc.FStar_Syntax_Syntax.comp ())
in (
# 646 "FStar.SMTEncoding.Encode.fst"
let c = (FStar_Syntax_Subst.subst_comp opening c0)
in (
# 649 "FStar.SMTEncoding.Encode.fst"
let _79_964 = (encode_binders None bs env)
in (match (_79_964) with
| (vars, guards, envbody, decls, _79_963) -> begin
(
# 650 "FStar.SMTEncoding.Encode.fst"
let _79_967 = (encode_term body envbody)
in (match (_79_967) with
| (body, decls') -> begin
(
# 651 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _164_645 = (let _164_644 = (let _164_643 = (let _164_642 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_164_642, body))
in (FStar_SMTEncoding_Term.mkImp _164_643))
in ([], vars, _164_644))
in (FStar_SMTEncoding_Term.mkForall _164_645))
in (
# 652 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 653 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _79_973, _79_975) -> begin
(let _164_648 = (let _164_647 = (let _164_646 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _164_646))
in (FStar_SMTEncoding_Term.mkApp _164_647))
in (_164_648, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(
# 662 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 663 "FStar.SMTEncoding.Encode.fst"
let fsym = (varops.fresh "Exp_abs")
in (
# 664 "FStar.SMTEncoding.Encode.fst"
let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 665 "FStar.SMTEncoding.Encode.fst"
let f = (let _164_650 = (let _164_649 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _164_649))
in (FStar_SMTEncoding_Term.mkApp _164_650))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 667 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let _79_990 = (encode_term_pred None tfun env f)
in (match (_79_990) with
| (f_has_t, decls'') -> begin
(
# 669 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _164_652 = (let _164_651 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_164_651, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_164_652))
in (
# 671 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _164_659 = (let _164_658 = (let _164_657 = (let _164_656 = (let _164_655 = (let _164_654 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _164_653 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_164_654, _164_653)))
in (FStar_SMTEncoding_Term.mkImp _164_655))
in (((app)::[])::[], (FStar_List.append vars cvars), _164_656))
in (FStar_SMTEncoding_Term.mkForall _164_657))
in (_164_658, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_164_659))
in (
# 673 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 674 "FStar.SMTEncoding.Encode.fst"
let _79_994 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_79_997, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_79_1009); FStar_Syntax_Syntax.lbunivs = _79_1007; FStar_Syntax_Syntax.lbtyp = _79_1005; FStar_Syntax_Syntax.lbeff = _79_1003; FStar_Syntax_Syntax.lbdef = _79_1001}::_79_999), _79_1015) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _79_1024; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _79_1021; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_79_1034) -> begin
(
# 687 "FStar.SMTEncoding.Encode.fst"
let _79_1036 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 688 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 689 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _164_660 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_164_660, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 696 "FStar.SMTEncoding.Encode.fst"
let _79_1052 = (encode_term e1 env)
in (match (_79_1052) with
| (ee1, decls1) -> begin
(
# 697 "FStar.SMTEncoding.Encode.fst"
let _79_1055 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_79_1055) with
| (xs, e2) -> begin
(
# 698 "FStar.SMTEncoding.Encode.fst"
let _79_1059 = (FStar_List.hd xs)
in (match (_79_1059) with
| (x, _79_1058) -> begin
(
# 699 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 700 "FStar.SMTEncoding.Encode.fst"
let _79_1063 = (encode_body e2 env')
in (match (_79_1063) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 704 "FStar.SMTEncoding.Encode.fst"
let _79_1071 = (encode_term e env)
in (match (_79_1071) with
| (scr, decls) -> begin
(
# 705 "FStar.SMTEncoding.Encode.fst"
let _79_1108 = (FStar_List.fold_right (fun b _79_1075 -> (match (_79_1075) with
| (else_case, decls) -> begin
(
# 706 "FStar.SMTEncoding.Encode.fst"
let _79_1079 = (FStar_Syntax_Subst.open_branch b)
in (match (_79_1079) with
| (p, w, br) -> begin
(
# 707 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _79_1083 _79_1086 -> (match ((_79_1083, _79_1086)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 709 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 710 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 711 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _79_1092 -> (match (_79_1092) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 712 "FStar.SMTEncoding.Encode.fst"
let _79_1102 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 715 "FStar.SMTEncoding.Encode.fst"
let _79_1099 = (encode_term w env)
in (match (_79_1099) with
| (w, decls2) -> begin
(let _164_694 = (let _164_693 = (let _164_692 = (let _164_691 = (let _164_690 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _164_690))
in (FStar_SMTEncoding_Term.mkEq _164_691))
in (guard, _164_692))
in (FStar_SMTEncoding_Term.mkAnd _164_693))
in (_164_694, decls2))
end))
end)
in (match (_79_1102) with
| (guard, decls2) -> begin
(
# 717 "FStar.SMTEncoding.Encode.fst"
let _79_1105 = (encode_br br env)
in (match (_79_1105) with
| (br, decls3) -> begin
(let _164_695 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_164_695, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_79_1108) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _79_1114 -> begin
(let _164_698 = (encode_one_pat env pat)
in (_164_698)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 731 "FStar.SMTEncoding.Encode.fst"
let _79_1117 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _164_701 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _164_701))
end else begin
()
end
in (
# 732 "FStar.SMTEncoding.Encode.fst"
let _79_1121 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_79_1121) with
| (vars, pat_term) -> begin
(
# 734 "FStar.SMTEncoding.Encode.fst"
let _79_1133 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _79_1124 v -> (match (_79_1124) with
| (env, vars) -> begin
(
# 735 "FStar.SMTEncoding.Encode.fst"
let _79_1130 = (gen_term_var env v)
in (match (_79_1130) with
| (xx, _79_1128, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_79_1133) with
| (env, vars) -> begin
(
# 738 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_79_1138) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _164_709 = (let _164_708 = (encode_const c)
in (scrutinee, _164_708))
in (FStar_SMTEncoding_Term.mkEq _164_709))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(
# 746 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (
# 747 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _79_1160 -> (match (_79_1160) with
| (arg, _79_1159) -> begin
(
# 748 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _164_712 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _164_712)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 752 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_79_1167) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_79_1177) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _164_720 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _79_1187 -> (match (_79_1187) with
| (arg, _79_1186) -> begin
(
# 764 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _164_719 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _164_719)))
end))))
in (FStar_All.pipe_right _164_720 FStar_List.flatten))
end))
in (
# 768 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _79_1190 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (
# 770 "FStar.SMTEncoding.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (
# 780 "FStar.SMTEncoding.Encode.fst"
let _79_1206 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _79_1196 _79_1200 -> (match ((_79_1196, _79_1200)) with
| ((tms, decls), (t, _79_1199)) -> begin
(
# 781 "FStar.SMTEncoding.Encode.fst"
let _79_1203 = (encode_term t env)
in (match (_79_1203) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_79_1206) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 787 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let _79_1215 = (let _164_733 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _164_733))
in (match (_79_1215) with
| (head, args) -> begin
(match ((let _164_735 = (let _164_734 = (FStar_Syntax_Util.un_uinst head)
in _164_734.FStar_Syntax_Syntax.n)
in (_164_735, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _79_1219) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _79_1232::(hd, _79_1229)::(tl, _79_1225)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _164_736 = (list_elements tl)
in (hd)::_164_736)
end
| _79_1236 -> begin
(
# 793 "FStar.SMTEncoding.Encode.fst"
let _79_1237 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 795 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 796 "FStar.SMTEncoding.Encode.fst"
let _79_1243 = (let _164_739 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _164_739 FStar_Syntax_Util.head_and_args))
in (match (_79_1243) with
| (head, args) -> begin
(match ((let _164_741 = (let _164_740 = (FStar_Syntax_Util.un_uinst head)
in _164_740.FStar_Syntax_Syntax.n)
in (_164_741, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_79_1251, _79_1253)::(e, _79_1248)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _79_1261)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _79_1266 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (
# 802 "FStar.SMTEncoding.Encode.fst"
let lemma_pats = (fun p -> (
# 803 "FStar.SMTEncoding.Encode.fst"
let elts = (list_elements p)
in (
# 804 "FStar.SMTEncoding.Encode.fst"
let smt_pat_or = (fun t -> (
# 805 "FStar.SMTEncoding.Encode.fst"
let _79_1274 = (let _164_746 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _164_746 FStar_Syntax_Util.head_and_args))
in (match (_79_1274) with
| (head, args) -> begin
(match ((let _164_748 = (let _164_747 = (FStar_Syntax_Util.un_uinst head)
in _164_747.FStar_Syntax_Syntax.n)
in (_164_748, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _79_1279)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _79_1284 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _164_751 = (list_elements e)
in (FStar_All.pipe_right _164_751 (FStar_List.map (fun branch -> (let _164_750 = (list_elements branch)
in (FStar_All.pipe_right _164_750 (FStar_List.map one_pat)))))))
end
| _79_1291 -> begin
(let _164_752 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_164_752)::[])
end)
end
| _79_1293 -> begin
(let _164_753 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_164_753)::[])
end))))
in (
# 819 "FStar.SMTEncoding.Encode.fst"
let _79_1327 = (match ((let _164_754 = (FStar_Syntax_Subst.compress t)
in _164_754.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 821 "FStar.SMTEncoding.Encode.fst"
let _79_1300 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_79_1300) with
| (binders, c) -> begin
(
# 822 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _79_1312)::(post, _79_1308)::(pats, _79_1304)::[] -> begin
(
# 825 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _164_755 = (lemma_pats pats')
in (binders, pre, post, _164_755)))
end
| _79_1320 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _79_1322 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_79_1327) with
| (binders, pre, post, patterns) -> begin
(
# 833 "FStar.SMTEncoding.Encode.fst"
let _79_1334 = (encode_binders None binders env)
in (match (_79_1334) with
| (vars, guards, env, decls, _79_1333) -> begin
(
# 836 "FStar.SMTEncoding.Encode.fst"
let _79_1347 = (let _164_759 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 837 "FStar.SMTEncoding.Encode.fst"
let _79_1344 = (let _164_758 = (FStar_All.pipe_right branch (FStar_List.map (fun _79_1339 -> (match (_79_1339) with
| (t, _79_1338) -> begin
(encode_term t (
# 837 "FStar.SMTEncoding.Encode.fst"
let _79_1340 = env
in {bindings = _79_1340.bindings; depth = _79_1340.depth; tcenv = _79_1340.tcenv; warn = _79_1340.warn; cache = _79_1340.cache; nolabels = _79_1340.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _79_1340.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _164_758 FStar_List.unzip))
in (match (_79_1344) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _164_759 FStar_List.unzip))
in (match (_79_1347) with
| (pats, decls') -> begin
(
# 840 "FStar.SMTEncoding.Encode.fst"
let decls' = (FStar_List.flatten decls')
in (
# 842 "FStar.SMTEncoding.Encode.fst"
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _164_762 = (let _164_761 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _164_761 e))
in (_164_762)::p))))
end
| _79_1357 -> begin
(
# 850 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _164_768 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_164_768)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _164_770 = (let _164_769 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _164_769 tl))
in (aux _164_770 vars))
end
| _79_1369 -> begin
pats
end))
in (let _164_771 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _164_771 vars)))
end)
end)
in (
# 857 "FStar.SMTEncoding.Encode.fst"
let env = (
# 857 "FStar.SMTEncoding.Encode.fst"
let _79_1371 = env
in {bindings = _79_1371.bindings; depth = _79_1371.depth; tcenv = _79_1371.tcenv; warn = _79_1371.warn; cache = _79_1371.cache; nolabels = true; use_zfuel_name = _79_1371.use_zfuel_name; encode_non_total_function_typ = _79_1371.encode_non_total_function_typ})
in (
# 858 "FStar.SMTEncoding.Encode.fst"
let _79_1376 = (let _164_772 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _164_772 env))
in (match (_79_1376) with
| (pre, decls'') -> begin
(
# 859 "FStar.SMTEncoding.Encode.fst"
let _79_1379 = (let _164_773 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _164_773 env))
in (match (_79_1379) with
| (post, decls''') -> begin
(
# 860 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _164_778 = (let _164_777 = (let _164_776 = (let _164_775 = (let _164_774 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_164_774, post))
in (FStar_SMTEncoding_Term.mkImp _164_775))
in (pats, vars, _164_776))
in (FStar_SMTEncoding_Term.mkForall _164_777))
in (_164_778, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 864 "FStar.SMTEncoding.Encode.fst"
let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _164_784 = (FStar_Syntax_Print.tag_of_term phi)
in (let _164_783 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _164_784 _164_783)))
end else begin
()
end)
in (
# 869 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 870 "FStar.SMTEncoding.Encode.fst"
let _79_1395 = (FStar_Util.fold_map (fun decls x -> (
# 870 "FStar.SMTEncoding.Encode.fst"
let _79_1392 = (encode_term (Prims.fst x) env)
in (match (_79_1392) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_79_1395) with
| (decls, args) -> begin
(let _164_800 = (f args)
in (_164_800, decls))
end)))
in (
# 873 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _79_1398 -> (f, []))
in (
# 874 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _164_814 = (FStar_List.hd l)
in (FStar_All.pipe_left f _164_814)))
in (
# 875 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _79_8 -> (match (_79_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _79_1409 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 879 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 880 "FStar.SMTEncoding.Encode.fst"
let _79_1426 = (FStar_List.fold_right (fun _79_1417 _79_1420 -> (match ((_79_1417, _79_1420)) with
| ((t, _79_1416), (phis, decls)) -> begin
(
# 882 "FStar.SMTEncoding.Encode.fst"
let _79_1423 = (encode_formula t env)
in (match (_79_1423) with
| (phi, decls') -> begin
((phi)::phis, (FStar_List.append decls' decls))
end))
end)) l ([], []))
in (match (_79_1426) with
| (phis, decls) -> begin
(let _164_839 = (f phis)
in (_164_839, decls))
end)))
in (
# 887 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _79_9 -> (match (_79_9) with
| _79_1433::_79_1431::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 891 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _79_10 -> (match (_79_10) with
| (lhs, _79_1444)::(rhs, _79_1440)::[] -> begin
(
# 893 "FStar.SMTEncoding.Encode.fst"
let _79_1449 = (encode_formula rhs env)
in (match (_79_1449) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _79_1452) -> begin
(l1, decls1)
end
| _79_1456 -> begin
(
# 897 "FStar.SMTEncoding.Encode.fst"
let _79_1459 = (encode_formula lhs env)
in (match (_79_1459) with
| (l2, decls2) -> begin
(let _164_844 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_164_844, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _79_1461 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 902 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _79_11 -> (match (_79_11) with
| (guard, _79_1474)::(_then, _79_1470)::(_else, _79_1466)::[] -> begin
(
# 904 "FStar.SMTEncoding.Encode.fst"
let _79_1479 = (encode_formula guard env)
in (match (_79_1479) with
| (g, decls1) -> begin
(
# 905 "FStar.SMTEncoding.Encode.fst"
let _79_1482 = (encode_formula _then env)
in (match (_79_1482) with
| (t, decls2) -> begin
(
# 906 "FStar.SMTEncoding.Encode.fst"
let _79_1485 = (encode_formula _else env)
in (match (_79_1485) with
| (e, decls3) -> begin
(
# 907 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _79_1488 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 912 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _164_856 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _164_856)))
in (
# 913 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _164_909 = (let _164_865 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _164_865))
in (let _164_908 = (let _164_907 = (let _164_871 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _164_871))
in (let _164_906 = (let _164_905 = (let _164_904 = (let _164_880 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _164_880))
in (let _164_903 = (let _164_902 = (let _164_901 = (let _164_889 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _164_889))
in (_164_901)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_164_902)
in (_164_904)::_164_903))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_164_905)
in (_164_907)::_164_906))
in (_164_909)::_164_908))
in (
# 925 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 927 "FStar.SMTEncoding.Encode.fst"
let _79_1506 = (encode_formula phi' env)
in (match (_79_1506) with
| (phi, decls) -> begin
(let _164_912 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_164_912, decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 931 "FStar.SMTEncoding.Encode.fst"
let _79_1513 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_79_1513) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _79_1520; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _79_1517; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 935 "FStar.SMTEncoding.Encode.fst"
let _79_1531 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_79_1531) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 939 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _79_1548::(x, _79_1545)::(t, _79_1541)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(
# 942 "FStar.SMTEncoding.Encode.fst"
let _79_1553 = (encode_term x env)
in (match (_79_1553) with
| (x, decls) -> begin
(
# 943 "FStar.SMTEncoding.Encode.fst"
let _79_1556 = (encode_term t env)
in (match (_79_1556) with
| (t, decls') -> begin
(let _164_913 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_164_913, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _79_1574::_79_1572::(r, _79_1569)::(msg, _79_1565)::(phi, _79_1561)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _164_917 = (let _164_914 = (FStar_Syntax_Subst.compress r)
in _164_914.FStar_Syntax_Syntax.n)
in (let _164_916 = (let _164_915 = (FStar_Syntax_Subst.compress msg)
in _164_915.FStar_Syntax_Syntax.n)
in (_164_917, _164_916)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _79_1582))) -> begin
(
# 949 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _79_1589 -> begin
(fallback phi)
end)
end
| _79_1591 when (head_redex env head) -> begin
(let _164_918 = (whnf env phi)
in (encode_formula _164_918 env))
end
| _79_1593 -> begin
(
# 959 "FStar.SMTEncoding.Encode.fst"
let _79_1596 = (encode_term phi env)
in (match (_79_1596) with
| (tt, decls) -> begin
(let _164_919 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_164_919, decls))
end))
end))
end
| _79_1598 -> begin
(
# 964 "FStar.SMTEncoding.Encode.fst"
let _79_1601 = (encode_term phi env)
in (match (_79_1601) with
| (tt, decls) -> begin
(let _164_920 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_164_920, decls))
end))
end))
in (
# 967 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 968 "FStar.SMTEncoding.Encode.fst"
let _79_1613 = (encode_binders None bs env)
in (match (_79_1613) with
| (vars, guards, env, decls, _79_1612) -> begin
(
# 969 "FStar.SMTEncoding.Encode.fst"
let _79_1626 = (let _164_932 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 970 "FStar.SMTEncoding.Encode.fst"
let _79_1623 = (let _164_931 = (FStar_All.pipe_right p (FStar_List.map (fun _79_1618 -> (match (_79_1618) with
| (t, _79_1617) -> begin
(encode_term t (
# 970 "FStar.SMTEncoding.Encode.fst"
let _79_1619 = env
in {bindings = _79_1619.bindings; depth = _79_1619.depth; tcenv = _79_1619.tcenv; warn = _79_1619.warn; cache = _79_1619.cache; nolabels = _79_1619.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _79_1619.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _164_931 FStar_List.unzip))
in (match (_79_1623) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _164_932 FStar_List.unzip))
in (match (_79_1626) with
| (pats, decls') -> begin
(
# 972 "FStar.SMTEncoding.Encode.fst"
let _79_1629 = (encode_formula body env)
in (match (_79_1629) with
| (body, decls'') -> begin
(let _164_933 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _164_933, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 975 "FStar.SMTEncoding.Encode.fst"
let _79_1630 = (debug phi)
in (
# 977 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _79_1642 -> (match (_79_1642) with
| (l, _79_1641) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_79_1645, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 987 "FStar.SMTEncoding.Encode.fst"
let _79_1655 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _164_950 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _164_950))
end else begin
()
end
in (
# 990 "FStar.SMTEncoding.Encode.fst"
let _79_1662 = (encode_q_body env vars pats body)
in (match (_79_1662) with
| (vars, pats, guard, body, decls) -> begin
(let _164_953 = (let _164_952 = (let _164_951 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _164_951))
in (FStar_SMTEncoding_Term.mkForall _164_952))
in (_164_953, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 994 "FStar.SMTEncoding.Encode.fst"
let _79_1674 = (encode_q_body env vars pats body)
in (match (_79_1674) with
| (vars, pats, guard, body, decls) -> begin
(let _164_956 = (let _164_955 = (let _164_954 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _164_954))
in (FStar_SMTEncoding_Term.mkExists _164_955))
in (_164_956, decls))
end))
end)))))))))))))))))

# 995 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 1003 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1006 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 1010 "FStar.SMTEncoding.Encode.fst"
let _79_1680 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_79_1680) with
| (asym, a) -> begin
(
# 1011 "FStar.SMTEncoding.Encode.fst"
let _79_1683 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_79_1683) with
| (xsym, x) -> begin
(
# 1012 "FStar.SMTEncoding.Encode.fst"
let _79_1686 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_79_1686) with
| (ysym, y) -> begin
(
# 1013 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 1014 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1015 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _164_999 = (let _164_998 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _164_998))
in (FStar_SMTEncoding_Term.mkApp _164_999))
in (
# 1016 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _164_1001 = (let _164_1000 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _164_1000, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_164_1001))
in (let _164_1007 = (let _164_1006 = (let _164_1005 = (let _164_1004 = (let _164_1003 = (let _164_1002 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _164_1002))
in (FStar_SMTEncoding_Term.mkForall _164_1003))
in (_164_1004, None))
in FStar_SMTEncoding_Term.Assume (_164_1005))
in (_164_1006)::[])
in (vname_decl)::_164_1007))))
in (
# 1019 "FStar.SMTEncoding.Encode.fst"
let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1020 "FStar.SMTEncoding.Encode.fst"
let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1021 "FStar.SMTEncoding.Encode.fst"
let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1022 "FStar.SMTEncoding.Encode.fst"
let prims = (let _164_1167 = (let _164_1016 = (let _164_1015 = (let _164_1014 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1014))
in (quant axy _164_1015))
in (FStar_Syntax_Const.op_Eq, _164_1016))
in (let _164_1166 = (let _164_1165 = (let _164_1023 = (let _164_1022 = (let _164_1021 = (let _164_1020 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _164_1020))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1021))
in (quant axy _164_1022))
in (FStar_Syntax_Const.op_notEq, _164_1023))
in (let _164_1164 = (let _164_1163 = (let _164_1032 = (let _164_1031 = (let _164_1030 = (let _164_1029 = (let _164_1028 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1027 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1028, _164_1027)))
in (FStar_SMTEncoding_Term.mkLT _164_1029))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1030))
in (quant xy _164_1031))
in (FStar_Syntax_Const.op_LT, _164_1032))
in (let _164_1162 = (let _164_1161 = (let _164_1041 = (let _164_1040 = (let _164_1039 = (let _164_1038 = (let _164_1037 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1036 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1037, _164_1036)))
in (FStar_SMTEncoding_Term.mkLTE _164_1038))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1039))
in (quant xy _164_1040))
in (FStar_Syntax_Const.op_LTE, _164_1041))
in (let _164_1160 = (let _164_1159 = (let _164_1050 = (let _164_1049 = (let _164_1048 = (let _164_1047 = (let _164_1046 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1045 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1046, _164_1045)))
in (FStar_SMTEncoding_Term.mkGT _164_1047))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1048))
in (quant xy _164_1049))
in (FStar_Syntax_Const.op_GT, _164_1050))
in (let _164_1158 = (let _164_1157 = (let _164_1059 = (let _164_1058 = (let _164_1057 = (let _164_1056 = (let _164_1055 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1054 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1055, _164_1054)))
in (FStar_SMTEncoding_Term.mkGTE _164_1056))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1057))
in (quant xy _164_1058))
in (FStar_Syntax_Const.op_GTE, _164_1059))
in (let _164_1156 = (let _164_1155 = (let _164_1068 = (let _164_1067 = (let _164_1066 = (let _164_1065 = (let _164_1064 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1063 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1064, _164_1063)))
in (FStar_SMTEncoding_Term.mkSub _164_1065))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _164_1066))
in (quant xy _164_1067))
in (FStar_Syntax_Const.op_Subtraction, _164_1068))
in (let _164_1154 = (let _164_1153 = (let _164_1075 = (let _164_1074 = (let _164_1073 = (let _164_1072 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _164_1072))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _164_1073))
in (quant qx _164_1074))
in (FStar_Syntax_Const.op_Minus, _164_1075))
in (let _164_1152 = (let _164_1151 = (let _164_1084 = (let _164_1083 = (let _164_1082 = (let _164_1081 = (let _164_1080 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1079 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1080, _164_1079)))
in (FStar_SMTEncoding_Term.mkAdd _164_1081))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _164_1082))
in (quant xy _164_1083))
in (FStar_Syntax_Const.op_Addition, _164_1084))
in (let _164_1150 = (let _164_1149 = (let _164_1093 = (let _164_1092 = (let _164_1091 = (let _164_1090 = (let _164_1089 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1088 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1089, _164_1088)))
in (FStar_SMTEncoding_Term.mkMul _164_1090))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _164_1091))
in (quant xy _164_1092))
in (FStar_Syntax_Const.op_Multiply, _164_1093))
in (let _164_1148 = (let _164_1147 = (let _164_1102 = (let _164_1101 = (let _164_1100 = (let _164_1099 = (let _164_1098 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1097 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1098, _164_1097)))
in (FStar_SMTEncoding_Term.mkDiv _164_1099))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _164_1100))
in (quant xy _164_1101))
in (FStar_Syntax_Const.op_Division, _164_1102))
in (let _164_1146 = (let _164_1145 = (let _164_1111 = (let _164_1110 = (let _164_1109 = (let _164_1108 = (let _164_1107 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1106 = (FStar_SMTEncoding_Term.unboxInt y)
in (_164_1107, _164_1106)))
in (FStar_SMTEncoding_Term.mkMod _164_1108))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _164_1109))
in (quant xy _164_1110))
in (FStar_Syntax_Const.op_Modulus, _164_1111))
in (let _164_1144 = (let _164_1143 = (let _164_1120 = (let _164_1119 = (let _164_1118 = (let _164_1117 = (let _164_1116 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _164_1115 = (FStar_SMTEncoding_Term.unboxBool y)
in (_164_1116, _164_1115)))
in (FStar_SMTEncoding_Term.mkAnd _164_1117))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1118))
in (quant xy _164_1119))
in (FStar_Syntax_Const.op_And, _164_1120))
in (let _164_1142 = (let _164_1141 = (let _164_1129 = (let _164_1128 = (let _164_1127 = (let _164_1126 = (let _164_1125 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _164_1124 = (FStar_SMTEncoding_Term.unboxBool y)
in (_164_1125, _164_1124)))
in (FStar_SMTEncoding_Term.mkOr _164_1126))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1127))
in (quant xy _164_1128))
in (FStar_Syntax_Const.op_Or, _164_1129))
in (let _164_1140 = (let _164_1139 = (let _164_1136 = (let _164_1135 = (let _164_1134 = (let _164_1133 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _164_1133))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_1134))
in (quant qx _164_1135))
in (FStar_Syntax_Const.op_Negation, _164_1136))
in (_164_1139)::[])
in (_164_1141)::_164_1140))
in (_164_1143)::_164_1142))
in (_164_1145)::_164_1144))
in (_164_1147)::_164_1146))
in (_164_1149)::_164_1148))
in (_164_1151)::_164_1150))
in (_164_1153)::_164_1152))
in (_164_1155)::_164_1154))
in (_164_1157)::_164_1156))
in (_164_1159)::_164_1158))
in (_164_1161)::_164_1160))
in (_164_1163)::_164_1162))
in (_164_1165)::_164_1164))
in (_164_1167)::_164_1166))
in (
# 1039 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _164_1199 = (FStar_All.pipe_right prims (FStar_List.filter (fun _79_1706 -> (match (_79_1706) with
| (l', _79_1705) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _164_1199 (FStar_List.collect (fun _79_1710 -> (match (_79_1710) with
| (_79_1708, b) -> begin
(b v)
end))))))
in (
# 1041 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _79_1716 -> (match (_79_1716) with
| (l', _79_1715) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1044 "FStar.SMTEncoding.Encode.fst"
let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (
# 1047 "FStar.SMTEncoding.Encode.fst"
let _79_1722 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_79_1722) with
| (xxsym, xx) -> begin
(
# 1048 "FStar.SMTEncoding.Encode.fst"
let _79_1725 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_79_1725) with
| (ffsym, ff) -> begin
(
# 1049 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _164_1225 = (let _164_1224 = (let _164_1223 = (let _164_1222 = (let _164_1221 = (let _164_1220 = (let _164_1219 = (let _164_1218 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _164_1218))
in (FStar_SMTEncoding_Term.mkEq _164_1219))
in (xx_has_type, _164_1220))
in (FStar_SMTEncoding_Term.mkImp _164_1221))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _164_1222))
in (FStar_SMTEncoding_Term.mkForall _164_1223))
in (_164_1224, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_164_1225)))
end))
end)))

# 1051 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1054 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1055 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1057 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1058 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1060 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun env nm tt -> (
# 1061 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _164_1246 = (let _164_1237 = (let _164_1236 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_164_1236, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_164_1237))
in (let _164_1245 = (let _164_1244 = (let _164_1243 = (let _164_1242 = (let _164_1241 = (let _164_1240 = (let _164_1239 = (let _164_1238 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _164_1238))
in (FStar_SMTEncoding_Term.mkImp _164_1239))
in (((typing_pred)::[])::[], (xx)::[], _164_1240))
in (mkForall_fuel _164_1241))
in (_164_1242, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_164_1243))
in (_164_1244)::[])
in (_164_1246)::_164_1245))))
in (
# 1064 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun env nm tt -> (
# 1065 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1066 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1067 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _164_1269 = (let _164_1258 = (let _164_1257 = (let _164_1256 = (let _164_1255 = (let _164_1254 = (let _164_1253 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _164_1253))
in (FStar_SMTEncoding_Term.mkImp _164_1254))
in (((typing_pred)::[])::[], (xx)::[], _164_1255))
in (mkForall_fuel _164_1256))
in (_164_1257, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_164_1258))
in (let _164_1268 = (let _164_1267 = (let _164_1266 = (let _164_1265 = (let _164_1264 = (let _164_1263 = (let _164_1260 = (let _164_1259 = (FStar_SMTEncoding_Term.boxBool b)
in (_164_1259)::[])
in (_164_1260)::[])
in (let _164_1262 = (let _164_1261 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _164_1261 tt))
in (_164_1263, (bb)::[], _164_1262)))
in (FStar_SMTEncoding_Term.mkForall _164_1264))
in (_164_1265, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_164_1266))
in (_164_1267)::[])
in (_164_1269)::_164_1268))))))
in (
# 1070 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun env nm tt -> (
# 1071 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1072 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1073 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1074 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1075 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1076 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1077 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _164_1283 = (let _164_1282 = (let _164_1281 = (let _164_1280 = (let _164_1279 = (let _164_1278 = (FStar_SMTEncoding_Term.boxInt a)
in (let _164_1277 = (let _164_1276 = (FStar_SMTEncoding_Term.boxInt b)
in (_164_1276)::[])
in (_164_1278)::_164_1277))
in (tt)::_164_1279)
in (tt)::_164_1280)
in ("Prims.Precedes", _164_1281))
in (FStar_SMTEncoding_Term.mkApp _164_1282))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _164_1283))
in (
# 1078 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _164_1284 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _164_1284))
in (let _164_1326 = (let _164_1290 = (let _164_1289 = (let _164_1288 = (let _164_1287 = (let _164_1286 = (let _164_1285 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _164_1285))
in (FStar_SMTEncoding_Term.mkImp _164_1286))
in (((typing_pred)::[])::[], (xx)::[], _164_1287))
in (mkForall_fuel _164_1288))
in (_164_1289, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_164_1290))
in (let _164_1325 = (let _164_1324 = (let _164_1298 = (let _164_1297 = (let _164_1296 = (let _164_1295 = (let _164_1292 = (let _164_1291 = (FStar_SMTEncoding_Term.boxInt b)
in (_164_1291)::[])
in (_164_1292)::[])
in (let _164_1294 = (let _164_1293 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _164_1293 tt))
in (_164_1295, (bb)::[], _164_1294)))
in (FStar_SMTEncoding_Term.mkForall _164_1296))
in (_164_1297, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_164_1298))
in (let _164_1323 = (let _164_1322 = (let _164_1321 = (let _164_1320 = (let _164_1319 = (let _164_1318 = (let _164_1317 = (let _164_1316 = (let _164_1315 = (let _164_1314 = (let _164_1313 = (let _164_1312 = (let _164_1301 = (let _164_1300 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _164_1299 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_164_1300, _164_1299)))
in (FStar_SMTEncoding_Term.mkGT _164_1301))
in (let _164_1311 = (let _164_1310 = (let _164_1304 = (let _164_1303 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _164_1302 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_164_1303, _164_1302)))
in (FStar_SMTEncoding_Term.mkGTE _164_1304))
in (let _164_1309 = (let _164_1308 = (let _164_1307 = (let _164_1306 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _164_1305 = (FStar_SMTEncoding_Term.unboxInt x)
in (_164_1306, _164_1305)))
in (FStar_SMTEncoding_Term.mkLT _164_1307))
in (_164_1308)::[])
in (_164_1310)::_164_1309))
in (_164_1312)::_164_1311))
in (typing_pred_y)::_164_1313)
in (typing_pred)::_164_1314)
in (FStar_SMTEncoding_Term.mk_and_l _164_1315))
in (_164_1316, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _164_1317))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _164_1318))
in (mkForall_fuel _164_1319))
in (_164_1320, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_164_1321))
in (_164_1322)::[])
in (_164_1324)::_164_1323))
in (_164_1326)::_164_1325)))))))))))
in (
# 1090 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun env nm tt -> (let _164_1337 = (let _164_1336 = (let _164_1335 = (let _164_1334 = (let _164_1333 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _164_1333))
in (FStar_SMTEncoding_Term.mkEq _164_1334))
in (_164_1335, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_164_1336))
in (_164_1337)::[]))
in (
# 1092 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun env nm tt -> (
# 1093 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1094 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _164_1360 = (let _164_1349 = (let _164_1348 = (let _164_1347 = (let _164_1346 = (let _164_1345 = (let _164_1344 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _164_1344))
in (FStar_SMTEncoding_Term.mkImp _164_1345))
in (((typing_pred)::[])::[], (xx)::[], _164_1346))
in (mkForall_fuel _164_1347))
in (_164_1348, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_164_1349))
in (let _164_1359 = (let _164_1358 = (let _164_1357 = (let _164_1356 = (let _164_1355 = (let _164_1354 = (let _164_1351 = (let _164_1350 = (FStar_SMTEncoding_Term.boxString b)
in (_164_1350)::[])
in (_164_1351)::[])
in (let _164_1353 = (let _164_1352 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _164_1352 tt))
in (_164_1354, (bb)::[], _164_1353)))
in (FStar_SMTEncoding_Term.mkForall _164_1355))
in (_164_1356, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_164_1357))
in (_164_1358)::[])
in (_164_1360)::_164_1359))))))
in (
# 1098 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun env reft_name _79_1768 -> (
# 1099 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1100 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1101 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1102 "FStar.SMTEncoding.Encode.fst"
let refa = (let _164_1369 = (let _164_1368 = (let _164_1367 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_164_1367)::[])
in (reft_name, _164_1368))
in (FStar_SMTEncoding_Term.mkApp _164_1369))
in (
# 1103 "FStar.SMTEncoding.Encode.fst"
let refb = (let _164_1372 = (let _164_1371 = (let _164_1370 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_164_1370)::[])
in (reft_name, _164_1371))
in (FStar_SMTEncoding_Term.mkApp _164_1372))
in (
# 1104 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1105 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _164_1391 = (let _164_1378 = (let _164_1377 = (let _164_1376 = (let _164_1375 = (let _164_1374 = (let _164_1373 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _164_1373))
in (FStar_SMTEncoding_Term.mkImp _164_1374))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _164_1375))
in (mkForall_fuel _164_1376))
in (_164_1377, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_164_1378))
in (let _164_1390 = (let _164_1389 = (let _164_1388 = (let _164_1387 = (let _164_1386 = (let _164_1385 = (let _164_1384 = (let _164_1383 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _164_1382 = (let _164_1381 = (let _164_1380 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _164_1379 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_164_1380, _164_1379)))
in (FStar_SMTEncoding_Term.mkEq _164_1381))
in (_164_1383, _164_1382)))
in (FStar_SMTEncoding_Term.mkImp _164_1384))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _164_1385))
in (mkForall_fuel' 2 _164_1386))
in (_164_1387, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_164_1388))
in (_164_1389)::[])
in (_164_1391)::_164_1390))))))))))
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun env nm false_tm -> (
# 1109 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _164_1400 = (let _164_1399 = (let _164_1398 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_164_1398, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_164_1399))
in (_164_1400)::[])))
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun env conj _79_1785 -> (
# 1112 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1113 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1114 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1115 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1116 "FStar.SMTEncoding.Encode.fst"
let valid = (let _164_1409 = (let _164_1408 = (let _164_1407 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_164_1407)::[])
in ("Valid", _164_1408))
in (FStar_SMTEncoding_Term.mkApp _164_1409))
in (
# 1117 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1118 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _164_1416 = (let _164_1415 = (let _164_1414 = (let _164_1413 = (let _164_1412 = (let _164_1411 = (let _164_1410 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_164_1410, valid))
in (FStar_SMTEncoding_Term.mkIff _164_1411))
in (((valid)::[])::[], (aa)::(bb)::[], _164_1412))
in (FStar_SMTEncoding_Term.mkForall _164_1413))
in (_164_1414, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_164_1415))
in (_164_1416)::[])))))))))
in (
# 1120 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun env disj _79_1797 -> (
# 1121 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1122 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1123 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1125 "FStar.SMTEncoding.Encode.fst"
let valid = (let _164_1425 = (let _164_1424 = (let _164_1423 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_164_1423)::[])
in ("Valid", _164_1424))
in (FStar_SMTEncoding_Term.mkApp _164_1425))
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _164_1432 = (let _164_1431 = (let _164_1430 = (let _164_1429 = (let _164_1428 = (let _164_1427 = (let _164_1426 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_164_1426, valid))
in (FStar_SMTEncoding_Term.mkIff _164_1427))
in (((valid)::[])::[], (aa)::(bb)::[], _164_1428))
in (FStar_SMTEncoding_Term.mkForall _164_1429))
in (_164_1430, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_164_1431))
in (_164_1432)::[])))))))))
in (
# 1129 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun env eq2 tt -> (
# 1130 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1131 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1132 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1134 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1135 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1136 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1137 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1138 "FStar.SMTEncoding.Encode.fst"
let valid = (let _164_1441 = (let _164_1440 = (let _164_1439 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_164_1439)::[])
in ("Valid", _164_1440))
in (FStar_SMTEncoding_Term.mkApp _164_1441))
in (let _164_1448 = (let _164_1447 = (let _164_1446 = (let _164_1445 = (let _164_1444 = (let _164_1443 = (let _164_1442 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_164_1442, valid))
in (FStar_SMTEncoding_Term.mkIff _164_1443))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _164_1444))
in (FStar_SMTEncoding_Term.mkForall _164_1445))
in (_164_1446, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_164_1447))
in (_164_1448)::[])))))))))))
in (
# 1140 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun env imp tt -> (
# 1141 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1142 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1143 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1144 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1145 "FStar.SMTEncoding.Encode.fst"
let valid = (let _164_1457 = (let _164_1456 = (let _164_1455 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_164_1455)::[])
in ("Valid", _164_1456))
in (FStar_SMTEncoding_Term.mkApp _164_1457))
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _164_1464 = (let _164_1463 = (let _164_1462 = (let _164_1461 = (let _164_1460 = (let _164_1459 = (let _164_1458 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_164_1458, valid))
in (FStar_SMTEncoding_Term.mkIff _164_1459))
in (((valid)::[])::[], (aa)::(bb)::[], _164_1460))
in (FStar_SMTEncoding_Term.mkForall _164_1461))
in (_164_1462, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_164_1463))
in (_164_1464)::[])))))))))
in (
# 1149 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun env iff tt -> (
# 1150 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1151 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1152 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1154 "FStar.SMTEncoding.Encode.fst"
let valid = (let _164_1473 = (let _164_1472 = (let _164_1471 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_164_1471)::[])
in ("Valid", _164_1472))
in (FStar_SMTEncoding_Term.mkApp _164_1473))
in (
# 1155 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1156 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _164_1480 = (let _164_1479 = (let _164_1478 = (let _164_1477 = (let _164_1476 = (let _164_1475 = (let _164_1474 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_164_1474, valid))
in (FStar_SMTEncoding_Term.mkIff _164_1475))
in (((valid)::[])::[], (aa)::(bb)::[], _164_1476))
in (FStar_SMTEncoding_Term.mkForall _164_1477))
in (_164_1478, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_164_1479))
in (_164_1480)::[])))))))))
in (
# 1158 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun env for_all tt -> (
# 1159 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1160 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1161 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1162 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1163 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1164 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1165 "FStar.SMTEncoding.Encode.fst"
let valid = (let _164_1489 = (let _164_1488 = (let _164_1487 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_164_1487)::[])
in ("Valid", _164_1488))
in (FStar_SMTEncoding_Term.mkApp _164_1489))
in (
# 1166 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _164_1492 = (let _164_1491 = (let _164_1490 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_164_1490)::[])
in ("Valid", _164_1491))
in (FStar_SMTEncoding_Term.mkApp _164_1492))
in (let _164_1506 = (let _164_1505 = (let _164_1504 = (let _164_1503 = (let _164_1502 = (let _164_1501 = (let _164_1500 = (let _164_1499 = (let _164_1498 = (let _164_1494 = (let _164_1493 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_164_1493)::[])
in (_164_1494)::[])
in (let _164_1497 = (let _164_1496 = (let _164_1495 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_164_1495, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _164_1496))
in (_164_1498, (xx)::[], _164_1497)))
in (FStar_SMTEncoding_Term.mkForall _164_1499))
in (_164_1500, valid))
in (FStar_SMTEncoding_Term.mkIff _164_1501))
in (((valid)::[])::[], (aa)::(bb)::[], _164_1502))
in (FStar_SMTEncoding_Term.mkForall _164_1503))
in (_164_1504, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_164_1505))
in (_164_1506)::[]))))))))))
in (
# 1168 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun env for_some tt -> (
# 1169 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1170 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1171 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1172 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1173 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1174 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1175 "FStar.SMTEncoding.Encode.fst"
let valid = (let _164_1515 = (let _164_1514 = (let _164_1513 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_164_1513)::[])
in ("Valid", _164_1514))
in (FStar_SMTEncoding_Term.mkApp _164_1515))
in (
# 1176 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _164_1518 = (let _164_1517 = (let _164_1516 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_164_1516)::[])
in ("Valid", _164_1517))
in (FStar_SMTEncoding_Term.mkApp _164_1518))
in (let _164_1532 = (let _164_1531 = (let _164_1530 = (let _164_1529 = (let _164_1528 = (let _164_1527 = (let _164_1526 = (let _164_1525 = (let _164_1524 = (let _164_1520 = (let _164_1519 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_164_1519)::[])
in (_164_1520)::[])
in (let _164_1523 = (let _164_1522 = (let _164_1521 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_164_1521, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _164_1522))
in (_164_1524, (xx)::[], _164_1523)))
in (FStar_SMTEncoding_Term.mkExists _164_1525))
in (_164_1526, valid))
in (FStar_SMTEncoding_Term.mkIff _164_1527))
in (((valid)::[])::[], (aa)::(bb)::[], _164_1528))
in (FStar_SMTEncoding_Term.mkForall _164_1529))
in (_164_1530, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_164_1531))
in (_164_1532)::[]))))))))))
in (
# 1178 "FStar.SMTEncoding.Encode.fst"
let mk_range_of_interp = (fun env range_of tt -> (
# 1179 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1180 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1181 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1182 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1183 "FStar.SMTEncoding.Encode.fst"
let range_of_ty = (FStar_SMTEncoding_Term.mkApp (range_of, (a)::(b)::[]))
in (let _164_1543 = (let _164_1542 = (let _164_1541 = (let _164_1540 = (let _164_1539 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_of_ty)
in (((range_of_ty)::[])::[], (aa)::(bb)::[], _164_1539))
in (FStar_SMTEncoding_Term.mkForall _164_1540))
in (_164_1541, Some ("Range_const typing")))
in FStar_SMTEncoding_Term.Assume (_164_1542))
in (_164_1543)::[])))))))
in (
# 1190 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_of_lid, mk_range_of_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _79_1883 -> (match (_79_1883) with
| (l, _79_1882) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_79_1886, f) -> begin
(f env s tt)
end))))))))))))))))))))))

# 1211 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1214 "FStar.SMTEncoding.Encode.fst"
let _79_1892 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _164_1755 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _164_1755))
end else begin
()
end
in (
# 1217 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1220 "FStar.SMTEncoding.Encode.fst"
let _79_1900 = (encode_sigelt' env se)
in (match (_79_1900) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _164_1758 = (let _164_1757 = (let _164_1756 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_164_1756))
in (_164_1757)::[])
in (_164_1758, e))
end
| _79_1903 -> begin
(let _164_1765 = (let _164_1764 = (let _164_1760 = (let _164_1759 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_164_1759))
in (_164_1760)::g)
in (let _164_1763 = (let _164_1762 = (let _164_1761 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_164_1761))
in (_164_1762)::[])
in (FStar_List.append _164_1764 _164_1763)))
in (_164_1765, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1226 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1232 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1233 "FStar.SMTEncoding.Encode.fst"
let tt = (norm env t)
in (
# 1239 "FStar.SMTEncoding.Encode.fst"
let _79_1916 = (encode_free_var env lid t tt quals)
in (match (_79_1916) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _164_1779 = (let _164_1778 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _164_1778))
in (_164_1779, env))
end else begin
(decls, env)
end
end))))
in (
# 1245 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _79_1923 lb -> (match (_79_1923) with
| (decls, env) -> begin
(
# 1247 "FStar.SMTEncoding.Encode.fst"
let _79_1927 = (let _164_1788 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _164_1788 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_79_1927) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _79_1945, _79_1947, _79_1949, _79_1951) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1259 "FStar.SMTEncoding.Encode.fst"
let _79_1957 = (new_term_constant_and_tok_from_lid env lid)
in (match (_79_1957) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _79_1960, t, quals, _79_1964) -> begin
(
# 1263 "FStar.SMTEncoding.Encode.fst"
let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_12 -> (match (_79_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _79_1977 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(
# 1268 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (
# 1269 "FStar.SMTEncoding.Encode.fst"
let _79_1982 = (encode_top_level_val env fv t quals)
in (match (_79_1982) with
| (decls, env) -> begin
(
# 1270 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1271 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _164_1791 = (let _164_1790 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _164_1790))
in (_164_1791, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _79_1988, _79_1990) -> begin
(
# 1277 "FStar.SMTEncoding.Encode.fst"
let _79_1995 = (encode_formula f env)
in (match (_79_1995) with
| (f, decls) -> begin
(
# 1278 "FStar.SMTEncoding.Encode.fst"
let g = (let _164_1796 = (let _164_1795 = (let _164_1794 = (let _164_1793 = (let _164_1792 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _164_1792))
in Some (_164_1793))
in (f, _164_1794))
in FStar_SMTEncoding_Term.Assume (_164_1795))
in (_164_1796)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _79_2000, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_79_2005, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _79_2013; FStar_Syntax_Syntax.lbtyp = _79_2011; FStar_Syntax_Syntax.lbeff = _79_2009; FStar_Syntax_Syntax.lbdef = _79_2007}::[]), _79_2020, _79_2022, _79_2024) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1285 "FStar.SMTEncoding.Encode.fst"
let _79_2030 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_79_2030) with
| (tname, ttok, env) -> begin
(
# 1286 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1287 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1288 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _164_1799 = (let _164_1798 = (let _164_1797 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_164_1797)::[])
in ("Valid", _164_1798))
in (FStar_SMTEncoding_Term.mkApp _164_1799))
in (
# 1289 "FStar.SMTEncoding.Encode.fst"
let decls = (let _164_1807 = (let _164_1806 = (let _164_1805 = (let _164_1804 = (let _164_1803 = (let _164_1802 = (let _164_1801 = (let _164_1800 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _164_1800))
in (FStar_SMTEncoding_Term.mkEq _164_1801))
in (((valid_b2t_x)::[])::[], (xx)::[], _164_1802))
in (FStar_SMTEncoding_Term.mkForall _164_1803))
in (_164_1804, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_164_1805))
in (_164_1806)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_164_1807)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_79_2036, _79_2038, _79_2040, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_13 -> (match (_79_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _79_2050 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _79_2056, _79_2058, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_14 -> (match (_79_14) with
| FStar_Syntax_Syntax.Projector (_79_2064) -> begin
true
end
| _79_2067 -> begin
false
end)))) -> begin
(
# 1303 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1304 "FStar.SMTEncoding.Encode.fst"
let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_79_2071) -> begin
([], env)
end
| None -> begin
(
# 1309 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _79_2079, _79_2081, quals) -> begin
(
# 1315 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1316 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1317 "FStar.SMTEncoding.Encode.fst"
let _79_2093 = (FStar_Util.first_N nbinders formals)
in (match (_79_2093) with
| (formals, extra_formals) -> begin
(
# 1318 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _79_2097 _79_2101 -> (match ((_79_2097, _79_2101)) with
| ((formal, _79_2096), (binder, _79_2100)) -> begin
(let _164_1821 = (let _164_1820 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _164_1820))
in FStar_Syntax_Syntax.NT (_164_1821))
end)) formals binders)
in (
# 1319 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _164_1825 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _79_2105 -> (match (_79_2105) with
| (x, i) -> begin
(let _164_1824 = (
# 1319 "FStar.SMTEncoding.Encode.fst"
let _79_2106 = x
in (let _164_1823 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _79_2106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _79_2106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _164_1823}))
in (_164_1824, i))
end))))
in (FStar_All.pipe_right _164_1825 FStar_Syntax_Util.name_binders))
in (
# 1320 "FStar.SMTEncoding.Encode.fst"
let body = (let _164_1832 = (FStar_Syntax_Subst.compress body)
in (let _164_1831 = (let _164_1826 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _164_1826))
in (let _164_1830 = (let _164_1829 = (let _164_1828 = (FStar_Syntax_Subst.subst subst t)
in _164_1828.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _164_1827 -> Some (_164_1827)) _164_1829))
in (FStar_Syntax_Syntax.extend_app_n _164_1832 _164_1831 _164_1830 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1323 "FStar.SMTEncoding.Encode.fst"
let destruct_bound_function = (fun flid t_norm e -> (
# 1324 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t_norm -> (match ((let _164_1843 = (FStar_Syntax_Util.unascribe e)
in _164_1843.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1327 "FStar.SMTEncoding.Encode.fst"
let _79_2125 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_79_2125) with
| (binders, body, opening) -> begin
(match ((let _164_1844 = (FStar_Syntax_Subst.compress t_norm)
in _164_1844.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1330 "FStar.SMTEncoding.Encode.fst"
let _79_2132 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_79_2132) with
| (formals, c) -> begin
(
# 1331 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1332 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1333 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1335 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1336 "FStar.SMTEncoding.Encode.fst"
let _79_2139 = (FStar_Util.first_N nformals binders)
in (match (_79_2139) with
| (bs0, rest) -> begin
(
# 1337 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1338 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _79_2143 _79_2147 -> (match ((_79_2143, _79_2147)) with
| ((b, _79_2142), (x, _79_2146)) -> begin
(let _164_1848 = (let _164_1847 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _164_1847))
in FStar_Syntax_Syntax.NT (_164_1848))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1340 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1343 "FStar.SMTEncoding.Encode.fst"
let _79_2153 = (eta_expand binders formals body tres)
in (match (_79_2153) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _79_2156) -> begin
(aux true x.FStar_Syntax_Syntax.sort)
end
| _79_2160 when (not (norm)) -> begin
(
# 1351 "FStar.SMTEncoding.Encode.fst"
let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _79_2163 -> begin
(let _164_1851 = (let _164_1850 = (FStar_Syntax_Print.term_to_string e)
in (let _164_1849 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _164_1850 _164_1849)))
in (FStar_All.failwith _164_1851))
end)
end))
end
| _79_2165 -> begin
(match ((let _164_1852 = (FStar_Syntax_Subst.compress t_norm)
in _164_1852.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1361 "FStar.SMTEncoding.Encode.fst"
let _79_2172 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_79_2172) with
| (formals, c) -> begin
(
# 1362 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1363 "FStar.SMTEncoding.Encode.fst"
let _79_2176 = (eta_expand [] formals e tres)
in (match (_79_2176) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _79_2178 -> begin
([], e, [], t_norm)
end)
end))
in (aux false t_norm)))
in (FStar_All.try_with (fun _79_2180 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1371 "FStar.SMTEncoding.Encode.fst"
let _79_2206 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _79_2193 lb -> (match (_79_2193) with
| (toks, typs, decls, env) -> begin
(
# 1373 "FStar.SMTEncoding.Encode.fst"
let _79_2195 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1374 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1375 "FStar.SMTEncoding.Encode.fst"
let _79_2201 = (let _164_1857 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _164_1857 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_79_2201) with
| (tok, decl, env) -> begin
(let _164_1860 = (let _164_1859 = (let _164_1858 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_164_1858, tok))
in (_164_1859)::toks)
in (_164_1860, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_79_2206) with
| (toks, typs, decls, env) -> begin
(
# 1377 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1378 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1379 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_15 -> (match (_79_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _79_2213 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _164_1863 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _164_1863)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _79_2223; FStar_Syntax_Syntax.lbunivs = _79_2221; FStar_Syntax_Syntax.lbtyp = _79_2219; FStar_Syntax_Syntax.lbeff = _79_2217; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid_fv, (f, ftok))::[]) -> begin
(
# 1386 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1387 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1388 "FStar.SMTEncoding.Encode.fst"
let _79_2243 = (destruct_bound_function flid t_norm e)
in (match (_79_2243) with
| (binders, body, _79_2240, _79_2242) -> begin
(
# 1389 "FStar.SMTEncoding.Encode.fst"
let _79_2250 = (encode_binders None binders env)
in (match (_79_2250) with
| (vars, guards, env', binder_decls, _79_2249) -> begin
(
# 1390 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _79_2253 -> begin
(let _164_1865 = (let _164_1864 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _164_1864))
in (FStar_SMTEncoding_Term.mkApp _164_1865))
end)
in (
# 1391 "FStar.SMTEncoding.Encode.fst"
let _79_2259 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _164_1867 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _164_1866 = (encode_formula body env')
in (_164_1867, _164_1866)))
end else begin
(let _164_1868 = (encode_term body env')
in (app, _164_1868))
end
in (match (_79_2259) with
| (app, (body, decls2)) -> begin
(
# 1395 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _164_1877 = (let _164_1876 = (let _164_1873 = (let _164_1872 = (let _164_1871 = (let _164_1870 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _164_1869 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_164_1870, _164_1869)))
in (FStar_SMTEncoding_Term.mkImp _164_1871))
in (((app)::[])::[], vars, _164_1872))
in (FStar_SMTEncoding_Term.mkForall _164_1873))
in (let _164_1875 = (let _164_1874 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_164_1874))
in (_164_1876, _164_1875)))
in FStar_SMTEncoding_Term.Assume (_164_1877))
in (let _164_1879 = (let _164_1878 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _164_1878))
in (_164_1879, env)))
end)))
end))
end))))
end
| _79_2262 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1401 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _164_1880 = (varops.fresh "fuel")
in (_164_1880, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1402 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1403 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1404 "FStar.SMTEncoding.Encode.fst"
let _79_2280 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _79_2268 _79_2273 -> (match ((_79_2268, _79_2273)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(
# 1405 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1406 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1407 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1408 "FStar.SMTEncoding.Encode.fst"
let env = (let _164_1885 = (let _164_1884 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _164_1883 -> Some (_164_1883)) _164_1884))
in (push_free_var env flid gtok _164_1885))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_79_2280) with
| (gtoks, env) -> begin
(
# 1410 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1411 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _79_2289 t_norm _79_2300 -> (match ((_79_2289, _79_2300)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _79_2299; FStar_Syntax_Syntax.lbunivs = _79_2297; FStar_Syntax_Syntax.lbtyp = _79_2295; FStar_Syntax_Syntax.lbeff = _79_2293; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1412 "FStar.SMTEncoding.Encode.fst"
let _79_2305 = (destruct_bound_function flid t_norm e)
in (match (_79_2305) with
| (binders, body, formals, tres) -> begin
(
# 1413 "FStar.SMTEncoding.Encode.fst"
let _79_2312 = (encode_binders None binders env)
in (match (_79_2312) with
| (vars, guards, env', binder_decls, _79_2311) -> begin
(
# 1414 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _164_1896 = (let _164_1895 = (let _164_1894 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_164_1894)
in (g, _164_1895, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_164_1896))
in (
# 1415 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1416 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1417 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1418 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1419 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _164_1899 = (let _164_1898 = (let _164_1897 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_164_1897)::vars_tm)
in (g, _164_1898))
in (FStar_SMTEncoding_Term.mkApp _164_1899))
in (
# 1420 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _164_1902 = (let _164_1901 = (let _164_1900 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_164_1900)::vars_tm)
in (g, _164_1901))
in (FStar_SMTEncoding_Term.mkApp _164_1902))
in (
# 1421 "FStar.SMTEncoding.Encode.fst"
let _79_2322 = (encode_term body env')
in (match (_79_2322) with
| (body_tm, decls2) -> begin
(
# 1422 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _164_1911 = (let _164_1910 = (let _164_1907 = (let _164_1906 = (let _164_1905 = (let _164_1904 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _164_1903 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_164_1904, _164_1903)))
in (FStar_SMTEncoding_Term.mkImp _164_1905))
in (((gsapp)::[])::[], (fuel)::vars, _164_1906))
in (FStar_SMTEncoding_Term.mkForall _164_1907))
in (let _164_1909 = (let _164_1908 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_164_1908))
in (_164_1910, _164_1909)))
in FStar_SMTEncoding_Term.Assume (_164_1911))
in (
# 1424 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _164_1915 = (let _164_1914 = (let _164_1913 = (let _164_1912 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _164_1912))
in (FStar_SMTEncoding_Term.mkForall _164_1913))
in (_164_1914, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_164_1915))
in (
# 1426 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _164_1924 = (let _164_1923 = (let _164_1922 = (let _164_1921 = (let _164_1920 = (let _164_1919 = (let _164_1918 = (let _164_1917 = (let _164_1916 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_164_1916)::vars_tm)
in (g, _164_1917))
in (FStar_SMTEncoding_Term.mkApp _164_1918))
in (gsapp, _164_1919))
in (FStar_SMTEncoding_Term.mkEq _164_1920))
in (((gsapp)::[])::[], (fuel)::vars, _164_1921))
in (FStar_SMTEncoding_Term.mkForall _164_1922))
in (_164_1923, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_164_1924))
in (
# 1428 "FStar.SMTEncoding.Encode.fst"
let _79_2345 = (
# 1429 "FStar.SMTEncoding.Encode.fst"
let _79_2332 = (encode_binders None formals env0)
in (match (_79_2332) with
| (vars, v_guards, env, binder_decls, _79_2331) -> begin
(
# 1430 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1431 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1432 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1433 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _164_1925 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _164_1925 ((fuel)::vars)))
in (let _164_1929 = (let _164_1928 = (let _164_1927 = (let _164_1926 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _164_1926))
in (FStar_SMTEncoding_Term.mkForall _164_1927))
in (_164_1928, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_164_1929)))
in (
# 1436 "FStar.SMTEncoding.Encode.fst"
let _79_2342 = (
# 1437 "FStar.SMTEncoding.Encode.fst"
let _79_2339 = (encode_term_pred None tres env gapp)
in (match (_79_2339) with
| (g_typing, d3) -> begin
(let _164_1937 = (let _164_1936 = (let _164_1935 = (let _164_1934 = (let _164_1933 = (let _164_1932 = (let _164_1931 = (let _164_1930 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_164_1930, g_typing))
in (FStar_SMTEncoding_Term.mkImp _164_1931))
in (((gapp)::[])::[], (fuel)::vars, _164_1932))
in (FStar_SMTEncoding_Term.mkForall _164_1933))
in (_164_1934, Some ("Typing correspondence of token to term")))
in FStar_SMTEncoding_Term.Assume (_164_1935))
in (_164_1936)::[])
in (d3, _164_1937))
end))
in (match (_79_2342) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_79_2345) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1441 "FStar.SMTEncoding.Encode.fst"
let _79_2361 = (let _164_1940 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _79_2349 _79_2353 -> (match ((_79_2349, _79_2353)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1442 "FStar.SMTEncoding.Encode.fst"
let _79_2357 = (encode_one_binding env0 gtok ty bs)
in (match (_79_2357) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _164_1940))
in (match (_79_2361) with
| (decls, eqns, env0) -> begin
(
# 1444 "FStar.SMTEncoding.Encode.fst"
let _79_2370 = (let _164_1942 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _164_1942 (FStar_List.partition (fun _79_16 -> (match (_79_16) with
| FStar_SMTEncoding_Term.DeclFun (_79_2364) -> begin
true
end
| _79_2367 -> begin
false
end)))))
in (match (_79_2370) with
| (prefix_decls, rest) -> begin
(
# 1447 "FStar.SMTEncoding.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _79_2179 -> (match (_79_2179) with
| Let_rec_unencodeable -> begin
(
# 1450 "FStar.SMTEncoding.Encode.fst"
let msg = (let _164_1945 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _164_1945 (FStar_String.concat " and ")))
in (
# 1451 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _79_2374, _79_2376, _79_2378) -> begin
(
# 1456 "FStar.SMTEncoding.Encode.fst"
let _79_2383 = (encode_signature env ses)
in (match (_79_2383) with
| (g, env) -> begin
(
# 1457 "FStar.SMTEncoding.Encode.fst"
let _79_2395 = (FStar_All.pipe_right g (FStar_List.partition (fun _79_17 -> (match (_79_17) with
| FStar_SMTEncoding_Term.Assume (_79_2386, Some ("inversion axiom")) -> begin
false
end
| _79_2392 -> begin
true
end))))
in (match (_79_2395) with
| (g', inversions) -> begin
(
# 1460 "FStar.SMTEncoding.Encode.fst"
let _79_2404 = (FStar_All.pipe_right g' (FStar_List.partition (fun _79_18 -> (match (_79_18) with
| FStar_SMTEncoding_Term.DeclFun (_79_2398) -> begin
true
end
| _79_2401 -> begin
false
end))))
in (match (_79_2404) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _79_2407, tps, k, _79_2411, datas, quals, _79_2415) -> begin
(
# 1466 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _79_19 -> (match (_79_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _79_2422 -> begin
false
end))))
in (
# 1467 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1469 "FStar.SMTEncoding.Encode.fst"
let _79_2434 = c
in (match (_79_2434) with
| (name, args, _79_2429, _79_2431, _79_2433) -> begin
(let _164_1953 = (let _164_1952 = (let _164_1951 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _164_1951, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_164_1952))
in (_164_1953)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1473 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _164_1959 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _164_1959 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1477 "FStar.SMTEncoding.Encode.fst"
let _79_2441 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_79_2441) with
| (xxsym, xx) -> begin
(
# 1478 "FStar.SMTEncoding.Encode.fst"
let _79_2477 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _79_2444 l -> (match (_79_2444) with
| (out, decls) -> begin
(
# 1479 "FStar.SMTEncoding.Encode.fst"
let _79_2449 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_79_2449) with
| (_79_2447, data_t) -> begin
(
# 1480 "FStar.SMTEncoding.Encode.fst"
let _79_2452 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_79_2452) with
| (args, res) -> begin
(
# 1481 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _164_1962 = (FStar_Syntax_Subst.compress res)
in _164_1962.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_79_2454, indices) -> begin
indices
end
| _79_2459 -> begin
[]
end)
in (
# 1484 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _79_2465 -> (match (_79_2465) with
| (x, _79_2464) -> begin
(let _164_1967 = (let _164_1966 = (let _164_1965 = (mk_term_projector_name l x)
in (_164_1965, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _164_1966))
in (push_term_var env x _164_1967))
end)) env))
in (
# 1487 "FStar.SMTEncoding.Encode.fst"
let _79_2469 = (encode_args indices env)
in (match (_79_2469) with
| (indices, decls') -> begin
(
# 1488 "FStar.SMTEncoding.Encode.fst"
let _79_2470 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1490 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _164_1972 = (FStar_List.map2 (fun v a -> (let _164_1971 = (let _164_1970 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_164_1970, a))
in (FStar_SMTEncoding_Term.mkEq _164_1971))) vars indices)
in (FStar_All.pipe_right _164_1972 FStar_SMTEncoding_Term.mk_and_l))
in (let _164_1977 = (let _164_1976 = (let _164_1975 = (let _164_1974 = (let _164_1973 = (mk_data_tester env l xx)
in (_164_1973, eqs))
in (FStar_SMTEncoding_Term.mkAnd _164_1974))
in (out, _164_1975))
in (FStar_SMTEncoding_Term.mkOr _164_1976))
in (_164_1977, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_79_2477) with
| (data_ax, decls) -> begin
(
# 1492 "FStar.SMTEncoding.Encode.fst"
let _79_2480 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_79_2480) with
| (ffsym, ff) -> begin
(
# 1493 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _164_1978 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _164_1978 xx tapp))
in (let _164_1985 = (let _164_1984 = (let _164_1983 = (let _164_1982 = (let _164_1981 = (let _164_1980 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _164_1979 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _164_1980, _164_1979)))
in (FStar_SMTEncoding_Term.mkForall _164_1981))
in (_164_1982, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_164_1983))
in (_164_1984)::[])
in (FStar_List.append decls _164_1985)))
end))
end))
end))
end)
in (
# 1497 "FStar.SMTEncoding.Encode.fst"
let _79_2490 = (match ((let _164_1986 = (FStar_Syntax_Subst.compress k)
in _164_1986.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _79_2487 -> begin
(tps, k)
end)
in (match (_79_2490) with
| (formals, res) -> begin
(
# 1503 "FStar.SMTEncoding.Encode.fst"
let _79_2493 = (FStar_Syntax_Subst.open_term formals res)
in (match (_79_2493) with
| (formals, res) -> begin
(
# 1504 "FStar.SMTEncoding.Encode.fst"
let _79_2500 = (encode_binders None formals env)
in (match (_79_2500) with
| (vars, guards, env', binder_decls, _79_2499) -> begin
(
# 1506 "FStar.SMTEncoding.Encode.fst"
let _79_2504 = (new_term_constant_and_tok_from_lid env t)
in (match (_79_2504) with
| (tname, ttok, env) -> begin
(
# 1507 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1508 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1509 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _164_1988 = (let _164_1987 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _164_1987))
in (FStar_SMTEncoding_Term.mkApp _164_1988))
in (
# 1510 "FStar.SMTEncoding.Encode.fst"
let _79_2525 = (
# 1511 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _164_1992 = (let _164_1991 = (FStar_All.pipe_right vars (FStar_List.map (fun _79_2510 -> (match (_79_2510) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _164_1990 = (varops.next_id ())
in (tname, _164_1991, FStar_SMTEncoding_Term.Term_sort, _164_1990, false)))
in (constructor_or_logic_type_decl _164_1992))
in (
# 1512 "FStar.SMTEncoding.Encode.fst"
let _79_2522 = (match (vars) with
| [] -> begin
(let _164_1996 = (let _164_1995 = (let _164_1994 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _164_1993 -> Some (_164_1993)) _164_1994))
in (push_free_var env t tname _164_1995))
in ([], _164_1996))
end
| _79_2514 -> begin
(
# 1515 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1516 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _164_1997 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _164_1997))
in (
# 1517 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1518 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1521 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _164_2001 = (let _164_2000 = (let _164_1999 = (let _164_1998 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _164_1998))
in (FStar_SMTEncoding_Term.mkForall' _164_1999))
in (_164_2000, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_164_2001))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_79_2522) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_79_2525) with
| (decls, env) -> begin
(
# 1524 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1525 "FStar.SMTEncoding.Encode.fst"
let _79_2528 = (encode_term_pred None res env' tapp)
in (match (_79_2528) with
| (k, decls) -> begin
(
# 1526 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _164_2005 = (let _164_2004 = (let _164_2003 = (let _164_2002 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _164_2002))
in (_164_2003, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_164_2004))
in (_164_2005)::[])
end else begin
[]
end
in (let _164_2011 = (let _164_2010 = (let _164_2009 = (let _164_2008 = (let _164_2007 = (let _164_2006 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _164_2006))
in (FStar_SMTEncoding_Term.mkForall _164_2007))
in (_164_2008, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_164_2009))
in (_164_2010)::[])
in (FStar_List.append (FStar_List.append decls karr) _164_2011)))
end))
in (
# 1531 "FStar.SMTEncoding.Encode.fst"
let aux = (let _164_2015 = (let _164_2012 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _164_2012))
in (let _164_2014 = (let _164_2013 = (pretype_axiom tapp vars)
in (_164_2013)::[])
in (FStar_List.append _164_2015 _164_2014)))
in (
# 1536 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _79_2535, _79_2537, _79_2539, _79_2541, _79_2543, _79_2545, _79_2547) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _79_2552, t, _79_2555, n_tps, quals, _79_2559, drange) -> begin
(
# 1544 "FStar.SMTEncoding.Encode.fst"
let _79_2566 = (new_term_constant_and_tok_from_lid env d)
in (match (_79_2566) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1545 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1546 "FStar.SMTEncoding.Encode.fst"
let _79_2570 = (FStar_Syntax_Util.arrow_formals t)
in (match (_79_2570) with
| (formals, t_res) -> begin
(
# 1547 "FStar.SMTEncoding.Encode.fst"
let _79_2573 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_79_2573) with
| (fuel_var, fuel_tm) -> begin
(
# 1548 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1549 "FStar.SMTEncoding.Encode.fst"
let _79_2580 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_79_2580) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1550 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _164_2017 = (mk_term_projector_name d x)
in (_164_2017, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1551 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _164_2019 = (let _164_2018 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _164_2018, true))
in (FStar_All.pipe_right _164_2019 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1552 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1553 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1554 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1555 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1557 "FStar.SMTEncoding.Encode.fst"
let _79_2590 = (encode_term_pred None t env ddtok_tm)
in (match (_79_2590) with
| (tok_typing, decls3) -> begin
(
# 1559 "FStar.SMTEncoding.Encode.fst"
let _79_2597 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_79_2597) with
| (vars', guards', env'', decls_formals, _79_2596) -> begin
(
# 1560 "FStar.SMTEncoding.Encode.fst"
let _79_2602 = (
# 1561 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1562 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_79_2602) with
| (ty_pred', decls_pred) -> begin
(
# 1564 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1565 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _79_2606 -> begin
(let _164_2021 = (let _164_2020 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _164_2020))
in (_164_2021)::[])
end)
in (
# 1569 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _79_2609 -> (match (()) with
| () -> begin
(
# 1570 "FStar.SMTEncoding.Encode.fst"
let _79_2612 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_79_2612) with
| (head, args) -> begin
(match ((let _164_2024 = (FStar_Syntax_Subst.compress head)
in _164_2024.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(
# 1574 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (
# 1575 "FStar.SMTEncoding.Encode.fst"
let _79_2630 = (encode_args args env')
in (match (_79_2630) with
| (encoded_args, arg_decls) -> begin
(
# 1576 "FStar.SMTEncoding.Encode.fst"
let _79_2645 = (FStar_List.fold_left (fun _79_2634 arg -> (match (_79_2634) with
| (env, arg_vars, eqns) -> begin
(
# 1577 "FStar.SMTEncoding.Encode.fst"
let _79_2640 = (let _164_2027 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _164_2027))
in (match (_79_2640) with
| (_79_2637, xv, env) -> begin
(let _164_2029 = (let _164_2028 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_164_2028)::eqns)
in (env, (xv)::arg_vars, _164_2029))
end))
end)) (env', [], []) encoded_args)
in (match (_79_2645) with
| (_79_2642, arg_vars, eqns) -> begin
(
# 1579 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1580 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1581 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1582 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1583 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1584 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1585 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _164_2036 = (let _164_2035 = (let _164_2034 = (let _164_2033 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _164_2032 = (let _164_2031 = (let _164_2030 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _164_2030))
in (FStar_SMTEncoding_Term.mkImp _164_2031))
in (((ty_pred)::[])::[], _164_2033, _164_2032)))
in (FStar_SMTEncoding_Term.mkForall _164_2034))
in (_164_2035, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_164_2036))
in (
# 1590 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1592 "FStar.SMTEncoding.Encode.fst"
let x = (let _164_2037 = (varops.fresh "x")
in (_164_2037, FStar_SMTEncoding_Term.Term_sort))
in (
# 1593 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _164_2047 = (let _164_2046 = (let _164_2045 = (let _164_2044 = (let _164_2039 = (let _164_2038 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_164_2038)::[])
in (_164_2039)::[])
in (let _164_2043 = (let _164_2042 = (let _164_2041 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _164_2040 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_164_2041, _164_2040)))
in (FStar_SMTEncoding_Term.mkImp _164_2042))
in (_164_2044, (x)::[], _164_2043)))
in (FStar_SMTEncoding_Term.mkForall _164_2045))
in (_164_2046, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_164_2047))))
end else begin
(
# 1596 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _164_2050 = (let _164_2049 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _164_2049 dapp))
in (_164_2050)::[])
end
| _79_2659 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _164_2057 = (let _164_2056 = (let _164_2055 = (let _164_2054 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _164_2053 = (let _164_2052 = (let _164_2051 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _164_2051))
in (FStar_SMTEncoding_Term.mkImp _164_2052))
in (((ty_pred)::[])::[], _164_2054, _164_2053)))
in (FStar_SMTEncoding_Term.mkForall _164_2055))
in (_164_2056, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_164_2057)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _79_2663 -> begin
(
# 1604 "FStar.SMTEncoding.Encode.fst"
let _79_2664 = (let _164_2060 = (let _164_2059 = (FStar_Syntax_Print.lid_to_string d)
in (let _164_2058 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _164_2059 _164_2058)))
in (FStar_TypeChecker_Errors.warn drange _164_2060))
in ([], []))
end)
end))
end))
in (
# 1607 "FStar.SMTEncoding.Encode.fst"
let _79_2668 = (encode_elim ())
in (match (_79_2668) with
| (decls2, elim) -> begin
(
# 1608 "FStar.SMTEncoding.Encode.fst"
let g = (let _164_2085 = (let _164_2084 = (let _164_2069 = (let _164_2068 = (let _164_2067 = (let _164_2066 = (let _164_2065 = (let _164_2064 = (let _164_2063 = (let _164_2062 = (let _164_2061 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _164_2061))
in Some (_164_2062))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _164_2063))
in FStar_SMTEncoding_Term.DeclFun (_164_2064))
in (_164_2065)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _164_2066))
in (FStar_List.append _164_2067 proxy_fresh))
in (FStar_List.append _164_2068 decls_formals))
in (FStar_List.append _164_2069 decls_pred))
in (let _164_2083 = (let _164_2082 = (let _164_2081 = (let _164_2073 = (let _164_2072 = (let _164_2071 = (let _164_2070 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _164_2070))
in (FStar_SMTEncoding_Term.mkForall _164_2071))
in (_164_2072, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_164_2073))
in (let _164_2080 = (let _164_2079 = (let _164_2078 = (let _164_2077 = (let _164_2076 = (let _164_2075 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _164_2074 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _164_2075, _164_2074)))
in (FStar_SMTEncoding_Term.mkForall _164_2076))
in (_164_2077, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_164_2078))
in (_164_2079)::[])
in (_164_2081)::_164_2080))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_164_2082)
in (FStar_List.append _164_2084 _164_2083)))
in (FStar_List.append _164_2085 elim))
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
# 1626 "FStar.SMTEncoding.Encode.fst"
let _79_2677 = (encode_free_var env x t t_norm [])
in (match (_79_2677) with
| (decls, env) -> begin
(
# 1627 "FStar.SMTEncoding.Encode.fst"
let _79_2682 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_79_2682) with
| (n, x', _79_2681) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _79_2686) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (
# 1633 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1634 "FStar.SMTEncoding.Encode.fst"
let _79_2695 = (encode_function_type_as_formula None None t env)
in (match (_79_2695) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (
# 1638 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _164_2098 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _164_2098)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1641 "FStar.SMTEncoding.Encode.fst"
let _79_2705 = (new_term_constant_and_tok_from_lid env lid)
in (match (_79_2705) with
| (vname, vtok, env) -> begin
(
# 1642 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _164_2099 = (FStar_Syntax_Subst.compress t_norm)
in _164_2099.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _79_2708) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _79_2711 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _79_2714 -> begin
[]
end)
in (
# 1645 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1646 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1649 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1650 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1651 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1653 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1654 "FStar.SMTEncoding.Encode.fst"
let _79_2729 = (
# 1655 "FStar.SMTEncoding.Encode.fst"
let _79_2724 = (curried_arrow_formals_comp t_norm)
in (match (_79_2724) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _164_2101 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _164_2101))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_79_2729) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1659 "FStar.SMTEncoding.Encode.fst"
let _79_2733 = (new_term_constant_and_tok_from_lid env lid)
in (match (_79_2733) with
| (vname, vtok, env) -> begin
(
# 1660 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _79_2736 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1663 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _79_20 -> (match (_79_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1665 "FStar.SMTEncoding.Encode.fst"
let _79_2752 = (FStar_Util.prefix vars)
in (match (_79_2752) with
| (_79_2747, (xxsym, _79_2750)) -> begin
(
# 1666 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _164_2118 = (let _164_2117 = (let _164_2116 = (let _164_2115 = (let _164_2114 = (let _164_2113 = (let _164_2112 = (let _164_2111 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _164_2111))
in (vapp, _164_2112))
in (FStar_SMTEncoding_Term.mkEq _164_2113))
in (((vapp)::[])::[], vars, _164_2114))
in (FStar_SMTEncoding_Term.mkForall _164_2115))
in (_164_2116, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_164_2117))
in (_164_2118)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1671 "FStar.SMTEncoding.Encode.fst"
let _79_2764 = (FStar_Util.prefix vars)
in (match (_79_2764) with
| (_79_2759, (xxsym, _79_2762)) -> begin
(
# 1672 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1673 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1674 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _164_2120 = (let _164_2119 = (mk_term_projector_name d f)
in (_164_2119, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _164_2120))
in (let _164_2125 = (let _164_2124 = (let _164_2123 = (let _164_2122 = (let _164_2121 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _164_2121))
in (FStar_SMTEncoding_Term.mkForall _164_2122))
in (_164_2123, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_164_2124))
in (_164_2125)::[]))))
end))
end
| _79_2769 -> begin
[]
end)))))
in (
# 1678 "FStar.SMTEncoding.Encode.fst"
let _79_2776 = (encode_binders None formals env)
in (match (_79_2776) with
| (vars, guards, env', decls1, _79_2775) -> begin
(
# 1679 "FStar.SMTEncoding.Encode.fst"
let _79_2785 = (match (pre_opt) with
| None -> begin
(let _164_2126 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_164_2126, decls1))
end
| Some (p) -> begin
(
# 1681 "FStar.SMTEncoding.Encode.fst"
let _79_2782 = (encode_formula p env')
in (match (_79_2782) with
| (g, ds) -> begin
(let _164_2127 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_164_2127, (FStar_List.append decls1 ds)))
end))
end)
in (match (_79_2785) with
| (guard, decls1) -> begin
(
# 1682 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1684 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _164_2129 = (let _164_2128 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _164_2128))
in (FStar_SMTEncoding_Term.mkApp _164_2129))
in (
# 1685 "FStar.SMTEncoding.Encode.fst"
let _79_2809 = (
# 1686 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _164_2132 = (let _164_2131 = (FStar_All.pipe_right formals (FStar_List.map (fun _79_2788 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _164_2131, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_164_2132))
in (
# 1687 "FStar.SMTEncoding.Encode.fst"
let _79_2796 = (
# 1688 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1688 "FStar.SMTEncoding.Encode.fst"
let _79_2791 = env
in {bindings = _79_2791.bindings; depth = _79_2791.depth; tcenv = _79_2791.tcenv; warn = _79_2791.warn; cache = _79_2791.cache; nolabels = _79_2791.nolabels; use_zfuel_name = _79_2791.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_79_2796) with
| (tok_typing, decls2) -> begin
(
# 1692 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1693 "FStar.SMTEncoding.Encode.fst"
let _79_2806 = (match (formals) with
| [] -> begin
(let _164_2136 = (let _164_2135 = (let _164_2134 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _164_2133 -> Some (_164_2133)) _164_2134))
in (push_free_var env lid vname _164_2135))
in ((FStar_List.append decls2 ((tok_typing)::[])), _164_2136))
end
| _79_2800 -> begin
(
# 1696 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1697 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _164_2137 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _164_2137))
in (
# 1698 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _164_2141 = (let _164_2140 = (let _164_2139 = (let _164_2138 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _164_2138))
in (FStar_SMTEncoding_Term.mkForall _164_2139))
in (_164_2140, Some ("Name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_164_2141))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_79_2806) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_79_2809) with
| (decls2, env) -> begin
(
# 1701 "FStar.SMTEncoding.Encode.fst"
let _79_2817 = (
# 1702 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1703 "FStar.SMTEncoding.Encode.fst"
let _79_2813 = (encode_term res_t env')
in (match (_79_2813) with
| (encoded_res_t, decls) -> begin
(let _164_2142 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _164_2142, decls))
end)))
in (match (_79_2817) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1705 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _164_2146 = (let _164_2145 = (let _164_2144 = (let _164_2143 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _164_2143))
in (FStar_SMTEncoding_Term.mkForall _164_2144))
in (_164_2145, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_164_2146))
in (
# 1706 "FStar.SMTEncoding.Encode.fst"
let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _164_2152 = (let _164_2149 = (let _164_2148 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _164_2147 = (varops.next_id ())
in (vname, _164_2148, FStar_SMTEncoding_Term.Term_sort, _164_2147)))
in (FStar_SMTEncoding_Term.fresh_constructor _164_2149))
in (let _164_2151 = (let _164_2150 = (pretype_axiom vapp vars)
in (_164_2150)::[])
in (_164_2152)::_164_2151))
end else begin
[]
end
in (
# 1711 "FStar.SMTEncoding.Encode.fst"
let g = (let _164_2154 = (let _164_2153 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_164_2153)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _164_2154))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _79_2825 se -> (match (_79_2825) with
| (g, env) -> begin
(
# 1717 "FStar.SMTEncoding.Encode.fst"
let _79_2829 = (encode_sigelt env se)
in (match (_79_2829) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1718 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1745 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _79_2836 -> (match (_79_2836) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_79_2838) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1750 "FStar.SMTEncoding.Encode.fst"
let _79_2845 = (new_term_constant env x)
in (match (_79_2845) with
| (xxsym, xx, env') -> begin
(
# 1751 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1752 "FStar.SMTEncoding.Encode.fst"
let _79_2847 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _164_2169 = (FStar_Syntax_Print.bv_to_string x)
in (let _164_2168 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _164_2167 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _164_2169 _164_2168 _164_2167))))
end else begin
()
end
in (
# 1754 "FStar.SMTEncoding.Encode.fst"
let _79_2851 = (encode_term_pred None t1 env xx)
in (match (_79_2851) with
| (t, decls') -> begin
(
# 1755 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _164_2173 = (let _164_2172 = (FStar_Syntax_Print.bv_to_string x)
in (let _164_2171 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _164_2170 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _164_2172 _164_2171 _164_2170))))
in Some (_164_2173))
end else begin
None
end
in (
# 1759 "FStar.SMTEncoding.Encode.fst"
let g = (let _164_2178 = (let _164_2177 = (let _164_2176 = (let _164_2175 = (FStar_All.pipe_left (fun _164_2174 -> Some (_164_2174)) (Prims.strcat "Encoding " xxsym))
in (t, _164_2175))
in FStar_SMTEncoding_Term.Assume (_164_2176))
in (_164_2177)::[])
in (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') _164_2178))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_79_2856, t)) -> begin
(
# 1765 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1766 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (
# 1768 "FStar.SMTEncoding.Encode.fst"
let _79_2865 = (encode_free_var env fv t t_norm [])
in (match (_79_2865) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1773 "FStar.SMTEncoding.Encode.fst"
let _79_2879 = (encode_sigelt env se)
in (match (_79_2879) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1776 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1779 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _79_2886 -> (match (_79_2886) with
| (l, _79_2883, _79_2885) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1780 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _79_2893 -> (match (_79_2893) with
| (l, _79_2890, _79_2892) -> begin
(let _164_2186 = (FStar_All.pipe_left (fun _164_2182 -> FStar_SMTEncoding_Term.Echo (_164_2182)) (Prims.fst l))
in (let _164_2185 = (let _164_2184 = (let _164_2183 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_164_2183))
in (_164_2184)::[])
in (_164_2186)::_164_2185))
end))))
in (prefix, suffix))))

# 1781 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1784 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _164_2191 = (let _164_2190 = (let _164_2189 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _164_2189; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_164_2190)::[])
in (FStar_ST.op_Colon_Equals last_env _164_2191)))

# 1787 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_79_2899 -> begin
(
# 1790 "FStar.SMTEncoding.Encode.fst"
let _79_2902 = e
in {bindings = _79_2902.bindings; depth = _79_2902.depth; tcenv = tcenv; warn = _79_2902.warn; cache = _79_2902.cache; nolabels = _79_2902.nolabels; use_zfuel_name = _79_2902.use_zfuel_name; encode_non_total_function_typ = _79_2902.encode_non_total_function_typ})
end))

# 1790 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _79_2908::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1793 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _79_2910 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1797 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1798 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1798 "FStar.SMTEncoding.Encode.fst"
let _79_2916 = hd
in {bindings = _79_2916.bindings; depth = _79_2916.depth; tcenv = _79_2916.tcenv; warn = _79_2916.warn; cache = refs; nolabels = _79_2916.nolabels; use_zfuel_name = _79_2916.use_zfuel_name; encode_non_total_function_typ = _79_2916.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1799 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _79_2919 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _79_2923::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1802 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _79_2925 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1803 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _79_2926 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1804 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _79_2927 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_79_2930::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _79_2935 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1808 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1812 "FStar.SMTEncoding.Encode.fst"
let _79_2937 = (init_env tcenv)
in (
# 1813 "FStar.SMTEncoding.Encode.fst"
let _79_2939 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1814 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1816 "FStar.SMTEncoding.Encode.fst"
let _79_2942 = (push_env ())
in (
# 1817 "FStar.SMTEncoding.Encode.fst"
let _79_2944 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1818 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1820 "FStar.SMTEncoding.Encode.fst"
let _79_2947 = (let _164_2212 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _164_2212))
in (
# 1821 "FStar.SMTEncoding.Encode.fst"
let _79_2949 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1822 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1824 "FStar.SMTEncoding.Encode.fst"
let _79_2952 = (mark_env ())
in (
# 1825 "FStar.SMTEncoding.Encode.fst"
let _79_2954 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1826 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1828 "FStar.SMTEncoding.Encode.fst"
let _79_2957 = (reset_mark_env ())
in (
# 1829 "FStar.SMTEncoding.Encode.fst"
let _79_2959 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1830 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1832 "FStar.SMTEncoding.Encode.fst"
let _79_2962 = (commit_mark_env ())
in (
# 1833 "FStar.SMTEncoding.Encode.fst"
let _79_2964 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1834 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1836 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _164_2228 = (let _164_2227 = (let _164_2226 = (let _164_2225 = (let _164_2224 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _164_2224 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _164_2225 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _164_2226))
in FStar_SMTEncoding_Term.Caption (_164_2227))
in (_164_2228)::decls)
end else begin
decls
end)
in (
# 1840 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1841 "FStar.SMTEncoding.Encode.fst"
let _79_2973 = (encode_sigelt env se)
in (match (_79_2973) with
| (decls, env) -> begin
(
# 1842 "FStar.SMTEncoding.Encode.fst"
let _79_2974 = (set_env env)
in (let _164_2229 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _164_2229)))
end)))))

# 1843 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1846 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1847 "FStar.SMTEncoding.Encode.fst"
let _79_2979 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _164_2234 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _164_2234))
end else begin
()
end
in (
# 1849 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1850 "FStar.SMTEncoding.Encode.fst"
let _79_2986 = (encode_signature (
# 1850 "FStar.SMTEncoding.Encode.fst"
let _79_2982 = env
in {bindings = _79_2982.bindings; depth = _79_2982.depth; tcenv = _79_2982.tcenv; warn = false; cache = _79_2982.cache; nolabels = _79_2982.nolabels; use_zfuel_name = _79_2982.use_zfuel_name; encode_non_total_function_typ = _79_2982.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_79_2986) with
| (decls, env) -> begin
(
# 1851 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1853 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1856 "FStar.SMTEncoding.Encode.fst"
let _79_2992 = (set_env (
# 1856 "FStar.SMTEncoding.Encode.fst"
let _79_2990 = env
in {bindings = _79_2990.bindings; depth = _79_2990.depth; tcenv = _79_2990.tcenv; warn = true; cache = _79_2990.cache; nolabels = _79_2990.nolabels; use_zfuel_name = _79_2990.use_zfuel_name; encode_non_total_function_typ = _79_2990.encode_non_total_function_typ}))
in (
# 1857 "FStar.SMTEncoding.Encode.fst"
let _79_2994 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1858 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1859 "FStar.SMTEncoding.Encode.fst"
let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (
# 1862 "FStar.SMTEncoding.Encode.fst"
let _79_3000 = (let _164_2253 = (let _164_2252 = (let _164_2251 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _164_2251))
in (FStar_Util.format1 "Starting query at %s" _164_2252))
in (push _164_2253))
in (
# 1863 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _79_3003 -> (match (()) with
| () -> begin
(let _164_2258 = (let _164_2257 = (let _164_2256 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _164_2256))
in (FStar_Util.format1 "Ending query at %s" _164_2257))
in (pop _164_2258))
end))
in (
# 1864 "FStar.SMTEncoding.Encode.fst"
let _79_3057 = (
# 1865 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1866 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1867 "FStar.SMTEncoding.Encode.fst"
let _79_3027 = (
# 1868 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1870 "FStar.SMTEncoding.Encode.fst"
let _79_3016 = (aux rest)
in (match (_79_3016) with
| (out, rest) -> begin
(
# 1871 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _164_2264 = (let _164_2263 = (FStar_Syntax_Syntax.mk_binder (
# 1872 "FStar.SMTEncoding.Encode.fst"
let _79_3018 = x
in {FStar_Syntax_Syntax.ppname = _79_3018.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _79_3018.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_164_2263)::out)
in (_164_2264, rest)))
end))
end
| _79_3021 -> begin
([], bindings)
end))
in (
# 1874 "FStar.SMTEncoding.Encode.fst"
let _79_3024 = (aux bindings)
in (match (_79_3024) with
| (closing, bindings) -> begin
(let _164_2265 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_164_2265, bindings))
end)))
in (match (_79_3027) with
| (q, bindings) -> begin
(
# 1876 "FStar.SMTEncoding.Encode.fst"
let _79_3036 = (let _164_2267 = (FStar_List.filter (fun _79_21 -> (match (_79_21) with
| FStar_TypeChecker_Env.Binding_sig (_79_3030) -> begin
false
end
| _79_3033 -> begin
true
end)) bindings)
in (encode_env_bindings env _164_2267))
in (match (_79_3036) with
| (env_decls, env) -> begin
(
# 1877 "FStar.SMTEncoding.Encode.fst"
let _79_3037 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _164_2268 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _164_2268))
end else begin
()
end
in (
# 1880 "FStar.SMTEncoding.Encode.fst"
let _79_3041 = (encode_formula q env)
in (match (_79_3041) with
| (phi, qdecls) -> begin
(
# 1881 "FStar.SMTEncoding.Encode.fst"
let _79_3046 = (let _164_2269 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _164_2269 phi))
in (match (_79_3046) with
| (phi, labels, _79_3045) -> begin
(
# 1882 "FStar.SMTEncoding.Encode.fst"
let _79_3049 = (encode_labels labels)
in (match (_79_3049) with
| (label_prefix, label_suffix) -> begin
(
# 1883 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1887 "FStar.SMTEncoding.Encode.fst"
let qry = (let _164_2271 = (let _164_2270 = (FStar_SMTEncoding_Term.mkNot phi)
in (_164_2270, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_164_2271))
in (
# 1888 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_79_3057) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _79_3064); FStar_SMTEncoding_Term.hash = _79_3061; FStar_SMTEncoding_Term.freevars = _79_3059}, _79_3069) -> begin
(
# 1891 "FStar.SMTEncoding.Encode.fst"
let _79_3072 = (pop ())
in ())
end
| _79_3075 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1892 "FStar.SMTEncoding.Encode.fst"
let _79_3076 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _79_3080) -> begin
(
# 1894 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1895 "FStar.SMTEncoding.Encode.fst"
let _79_3084 = (FStar_SMTEncoding_ErrorReporting.askZ3_and_report_errors tcenv fresh labels prefix qry suffix)
in (pop ())))
end
| _79_3087 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1899 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1902 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1903 "FStar.SMTEncoding.Encode.fst"
let _79_3091 = (push "query")
in (
# 1904 "FStar.SMTEncoding.Encode.fst"
let _79_3096 = (encode_formula q env)
in (match (_79_3096) with
| (f, _79_3095) -> begin
(
# 1905 "FStar.SMTEncoding.Encode.fst"
let _79_3097 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _79_3101) -> begin
true
end
| _79_3105 -> begin
false
end))
end)))))

# 1908 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1923 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _79_3106 -> ()); FStar_TypeChecker_Env.push = (fun _79_3108 -> ()); FStar_TypeChecker_Env.pop = (fun _79_3110 -> ()); FStar_TypeChecker_Env.mark = (fun _79_3112 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _79_3114 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _79_3116 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _79_3118 _79_3120 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _79_3122 _79_3124 -> ()); FStar_TypeChecker_Env.solve = (fun _79_3126 _79_3128 _79_3130 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _79_3132 _79_3134 -> false); FStar_TypeChecker_Env.finish = (fun _79_3136 -> ()); FStar_TypeChecker_Env.refresh = (fun _79_3137 -> ())}





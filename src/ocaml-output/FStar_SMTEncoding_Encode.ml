
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
let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _172_13 = (let _172_12 = (let _172_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _172_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _172_12))
in Some (_172_13))
end))

# 42 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 43 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _83_46 = a
in (let _172_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _172_20; FStar_Syntax_Syntax.index = _83_46.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _83_46.FStar_Syntax_Syntax.sort}))
in (let _172_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _172_21))))

# 46 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _83_53 -> (match (()) with
| () -> begin
(let _172_31 = (let _172_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _172_30 lid.FStar_Ident.str))
in (FStar_All.failwith _172_31))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _83_57 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_83_57) with
| (_83_55, t) -> begin
(match ((let _172_32 = (FStar_Syntax_Subst.compress t)
in _172_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _83_65 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_83_65) with
| (binders, _83_64) -> begin
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
| _83_68 -> begin
(fail ())
end)
end))))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _172_38 = (let _172_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _172_37))
in (FStar_All.pipe_left escape _172_38)))

# 58 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _172_44 = (let _172_43 = (mk_term_projector_name lid a)
in (_172_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _172_44)))

# 60 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _172_50 = (let _172_49 = (mk_term_projector_name_by_pos lid i)
in (_172_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _172_50)))

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
let new_scope = (fun _83_92 -> (match (()) with
| () -> begin
(let _172_154 = (FStar_Util.smap_create 100)
in (let _172_153 = (FStar_Util.smap_create 100)
in (_172_154, _172_153)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _172_156 = (let _172_155 = (new_scope ())
in (_172_155)::[])
in (FStar_Util.mk_ref _172_156))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _172_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _172_160 (fun _83_100 -> (match (_83_100) with
| (names, _83_99) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_83_103) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _83_105 = (FStar_Util.incr ctr)
in (let _172_162 = (let _172_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_161))
in (Prims.strcat (Prims.strcat y "__") _172_162)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _172_164 = (let _172_163 = (FStar_ST.read scopes)
in (FStar_List.hd _172_163))
in (FStar_All.pipe_left Prims.fst _172_164))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _83_109 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _172_171 = (let _172_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _172_169 "__"))
in (let _172_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _172_171 _172_170))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _83_117 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _83_118 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _172_179 = (let _172_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _172_178))
in (FStar_Util.format2 "%s_%s" pfx _172_179)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _172_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _172_183 (fun _83_127 -> (match (_83_127) with
| (_83_125, strings) -> begin
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
let f = (let _172_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _172_184))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _172_186 = (let _172_185 = (FStar_ST.read scopes)
in (FStar_List.hd _172_185))
in (FStar_All.pipe_left Prims.snd _172_186))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _83_134 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _83_137 -> (match (()) with
| () -> begin
(let _172_191 = (let _172_190 = (new_scope ())
in (let _172_189 = (FStar_ST.read scopes)
in (_172_190)::_172_189))
in (FStar_ST.op_Colon_Equals scopes _172_191))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _83_139 -> (match (()) with
| () -> begin
(let _172_195 = (let _172_194 = (FStar_ST.read scopes)
in (FStar_List.tl _172_194))
in (FStar_ST.op_Colon_Equals scopes _172_195))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _83_141 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _83_143 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _83_145 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _83_158 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _83_163 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _83_166 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 122 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _83_168 = x
in (let _172_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _172_210; FStar_Syntax_Syntax.index = _83_168.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _83_168.FStar_Syntax_Syntax.sort})))

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
| Binding_var (_83_172) -> begin
_83_172
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_83_175) -> begin
_83_175
end))

# 131 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 132 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 142 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _172_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _83_2 -> (match (_83_2) with
| Binding_var (x, _83_190) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _83_195, _83_197, _83_199) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _172_268 (FStar_String.concat ", "))))

# 147 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_172_278))
end else begin
None
end)

# 154 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _172_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _172_283))))

# 158 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _172_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _172_288))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _83_213 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _83_213.tcenv; warn = _83_213.warn; cache = _83_213.cache; nolabels = _83_213.nolabels; use_zfuel_name = _83_213.use_zfuel_name; encode_non_total_function_typ = _83_213.encode_non_total_function_typ})))))

# 162 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _83_219 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _83_219.depth; tcenv = _83_219.tcenv; warn = _83_219.warn; cache = _83_219.cache; nolabels = _83_219.nolabels; use_zfuel_name = _83_219.use_zfuel_name; encode_non_total_function_typ = _83_219.encode_non_total_function_typ})))))

# 166 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _83_224 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _83_224.depth; tcenv = _83_224.tcenv; warn = _83_224.warn; cache = _83_224.cache; nolabels = _83_224.nolabels; use_zfuel_name = _83_224.use_zfuel_name; encode_non_total_function_typ = _83_224.encode_non_total_function_typ}))

# 168 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _83_3 -> (match (_83_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _83_234 -> begin
None
end)))) with
| None -> begin
(let _172_305 = (let _172_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _172_304))
in (FStar_All.failwith _172_305))
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
in (let _172_316 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _83_244 = env
in (let _172_315 = (let _172_314 = (let _172_313 = (let _172_312 = (let _172_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _172_310 -> Some (_172_310)) _172_311))
in (x, fname, _172_312, None))
in Binding_fvar (_172_313))
in (_172_314)::env.bindings)
in {bindings = _172_315; depth = _83_244.depth; tcenv = _83_244.tcenv; warn = _83_244.warn; cache = _83_244.cache; nolabels = _83_244.nolabels; use_zfuel_name = _83_244.use_zfuel_name; encode_non_total_function_typ = _83_244.encode_non_total_function_typ}))
in (fname, ftok, _172_316)))))

# 179 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _83_4 -> (match (_83_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _83_256 -> begin
None
end))))

# 181 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _172_327 = (let _172_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _172_326))
in (FStar_All.failwith _172_327))
end
| Some (s) -> begin
s
end))

# 185 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _83_266 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _83_266.depth; tcenv = _83_266.tcenv; warn = _83_266.warn; cache = _83_266.cache; nolabels = _83_266.nolabels; use_zfuel_name = _83_266.use_zfuel_name; encode_non_total_function_typ = _83_266.encode_non_total_function_typ}))

# 187 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _83_275 = (lookup_lid env x)
in (match (_83_275) with
| (t1, t2, _83_274) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _172_344 = (let _172_343 = (let _172_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_172_342)::[])
in (f, _172_343))
in (FStar_SMTEncoding_Term.mkApp _172_344))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _83_277 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _83_277.depth; tcenv = _83_277.tcenv; warn = _83_277.warn; cache = _83_277.cache; nolabels = _83_277.nolabels; use_zfuel_name = _83_277.use_zfuel_name; encode_non_total_function_typ = _83_277.encode_non_total_function_typ}))
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
| _83_290 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_83_294, fuel::[]) -> begin
if (let _172_350 = (let _172_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _172_349 Prims.fst))
in (FStar_Util.starts_with _172_350 "fuel")) then begin
(let _172_353 = (let _172_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _172_352 fuel))
in (FStar_All.pipe_left (fun _172_351 -> Some (_172_351)) _172_353))
end else begin
Some (t)
end
end
| _83_300 -> begin
Some (t)
end)
end
| _83_302 -> begin
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
(let _172_357 = (let _172_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _172_356))
in (FStar_All.failwith _172_357))
end))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _83_315 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_83_315) with
| (x, _83_312, _83_314) -> begin
x
end)))

# 213 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _83_321 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_83_321) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _83_325; FStar_SMTEncoding_Term.freevars = _83_323}) when env.use_zfuel_name -> begin
(g, zf)
end
| _83_333 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _83_343 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 225 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _83_5 -> (match (_83_5) with
| Binding_fvar (_83_348, nm', tok, _83_352) when (nm = nm') -> begin
tok
end
| _83_356 -> begin
None
end))))

# 234 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _83_361 -> (match (_83_361) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _83_363 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _83_366 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_366) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _83_376 -> begin
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
(let _172_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _172_374))
end
| _83_389 -> begin
(let _172_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _172_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _83_392 -> begin
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
(let _172_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_381 FStar_Option.isNone))
end
| _83_431 -> begin
false
end)))

# 269 "FStar.SMTEncoding.Encode.fst"
let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _172_386 = (FStar_Syntax_Util.un_uinst t)
in _172_386.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_83_435) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _172_387 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_387 FStar_Option.isSome))
end
| _83_440 -> begin
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
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _172_400 = (let _172_398 = (FStar_Syntax_Syntax.null_binder t)
in (_172_398)::[])
in (let _172_399 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _172_400 _172_399 None))))

# 284 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _172_407 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _172_407))
end
| s -> begin
(
# 287 "FStar.SMTEncoding.Encode.fst"
let _83_452 = ()
in (let _172_408 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _172_408)))
end)) e)))

# 288 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 290 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _83_6 -> (match (_83_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _83_462 -> begin
false
end))

# 295 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 296 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _83_473; FStar_SMTEncoding_Term.freevars = _83_471}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _83_491) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _83_498 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_83_500, []) -> begin
(
# 307 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _83_506 -> begin
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
(let _172_465 = (let _172_464 = (let _172_463 = (let _172_462 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _172_462))
in (_172_463)::[])
in ("FStar.Char.char", _172_464))
in (FStar_SMTEncoding_Term.mkApp _172_465))
end
| FStar_Const.Const_int (i, None) -> begin
(let _172_466 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _172_466))
end
| FStar_Const.Const_int (i, Some (q)) -> begin
(let _172_470 = (let _172_469 = (let _172_468 = (let _172_467 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _172_467))
in (_172_468)::[])
in ((FStar_Const.string_of_int_qualifier q), _172_469))
in (FStar_SMTEncoding_Term.mkApp _172_470))
end
| FStar_Const.Const_string (bytes, _83_531) -> begin
(let _172_471 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _172_471))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _172_473 = (let _172_472 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _172_472))
in (FStar_All.failwith _172_473))
end))

# 360 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 361 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 362 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_83_545) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_83_548) -> begin
(let _172_482 = (FStar_Syntax_Util.unrefine t)
in (aux true _172_482))
end
| _83_551 -> begin
if norm then begin
(let _172_483 = (whnf env t)
in (aux false _172_483))
end else begin
(let _172_486 = (let _172_485 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _172_484 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _172_485 _172_484)))
in (FStar_All.failwith _172_486))
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
| _83_559 -> begin
(let _172_489 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _172_489))
end)))

# 378 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 385 "FStar.SMTEncoding.Encode.fst"
let _83_563 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_537 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _172_537))
end else begin
()
end
in (
# 387 "FStar.SMTEncoding.Encode.fst"
let _83_591 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _83_570 b -> (match (_83_570) with
| (vars, guards, env, decls, names) -> begin
(
# 388 "FStar.SMTEncoding.Encode.fst"
let _83_585 = (
# 389 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 390 "FStar.SMTEncoding.Encode.fst"
let _83_576 = (gen_term_var env x)
in (match (_83_576) with
| (xxsym, xx, env') -> begin
(
# 391 "FStar.SMTEncoding.Encode.fst"
let _83_579 = (let _172_540 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _172_540 env xx))
in (match (_83_579) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_83_585) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_83_591) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 406 "FStar.SMTEncoding.Encode.fst"
let _83_598 = (encode_term t env)
in (match (_83_598) with
| (t, decls) -> begin
(let _172_545 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_172_545, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 410 "FStar.SMTEncoding.Encode.fst"
let _83_605 = (encode_term t env)
in (match (_83_605) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _172_550 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_172_550, decls))
end
| Some (f) -> begin
(let _172_551 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_172_551, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 418 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 419 "FStar.SMTEncoding.Encode.fst"
let _83_612 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_556 = (FStar_Syntax_Print.tag_of_term t)
in (let _172_555 = (FStar_Syntax_Print.tag_of_term t0)
in (let _172_554 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _172_556 _172_555 _172_554))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _172_561 = (let _172_560 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _172_559 = (FStar_Syntax_Print.tag_of_term t0)
in (let _172_558 = (FStar_Syntax_Print.term_to_string t0)
in (let _172_557 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _172_560 _172_559 _172_558 _172_557)))))
in (FStar_All.failwith _172_561))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _172_563 = (let _172_562 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _172_562))
in (FStar_All.failwith _172_563))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _83_623) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _83_628) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 435 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _172_564 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_172_564, []))
end
| FStar_Syntax_Syntax.Tm_type (_83_637) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _83_641) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _172_565 = (encode_const c)
in (_172_565, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 451 "FStar.SMTEncoding.Encode.fst"
let _83_652 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_652) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 455 "FStar.SMTEncoding.Encode.fst"
let _83_659 = (encode_binders None binders env)
in (match (_83_659) with
| (vars, guards, env', decls, _83_658) -> begin
(
# 456 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _172_566 = (varops.fresh "f")
in (_172_566, FStar_SMTEncoding_Term.Term_sort))
in (
# 457 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 458 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 459 "FStar.SMTEncoding.Encode.fst"
let _83_665 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_83_665) with
| (pre_opt, res_t) -> begin
(
# 460 "FStar.SMTEncoding.Encode.fst"
let _83_668 = (encode_term_pred None res_t env' app)
in (match (_83_668) with
| (res_pred, decls') -> begin
(
# 461 "FStar.SMTEncoding.Encode.fst"
let _83_677 = (match (pre_opt) with
| None -> begin
(let _172_567 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_567, decls))
end
| Some (pre) -> begin
(
# 464 "FStar.SMTEncoding.Encode.fst"
let _83_674 = (encode_formula pre env')
in (match (_83_674) with
| (guard, decls0) -> begin
(let _172_568 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_172_568, (FStar_List.append decls decls0)))
end))
end)
in (match (_83_677) with
| (guards, guard_decls) -> begin
(
# 466 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _172_570 = (let _172_569 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _172_569))
in (FStar_SMTEncoding_Term.mkForall _172_570))
in (
# 471 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _172_572 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _172_572 (FStar_List.filter (fun _83_682 -> (match (_83_682) with
| (x, _83_681) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 472 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _83_688) -> begin
(let _172_575 = (let _172_574 = (let _172_573 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _172_573))
in (FStar_SMTEncoding_Term.mkApp _172_574))
in (_172_575, []))
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
(let _172_576 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_172_576))
end else begin
None
end
in (
# 485 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 487 "FStar.SMTEncoding.Encode.fst"
let t = (let _172_578 = (let _172_577 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _172_577))
in (FStar_SMTEncoding_Term.mkApp _172_578))
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 490 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _172_580 = (let _172_579 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_172_579, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_172_580))
in (
# 492 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 493 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _172_587 = (let _172_586 = (let _172_585 = (let _172_584 = (let _172_583 = (let _172_582 = (let _172_581 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_581))
in (f_has_t, _172_582))
in (FStar_SMTEncoding_Term.mkImp _172_583))
in (((f_has_t)::[])::[], (fsym)::cvars, _172_584))
in (mkForall_fuel _172_585))
in (_172_586, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_172_587))
in (
# 495 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _172_591 = (let _172_590 = (let _172_589 = (let _172_588 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _172_588))
in (FStar_SMTEncoding_Term.mkForall _172_589))
in (_172_590, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_172_591))
in (
# 498 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 499 "FStar.SMTEncoding.Encode.fst"
let _83_704 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
let t_kinding = (let _172_593 = (let _172_592 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_172_592, Some ("Typing for non-total arrows")))
in FStar_SMTEncoding_Term.Assume (_172_593))
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
let t_interp = (let _172_600 = (let _172_599 = (let _172_598 = (let _172_597 = (let _172_596 = (let _172_595 = (let _172_594 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_594))
in (f_has_t, _172_595))
in (FStar_SMTEncoding_Term.mkImp _172_596))
in (((f_has_t)::[])::[], (fsym)::[], _172_597))
in (mkForall_fuel _172_598))
in (_172_599, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_172_600))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_83_715) -> begin
(
# 517 "FStar.SMTEncoding.Encode.fst"
let _83_735 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _83_722; FStar_Syntax_Syntax.pos = _83_720; FStar_Syntax_Syntax.vars = _83_718} -> begin
(
# 519 "FStar.SMTEncoding.Encode.fst"
let _83_730 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_83_730) with
| (b, f) -> begin
(let _172_602 = (let _172_601 = (FStar_List.hd b)
in (Prims.fst _172_601))
in (_172_602, f))
end))
end
| _83_732 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_83_735) with
| (x, f) -> begin
(
# 523 "FStar.SMTEncoding.Encode.fst"
let _83_738 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_83_738) with
| (base_t, decls) -> begin
(
# 524 "FStar.SMTEncoding.Encode.fst"
let _83_742 = (gen_term_var env x)
in (match (_83_742) with
| (x, xtm, env') -> begin
(
# 525 "FStar.SMTEncoding.Encode.fst"
let _83_745 = (encode_formula f env')
in (match (_83_745) with
| (refinement, decls') -> begin
(
# 527 "FStar.SMTEncoding.Encode.fst"
let _83_748 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_748) with
| (fsym, fterm) -> begin
(
# 529 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _172_604 = (let _172_603 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_172_603, refinement))
in (FStar_SMTEncoding_Term.mkAnd _172_604))
in (
# 531 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _172_606 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _172_606 (FStar_List.filter (fun _83_753 -> (match (_83_753) with
| (y, _83_752) -> begin
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
| Some (t, _83_760, _83_762) -> begin
(let _172_609 = (let _172_608 = (let _172_607 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _172_607))
in (FStar_SMTEncoding_Term.mkApp _172_608))
in (_172_609, []))
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
let t = (let _172_611 = (let _172_610 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _172_610))
in (FStar_SMTEncoding_Term.mkApp _172_611))
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
let assumption = (let _172_613 = (let _172_612 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _172_612))
in (FStar_SMTEncoding_Term.mkForall _172_613))
in (
# 552 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _172_620 = (let _172_619 = (let _172_618 = (let _172_617 = (let _172_616 = (let _172_615 = (let _172_614 = (FStar_Syntax_Print.term_to_string t0)
in Some (_172_614))
in (assumption, _172_615))
in FStar_SMTEncoding_Term.Assume (_172_616))
in (_172_617)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, Some ("refinement kinding"))))::_172_618)
in (tdecl)::_172_619)
in (FStar_List.append (FStar_List.append decls decls') _172_620))
in (
# 557 "FStar.SMTEncoding.Encode.fst"
let _83_775 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
let ttm = (let _172_621 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _172_621))
in (
# 563 "FStar.SMTEncoding.Encode.fst"
let _83_784 = (encode_term_pred None k env ttm)
in (match (_83_784) with
| (t_has_k, decls) -> begin
(
# 564 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, Some ("Uvar typing")))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_83_787) -> begin
(
# 568 "FStar.SMTEncoding.Encode.fst"
let _83_791 = (FStar_Syntax_Util.head_and_args t0)
in (match (_83_791) with
| (head, args_e) -> begin
(match ((let _172_623 = (let _172_622 = (FStar_Syntax_Subst.compress head)
in _172_622.FStar_Syntax_Syntax.n)
in (_172_623, args_e))) with
| (_83_793, _83_795) when (head_redex env head) -> begin
(let _172_624 = (whnf env t)
in (encode_term _172_624 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), _::(v1, _)::(v2, _)::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(
# 575 "FStar.SMTEncoding.Encode.fst"
let _83_835 = (encode_term v1 env)
in (match (_83_835) with
| (v1, decls1) -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let _83_838 = (encode_term v2 env)
in (match (_83_838) with
| (v2, decls2) -> begin
(let _172_625 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_172_625, (FStar_List.append decls1 decls2)))
end))
end))
end
| _83_840 -> begin
(
# 580 "FStar.SMTEncoding.Encode.fst"
let _83_843 = (encode_args args_e env)
in (match (_83_843) with
| (args, decls) -> begin
(
# 582 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 583 "FStar.SMTEncoding.Encode.fst"
let _83_848 = (encode_term head env)
in (match (_83_848) with
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
let _83_857 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_83_857) with
| (formals, rest) -> begin
(
# 589 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _83_861 _83_865 -> (match ((_83_861, _83_865)) with
| ((bv, _83_860), (a, _83_864)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 590 "FStar.SMTEncoding.Encode.fst"
let ty = (let _172_630 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _172_630 (FStar_Syntax_Subst.subst subst)))
in (
# 591 "FStar.SMTEncoding.Encode.fst"
let _83_870 = (encode_term_pred None ty env app_tm)
in (match (_83_870) with
| (has_type, decls'') -> begin
(
# 592 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 593 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _172_632 = (let _172_631 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_172_631, Some ("Partial app typing")))
in FStar_SMTEncoding_Term.Assume (_172_632))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 597 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 598 "FStar.SMTEncoding.Encode.fst"
let _83_877 = (lookup_free_var_sym env fv)
in (match (_83_877) with
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
(let _172_636 = (let _172_635 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _172_635 Prims.snd))
in Some (_172_636))
end
| FStar_Syntax_Syntax.Tm_ascribed (_83_909, FStar_Util.Inl (t), _83_913) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_83_917, FStar_Util.Inr (c), _83_921) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _83_925 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 616 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _172_637 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _172_637))
in (
# 617 "FStar.SMTEncoding.Encode.fst"
let _83_933 = (curried_arrow_formals_comp head_type)
in (match (_83_933) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _83_949 -> begin
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
let _83_958 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_83_958) with
| (bs, body, opening) -> begin
(
# 632 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _83_960 -> (match (()) with
| () -> begin
(
# 633 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 634 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, Some ("Imprecise function encoding")))
in (let _172_640 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_172_640, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 639 "FStar.SMTEncoding.Encode.fst"
let _83_964 = (let _172_642 = (let _172_641 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _172_641))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _172_642))
in (fallback ()))
end
| Some (lc) -> begin
if (let _172_643 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _172_643)) then begin
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
let _83_976 = (encode_binders None bs env)
in (match (_83_976) with
| (vars, guards, envbody, decls, _83_975) -> begin
(
# 650 "FStar.SMTEncoding.Encode.fst"
let _83_979 = (encode_term body envbody)
in (match (_83_979) with
| (body, decls') -> begin
(
# 651 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _172_647 = (let _172_646 = (let _172_645 = (let _172_644 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_644, body))
in (FStar_SMTEncoding_Term.mkImp _172_645))
in ([], vars, _172_646))
in (FStar_SMTEncoding_Term.mkForall _172_647))
in (
# 652 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 653 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _83_985, _83_987) -> begin
(let _172_650 = (let _172_649 = (let _172_648 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _172_648))
in (FStar_SMTEncoding_Term.mkApp _172_649))
in (_172_650, []))
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
let f = (let _172_652 = (let _172_651 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _172_651))
in (FStar_SMTEncoding_Term.mkApp _172_652))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 667 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let _83_1002 = (encode_term_pred None tfun env f)
in (match (_83_1002) with
| (f_has_t, decls'') -> begin
(
# 669 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _172_654 = (let _172_653 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_172_653, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_172_654))
in (
# 671 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _172_661 = (let _172_660 = (let _172_659 = (let _172_658 = (let _172_657 = (let _172_656 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _172_655 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_172_656, _172_655)))
in (FStar_SMTEncoding_Term.mkImp _172_657))
in (((app)::[])::[], (FStar_List.append vars cvars), _172_658))
in (FStar_SMTEncoding_Term.mkForall _172_659))
in (_172_660, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_172_661))
in (
# 673 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 674 "FStar.SMTEncoding.Encode.fst"
let _83_1006 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_83_1009, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_83_1021); FStar_Syntax_Syntax.lbunivs = _83_1019; FStar_Syntax_Syntax.lbtyp = _83_1017; FStar_Syntax_Syntax.lbeff = _83_1015; FStar_Syntax_Syntax.lbdef = _83_1013}::_83_1011), _83_1027) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1036; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1033; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_83_1046) -> begin
(
# 687 "FStar.SMTEncoding.Encode.fst"
let _83_1048 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 688 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 689 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _172_662 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_172_662, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 696 "FStar.SMTEncoding.Encode.fst"
let _83_1064 = (encode_term e1 env)
in (match (_83_1064) with
| (ee1, decls1) -> begin
(
# 697 "FStar.SMTEncoding.Encode.fst"
let _83_1067 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_83_1067) with
| (xs, e2) -> begin
(
# 698 "FStar.SMTEncoding.Encode.fst"
let _83_1071 = (FStar_List.hd xs)
in (match (_83_1071) with
| (x, _83_1070) -> begin
(
# 699 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 700 "FStar.SMTEncoding.Encode.fst"
let _83_1075 = (encode_body e2 env')
in (match (_83_1075) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 704 "FStar.SMTEncoding.Encode.fst"
let _83_1083 = (encode_term e env)
in (match (_83_1083) with
| (scr, decls) -> begin
(
# 705 "FStar.SMTEncoding.Encode.fst"
let _83_1120 = (FStar_List.fold_right (fun b _83_1087 -> (match (_83_1087) with
| (else_case, decls) -> begin
(
# 706 "FStar.SMTEncoding.Encode.fst"
let _83_1091 = (FStar_Syntax_Subst.open_branch b)
in (match (_83_1091) with
| (p, w, br) -> begin
(
# 707 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _83_1095 _83_1098 -> (match ((_83_1095, _83_1098)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 709 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 710 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 711 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _83_1104 -> (match (_83_1104) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 712 "FStar.SMTEncoding.Encode.fst"
let _83_1114 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 715 "FStar.SMTEncoding.Encode.fst"
let _83_1111 = (encode_term w env)
in (match (_83_1111) with
| (w, decls2) -> begin
(let _172_696 = (let _172_695 = (let _172_694 = (let _172_693 = (let _172_692 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _172_692))
in (FStar_SMTEncoding_Term.mkEq _172_693))
in (guard, _172_694))
in (FStar_SMTEncoding_Term.mkAnd _172_695))
in (_172_696, decls2))
end))
end)
in (match (_83_1114) with
| (guard, decls2) -> begin
(
# 717 "FStar.SMTEncoding.Encode.fst"
let _83_1117 = (encode_br br env)
in (match (_83_1117) with
| (br, decls3) -> begin
(let _172_697 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_172_697, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_83_1120) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _83_1126 -> begin
(let _172_700 = (encode_one_pat env pat)
in (_172_700)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 731 "FStar.SMTEncoding.Encode.fst"
let _83_1129 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_703 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _172_703))
end else begin
()
end
in (
# 732 "FStar.SMTEncoding.Encode.fst"
let _83_1133 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_83_1133) with
| (vars, pat_term) -> begin
(
# 734 "FStar.SMTEncoding.Encode.fst"
let _83_1145 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _83_1136 v -> (match (_83_1136) with
| (env, vars) -> begin
(
# 735 "FStar.SMTEncoding.Encode.fst"
let _83_1142 = (gen_term_var env v)
in (match (_83_1142) with
| (xx, _83_1140, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_83_1145) with
| (env, vars) -> begin
(
# 738 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_83_1150) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _172_711 = (let _172_710 = (encode_const c)
in (scrutinee, _172_710))
in (FStar_SMTEncoding_Term.mkEq _172_711))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(
# 746 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (
# 747 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1172 -> (match (_83_1172) with
| (arg, _83_1171) -> begin
(
# 748 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _172_714 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _172_714)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 752 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_83_1179) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_83_1189) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _172_722 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _83_1199 -> (match (_83_1199) with
| (arg, _83_1198) -> begin
(
# 764 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _172_721 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _172_721)))
end))))
in (FStar_All.pipe_right _172_722 FStar_List.flatten))
end))
in (
# 768 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _83_1202 -> (match (()) with
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
let _83_1218 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _83_1208 _83_1212 -> (match ((_83_1208, _83_1212)) with
| ((tms, decls), (t, _83_1211)) -> begin
(
# 781 "FStar.SMTEncoding.Encode.fst"
let _83_1215 = (encode_term t env)
in (match (_83_1215) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_83_1218) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 787 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let _83_1227 = (let _172_735 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _172_735))
in (match (_83_1227) with
| (head, args) -> begin
(match ((let _172_737 = (let _172_736 = (FStar_Syntax_Util.un_uinst head)
in _172_736.FStar_Syntax_Syntax.n)
in (_172_737, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1231) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1244::(hd, _83_1241)::(tl, _83_1237)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _172_738 = (list_elements tl)
in (hd)::_172_738)
end
| _83_1248 -> begin
(
# 793 "FStar.SMTEncoding.Encode.fst"
let _83_1249 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 795 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 796 "FStar.SMTEncoding.Encode.fst"
let _83_1255 = (let _172_741 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _172_741 FStar_Syntax_Util.head_and_args))
in (match (_83_1255) with
| (head, args) -> begin
(match ((let _172_743 = (let _172_742 = (FStar_Syntax_Util.un_uinst head)
in _172_742.FStar_Syntax_Syntax.n)
in (_172_743, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_83_1263, _83_1265)::(e, _83_1260)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _83_1273)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _83_1278 -> begin
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
let _83_1286 = (let _172_748 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _172_748 FStar_Syntax_Util.head_and_args))
in (match (_83_1286) with
| (head, args) -> begin
(match ((let _172_750 = (let _172_749 = (FStar_Syntax_Util.un_uinst head)
in _172_749.FStar_Syntax_Syntax.n)
in (_172_750, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _83_1291)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _83_1296 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _172_753 = (list_elements e)
in (FStar_All.pipe_right _172_753 (FStar_List.map (fun branch -> (let _172_752 = (list_elements branch)
in (FStar_All.pipe_right _172_752 (FStar_List.map one_pat)))))))
end
| _83_1303 -> begin
(let _172_754 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_172_754)::[])
end)
end
| _83_1305 -> begin
(let _172_755 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_172_755)::[])
end))))
in (
# 819 "FStar.SMTEncoding.Encode.fst"
let _83_1339 = (match ((let _172_756 = (FStar_Syntax_Subst.compress t)
in _172_756.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 821 "FStar.SMTEncoding.Encode.fst"
let _83_1312 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_83_1312) with
| (binders, c) -> begin
(
# 822 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _83_1324)::(post, _83_1320)::(pats, _83_1316)::[] -> begin
(
# 825 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _172_757 = (lemma_pats pats')
in (binders, pre, post, _172_757)))
end
| _83_1332 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _83_1334 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_83_1339) with
| (binders, pre, post, patterns) -> begin
(
# 833 "FStar.SMTEncoding.Encode.fst"
let _83_1346 = (encode_binders None binders env)
in (match (_83_1346) with
| (vars, guards, env, decls, _83_1345) -> begin
(
# 836 "FStar.SMTEncoding.Encode.fst"
let _83_1359 = (let _172_761 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 837 "FStar.SMTEncoding.Encode.fst"
let _83_1356 = (let _172_760 = (FStar_All.pipe_right branch (FStar_List.map (fun _83_1351 -> (match (_83_1351) with
| (t, _83_1350) -> begin
(encode_term t (
# 837 "FStar.SMTEncoding.Encode.fst"
let _83_1352 = env
in {bindings = _83_1352.bindings; depth = _83_1352.depth; tcenv = _83_1352.tcenv; warn = _83_1352.warn; cache = _83_1352.cache; nolabels = _83_1352.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1352.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _172_760 FStar_List.unzip))
in (match (_83_1356) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _172_761 FStar_List.unzip))
in (match (_83_1359) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _172_764 = (let _172_763 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _172_763 e))
in (_172_764)::p))))
end
| _83_1369 -> begin
(
# 850 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _172_770 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_172_770)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _172_772 = (let _172_771 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _172_771 tl))
in (aux _172_772 vars))
end
| _83_1381 -> begin
pats
end))
in (let _172_773 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _172_773 vars)))
end)
end)
in (
# 857 "FStar.SMTEncoding.Encode.fst"
let env = (
# 857 "FStar.SMTEncoding.Encode.fst"
let _83_1383 = env
in {bindings = _83_1383.bindings; depth = _83_1383.depth; tcenv = _83_1383.tcenv; warn = _83_1383.warn; cache = _83_1383.cache; nolabels = true; use_zfuel_name = _83_1383.use_zfuel_name; encode_non_total_function_typ = _83_1383.encode_non_total_function_typ})
in (
# 858 "FStar.SMTEncoding.Encode.fst"
let _83_1388 = (let _172_774 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _172_774 env))
in (match (_83_1388) with
| (pre, decls'') -> begin
(
# 859 "FStar.SMTEncoding.Encode.fst"
let _83_1391 = (let _172_775 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _172_775 env))
in (match (_83_1391) with
| (post, decls''') -> begin
(
# 860 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _172_780 = (let _172_779 = (let _172_778 = (let _172_777 = (let _172_776 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_172_776, post))
in (FStar_SMTEncoding_Term.mkImp _172_777))
in (pats, vars, _172_778))
in (FStar_SMTEncoding_Term.mkForall _172_779))
in (_172_780, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 864 "FStar.SMTEncoding.Encode.fst"
let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_786 = (FStar_Syntax_Print.tag_of_term phi)
in (let _172_785 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _172_786 _172_785)))
end else begin
()
end)
in (
# 869 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 870 "FStar.SMTEncoding.Encode.fst"
let _83_1407 = (FStar_Util.fold_map (fun decls x -> (
# 870 "FStar.SMTEncoding.Encode.fst"
let _83_1404 = (encode_term (Prims.fst x) env)
in (match (_83_1404) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_83_1407) with
| (decls, args) -> begin
(let _172_802 = (f args)
in (_172_802, decls))
end)))
in (
# 873 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _83_1410 -> (f, []))
in (
# 874 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _172_816 = (FStar_List.hd l)
in (FStar_All.pipe_left f _172_816)))
in (
# 875 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _83_8 -> (match (_83_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _83_1421 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 879 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 880 "FStar.SMTEncoding.Encode.fst"
let _83_1438 = (FStar_List.fold_right (fun _83_1429 _83_1432 -> (match ((_83_1429, _83_1432)) with
| ((t, _83_1428), (phis, decls)) -> begin
(
# 882 "FStar.SMTEncoding.Encode.fst"
let _83_1435 = (encode_formula t env)
in (match (_83_1435) with
| (phi, decls') -> begin
((phi)::phis, (FStar_List.append decls' decls))
end))
end)) l ([], []))
in (match (_83_1438) with
| (phis, decls) -> begin
(let _172_841 = (f phis)
in (_172_841, decls))
end)))
in (
# 887 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _83_9 -> (match (_83_9) with
| _83_1445::_83_1443::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 891 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _83_10 -> (match (_83_10) with
| (lhs, _83_1456)::(rhs, _83_1452)::[] -> begin
(
# 893 "FStar.SMTEncoding.Encode.fst"
let _83_1461 = (encode_formula rhs env)
in (match (_83_1461) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_1464) -> begin
(l1, decls1)
end
| _83_1468 -> begin
(
# 897 "FStar.SMTEncoding.Encode.fst"
let _83_1471 = (encode_formula lhs env)
in (match (_83_1471) with
| (l2, decls2) -> begin
(let _172_846 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_172_846, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _83_1473 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 902 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _83_11 -> (match (_83_11) with
| (guard, _83_1486)::(_then, _83_1482)::(_else, _83_1478)::[] -> begin
(
# 904 "FStar.SMTEncoding.Encode.fst"
let _83_1491 = (encode_formula guard env)
in (match (_83_1491) with
| (g, decls1) -> begin
(
# 905 "FStar.SMTEncoding.Encode.fst"
let _83_1494 = (encode_formula _then env)
in (match (_83_1494) with
| (t, decls2) -> begin
(
# 906 "FStar.SMTEncoding.Encode.fst"
let _83_1497 = (encode_formula _else env)
in (match (_83_1497) with
| (e, decls3) -> begin
(
# 907 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _83_1500 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 912 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _172_858 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _172_858)))
in (
# 913 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _172_911 = (let _172_867 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _172_867))
in (let _172_910 = (let _172_909 = (let _172_873 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _172_873))
in (let _172_908 = (let _172_907 = (let _172_906 = (let _172_882 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _172_882))
in (let _172_905 = (let _172_904 = (let _172_903 = (let _172_891 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _172_891))
in (_172_903)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_172_904)
in (_172_906)::_172_905))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_172_907)
in (_172_909)::_172_908))
in (_172_911)::_172_910))
in (
# 925 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 927 "FStar.SMTEncoding.Encode.fst"
let _83_1518 = (encode_formula phi' env)
in (match (_83_1518) with
| (phi, decls) -> begin
(let _172_914 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_172_914, decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 931 "FStar.SMTEncoding.Encode.fst"
let _83_1525 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_83_1525) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _83_1532; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _83_1529; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 935 "FStar.SMTEncoding.Encode.fst"
let _83_1543 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_83_1543) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 939 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1560::(x, _83_1557)::(t, _83_1553)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(
# 942 "FStar.SMTEncoding.Encode.fst"
let _83_1565 = (encode_term x env)
in (match (_83_1565) with
| (x, decls) -> begin
(
# 943 "FStar.SMTEncoding.Encode.fst"
let _83_1568 = (encode_term t env)
in (match (_83_1568) with
| (t, decls') -> begin
(let _172_915 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_172_915, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _83_1586::_83_1584::(r, _83_1581)::(msg, _83_1577)::(phi, _83_1573)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _172_919 = (let _172_916 = (FStar_Syntax_Subst.compress r)
in _172_916.FStar_Syntax_Syntax.n)
in (let _172_918 = (let _172_917 = (FStar_Syntax_Subst.compress msg)
in _172_917.FStar_Syntax_Syntax.n)
in (_172_919, _172_918)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _83_1594))) -> begin
(
# 949 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _83_1601 -> begin
(fallback phi)
end)
end
| _83_1603 when (head_redex env head) -> begin
(let _172_920 = (whnf env phi)
in (encode_formula _172_920 env))
end
| _83_1605 -> begin
(
# 959 "FStar.SMTEncoding.Encode.fst"
let _83_1608 = (encode_term phi env)
in (match (_83_1608) with
| (tt, decls) -> begin
(let _172_921 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_172_921, decls))
end))
end))
end
| _83_1610 -> begin
(
# 964 "FStar.SMTEncoding.Encode.fst"
let _83_1613 = (encode_term phi env)
in (match (_83_1613) with
| (tt, decls) -> begin
(let _172_922 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_172_922, decls))
end))
end))
in (
# 967 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 968 "FStar.SMTEncoding.Encode.fst"
let _83_1625 = (encode_binders None bs env)
in (match (_83_1625) with
| (vars, guards, env, decls, _83_1624) -> begin
(
# 969 "FStar.SMTEncoding.Encode.fst"
let _83_1638 = (let _172_934 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 970 "FStar.SMTEncoding.Encode.fst"
let _83_1635 = (let _172_933 = (FStar_All.pipe_right p (FStar_List.map (fun _83_1630 -> (match (_83_1630) with
| (t, _83_1629) -> begin
(encode_term t (
# 970 "FStar.SMTEncoding.Encode.fst"
let _83_1631 = env
in {bindings = _83_1631.bindings; depth = _83_1631.depth; tcenv = _83_1631.tcenv; warn = _83_1631.warn; cache = _83_1631.cache; nolabels = _83_1631.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _83_1631.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _172_933 FStar_List.unzip))
in (match (_83_1635) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _172_934 FStar_List.unzip))
in (match (_83_1638) with
| (pats, decls') -> begin
(
# 972 "FStar.SMTEncoding.Encode.fst"
let _83_1641 = (encode_formula body env)
in (match (_83_1641) with
| (body, decls'') -> begin
(let _172_935 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _172_935, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 975 "FStar.SMTEncoding.Encode.fst"
let _83_1642 = (debug phi)
in (
# 977 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _83_1654 -> (match (_83_1654) with
| (l, _83_1653) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_83_1657, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 987 "FStar.SMTEncoding.Encode.fst"
let _83_1667 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _172_952 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _172_952))
end else begin
()
end
in (
# 990 "FStar.SMTEncoding.Encode.fst"
let _83_1674 = (encode_q_body env vars pats body)
in (match (_83_1674) with
| (vars, pats, guard, body, decls) -> begin
(let _172_955 = (let _172_954 = (let _172_953 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _172_953))
in (FStar_SMTEncoding_Term.mkForall _172_954))
in (_172_955, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 994 "FStar.SMTEncoding.Encode.fst"
let _83_1686 = (encode_q_body env vars pats body)
in (match (_83_1686) with
| (vars, pats, guard, body, decls) -> begin
(let _172_958 = (let _172_957 = (let _172_956 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _172_956))
in (FStar_SMTEncoding_Term.mkExists _172_957))
in (_172_958, decls))
end))
end)))))))))))))))))

# 1003 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 1003 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1009 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 1010 "FStar.SMTEncoding.Encode.fst"
let _83_1692 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1692) with
| (asym, a) -> begin
(
# 1011 "FStar.SMTEncoding.Encode.fst"
let _83_1695 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1695) with
| (xsym, x) -> begin
(
# 1012 "FStar.SMTEncoding.Encode.fst"
let _83_1698 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1698) with
| (ysym, y) -> begin
(
# 1013 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 1014 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1015 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _172_1001 = (let _172_1000 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _172_1000))
in (FStar_SMTEncoding_Term.mkApp _172_1001))
in (
# 1016 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _172_1003 = (let _172_1002 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _172_1002, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_1003))
in (let _172_1009 = (let _172_1008 = (let _172_1007 = (let _172_1006 = (let _172_1005 = (let _172_1004 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _172_1004))
in (FStar_SMTEncoding_Term.mkForall _172_1005))
in (_172_1006, None))
in FStar_SMTEncoding_Term.Assume (_172_1007))
in (_172_1008)::[])
in (vname_decl)::_172_1009))))
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
let prims = (let _172_1169 = (let _172_1018 = (let _172_1017 = (let _172_1016 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1016))
in (quant axy _172_1017))
in (FStar_Syntax_Const.op_Eq, _172_1018))
in (let _172_1168 = (let _172_1167 = (let _172_1025 = (let _172_1024 = (let _172_1023 = (let _172_1022 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _172_1022))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1023))
in (quant axy _172_1024))
in (FStar_Syntax_Const.op_notEq, _172_1025))
in (let _172_1166 = (let _172_1165 = (let _172_1034 = (let _172_1033 = (let _172_1032 = (let _172_1031 = (let _172_1030 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1029 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1030, _172_1029)))
in (FStar_SMTEncoding_Term.mkLT _172_1031))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1032))
in (quant xy _172_1033))
in (FStar_Syntax_Const.op_LT, _172_1034))
in (let _172_1164 = (let _172_1163 = (let _172_1043 = (let _172_1042 = (let _172_1041 = (let _172_1040 = (let _172_1039 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1038 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1039, _172_1038)))
in (FStar_SMTEncoding_Term.mkLTE _172_1040))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1041))
in (quant xy _172_1042))
in (FStar_Syntax_Const.op_LTE, _172_1043))
in (let _172_1162 = (let _172_1161 = (let _172_1052 = (let _172_1051 = (let _172_1050 = (let _172_1049 = (let _172_1048 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1047 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1048, _172_1047)))
in (FStar_SMTEncoding_Term.mkGT _172_1049))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1050))
in (quant xy _172_1051))
in (FStar_Syntax_Const.op_GT, _172_1052))
in (let _172_1160 = (let _172_1159 = (let _172_1061 = (let _172_1060 = (let _172_1059 = (let _172_1058 = (let _172_1057 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1056 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1057, _172_1056)))
in (FStar_SMTEncoding_Term.mkGTE _172_1058))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1059))
in (quant xy _172_1060))
in (FStar_Syntax_Const.op_GTE, _172_1061))
in (let _172_1158 = (let _172_1157 = (let _172_1070 = (let _172_1069 = (let _172_1068 = (let _172_1067 = (let _172_1066 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1065 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1066, _172_1065)))
in (FStar_SMTEncoding_Term.mkSub _172_1067))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1068))
in (quant xy _172_1069))
in (FStar_Syntax_Const.op_Subtraction, _172_1070))
in (let _172_1156 = (let _172_1155 = (let _172_1077 = (let _172_1076 = (let _172_1075 = (let _172_1074 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _172_1074))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1075))
in (quant qx _172_1076))
in (FStar_Syntax_Const.op_Minus, _172_1077))
in (let _172_1154 = (let _172_1153 = (let _172_1086 = (let _172_1085 = (let _172_1084 = (let _172_1083 = (let _172_1082 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1081 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1082, _172_1081)))
in (FStar_SMTEncoding_Term.mkAdd _172_1083))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1084))
in (quant xy _172_1085))
in (FStar_Syntax_Const.op_Addition, _172_1086))
in (let _172_1152 = (let _172_1151 = (let _172_1095 = (let _172_1094 = (let _172_1093 = (let _172_1092 = (let _172_1091 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1090 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1091, _172_1090)))
in (FStar_SMTEncoding_Term.mkMul _172_1092))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1093))
in (quant xy _172_1094))
in (FStar_Syntax_Const.op_Multiply, _172_1095))
in (let _172_1150 = (let _172_1149 = (let _172_1104 = (let _172_1103 = (let _172_1102 = (let _172_1101 = (let _172_1100 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1099 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1100, _172_1099)))
in (FStar_SMTEncoding_Term.mkDiv _172_1101))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1102))
in (quant xy _172_1103))
in (FStar_Syntax_Const.op_Division, _172_1104))
in (let _172_1148 = (let _172_1147 = (let _172_1113 = (let _172_1112 = (let _172_1111 = (let _172_1110 = (let _172_1109 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1108 = (FStar_SMTEncoding_Term.unboxInt y)
in (_172_1109, _172_1108)))
in (FStar_SMTEncoding_Term.mkMod _172_1110))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _172_1111))
in (quant xy _172_1112))
in (FStar_Syntax_Const.op_Modulus, _172_1113))
in (let _172_1146 = (let _172_1145 = (let _172_1122 = (let _172_1121 = (let _172_1120 = (let _172_1119 = (let _172_1118 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _172_1117 = (FStar_SMTEncoding_Term.unboxBool y)
in (_172_1118, _172_1117)))
in (FStar_SMTEncoding_Term.mkAnd _172_1119))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1120))
in (quant xy _172_1121))
in (FStar_Syntax_Const.op_And, _172_1122))
in (let _172_1144 = (let _172_1143 = (let _172_1131 = (let _172_1130 = (let _172_1129 = (let _172_1128 = (let _172_1127 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _172_1126 = (FStar_SMTEncoding_Term.unboxBool y)
in (_172_1127, _172_1126)))
in (FStar_SMTEncoding_Term.mkOr _172_1128))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1129))
in (quant xy _172_1130))
in (FStar_Syntax_Const.op_Or, _172_1131))
in (let _172_1142 = (let _172_1141 = (let _172_1138 = (let _172_1137 = (let _172_1136 = (let _172_1135 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _172_1135))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_1136))
in (quant qx _172_1137))
in (FStar_Syntax_Const.op_Negation, _172_1138))
in (_172_1141)::[])
in (_172_1143)::_172_1142))
in (_172_1145)::_172_1144))
in (_172_1147)::_172_1146))
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
in (
# 1039 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _172_1201 = (FStar_All.pipe_right prims (FStar_List.filter (fun _83_1718 -> (match (_83_1718) with
| (l', _83_1717) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _172_1201 (FStar_List.collect (fun _83_1722 -> (match (_83_1722) with
| (_83_1720, b) -> begin
(b v)
end))))))
in (
# 1041 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _83_1728 -> (match (_83_1728) with
| (l', _83_1727) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1046 "FStar.SMTEncoding.Encode.fst"
let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (
# 1047 "FStar.SMTEncoding.Encode.fst"
let _83_1734 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_1734) with
| (xxsym, xx) -> begin
(
# 1048 "FStar.SMTEncoding.Encode.fst"
let _83_1737 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_1737) with
| (ffsym, ff) -> begin
(
# 1049 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _172_1227 = (let _172_1226 = (let _172_1225 = (let _172_1224 = (let _172_1223 = (let _172_1222 = (let _172_1221 = (let _172_1220 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _172_1220))
in (FStar_SMTEncoding_Term.mkEq _172_1221))
in (xx_has_type, _172_1222))
in (FStar_SMTEncoding_Term.mkImp _172_1223))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _172_1224))
in (FStar_SMTEncoding_Term.mkForall _172_1225))
in (_172_1226, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_172_1227)))
end))
end)))

# 1053 "FStar.SMTEncoding.Encode.fst"
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
in (let _172_1248 = (let _172_1239 = (let _172_1238 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_172_1238, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_172_1239))
in (let _172_1247 = (let _172_1246 = (let _172_1245 = (let _172_1244 = (let _172_1243 = (let _172_1242 = (let _172_1241 = (let _172_1240 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _172_1240))
in (FStar_SMTEncoding_Term.mkImp _172_1241))
in (((typing_pred)::[])::[], (xx)::[], _172_1242))
in (mkForall_fuel _172_1243))
in (_172_1244, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1245))
in (_172_1246)::[])
in (_172_1248)::_172_1247))))
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
in (let _172_1271 = (let _172_1260 = (let _172_1259 = (let _172_1258 = (let _172_1257 = (let _172_1256 = (let _172_1255 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _172_1255))
in (FStar_SMTEncoding_Term.mkImp _172_1256))
in (((typing_pred)::[])::[], (xx)::[], _172_1257))
in (mkForall_fuel _172_1258))
in (_172_1259, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1260))
in (let _172_1270 = (let _172_1269 = (let _172_1268 = (let _172_1267 = (let _172_1266 = (let _172_1265 = (let _172_1262 = (let _172_1261 = (FStar_SMTEncoding_Term.boxBool b)
in (_172_1261)::[])
in (_172_1262)::[])
in (let _172_1264 = (let _172_1263 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1263 tt))
in (_172_1265, (bb)::[], _172_1264)))
in (FStar_SMTEncoding_Term.mkForall _172_1266))
in (_172_1267, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_172_1268))
in (_172_1269)::[])
in (_172_1271)::_172_1270))))))
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
let precedes = (let _172_1285 = (let _172_1284 = (let _172_1283 = (let _172_1282 = (let _172_1281 = (let _172_1280 = (FStar_SMTEncoding_Term.boxInt a)
in (let _172_1279 = (let _172_1278 = (FStar_SMTEncoding_Term.boxInt b)
in (_172_1278)::[])
in (_172_1280)::_172_1279))
in (tt)::_172_1281)
in (tt)::_172_1282)
in ("Prims.Precedes", _172_1283))
in (FStar_SMTEncoding_Term.mkApp _172_1284))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _172_1285))
in (
# 1078 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _172_1286 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _172_1286))
in (let _172_1328 = (let _172_1292 = (let _172_1291 = (let _172_1290 = (let _172_1289 = (let _172_1288 = (let _172_1287 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _172_1287))
in (FStar_SMTEncoding_Term.mkImp _172_1288))
in (((typing_pred)::[])::[], (xx)::[], _172_1289))
in (mkForall_fuel _172_1290))
in (_172_1291, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1292))
in (let _172_1327 = (let _172_1326 = (let _172_1300 = (let _172_1299 = (let _172_1298 = (let _172_1297 = (let _172_1294 = (let _172_1293 = (FStar_SMTEncoding_Term.boxInt b)
in (_172_1293)::[])
in (_172_1294)::[])
in (let _172_1296 = (let _172_1295 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1295 tt))
in (_172_1297, (bb)::[], _172_1296)))
in (FStar_SMTEncoding_Term.mkForall _172_1298))
in (_172_1299, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_172_1300))
in (let _172_1325 = (let _172_1324 = (let _172_1323 = (let _172_1322 = (let _172_1321 = (let _172_1320 = (let _172_1319 = (let _172_1318 = (let _172_1317 = (let _172_1316 = (let _172_1315 = (let _172_1314 = (let _172_1303 = (let _172_1302 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _172_1301 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_172_1302, _172_1301)))
in (FStar_SMTEncoding_Term.mkGT _172_1303))
in (let _172_1313 = (let _172_1312 = (let _172_1306 = (let _172_1305 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _172_1304 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_172_1305, _172_1304)))
in (FStar_SMTEncoding_Term.mkGTE _172_1306))
in (let _172_1311 = (let _172_1310 = (let _172_1309 = (let _172_1308 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _172_1307 = (FStar_SMTEncoding_Term.unboxInt x)
in (_172_1308, _172_1307)))
in (FStar_SMTEncoding_Term.mkLT _172_1309))
in (_172_1310)::[])
in (_172_1312)::_172_1311))
in (_172_1314)::_172_1313))
in (typing_pred_y)::_172_1315)
in (typing_pred)::_172_1316)
in (FStar_SMTEncoding_Term.mk_and_l _172_1317))
in (_172_1318, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _172_1319))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _172_1320))
in (mkForall_fuel _172_1321))
in (_172_1322, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_172_1323))
in (_172_1324)::[])
in (_172_1326)::_172_1325))
in (_172_1328)::_172_1327)))))))))))
in (
# 1090 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun env nm tt -> (let _172_1339 = (let _172_1338 = (let _172_1337 = (let _172_1336 = (let _172_1335 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _172_1335))
in (FStar_SMTEncoding_Term.mkEq _172_1336))
in (_172_1337, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_172_1338))
in (_172_1339)::[]))
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
in (let _172_1362 = (let _172_1351 = (let _172_1350 = (let _172_1349 = (let _172_1348 = (let _172_1347 = (let _172_1346 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _172_1346))
in (FStar_SMTEncoding_Term.mkImp _172_1347))
in (((typing_pred)::[])::[], (xx)::[], _172_1348))
in (mkForall_fuel _172_1349))
in (_172_1350, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1351))
in (let _172_1361 = (let _172_1360 = (let _172_1359 = (let _172_1358 = (let _172_1357 = (let _172_1356 = (let _172_1353 = (let _172_1352 = (FStar_SMTEncoding_Term.boxString b)
in (_172_1352)::[])
in (_172_1353)::[])
in (let _172_1355 = (let _172_1354 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _172_1354 tt))
in (_172_1356, (bb)::[], _172_1355)))
in (FStar_SMTEncoding_Term.mkForall _172_1357))
in (_172_1358, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_172_1359))
in (_172_1360)::[])
in (_172_1362)::_172_1361))))))
in (
# 1098 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun env reft_name _83_1780 -> (
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
let refa = (let _172_1371 = (let _172_1370 = (let _172_1369 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_172_1369)::[])
in (reft_name, _172_1370))
in (FStar_SMTEncoding_Term.mkApp _172_1371))
in (
# 1103 "FStar.SMTEncoding.Encode.fst"
let refb = (let _172_1374 = (let _172_1373 = (let _172_1372 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_172_1372)::[])
in (reft_name, _172_1373))
in (FStar_SMTEncoding_Term.mkApp _172_1374))
in (
# 1104 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1105 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _172_1393 = (let _172_1380 = (let _172_1379 = (let _172_1378 = (let _172_1377 = (let _172_1376 = (let _172_1375 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _172_1375))
in (FStar_SMTEncoding_Term.mkImp _172_1376))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _172_1377))
in (mkForall_fuel _172_1378))
in (_172_1379, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_172_1380))
in (let _172_1392 = (let _172_1391 = (let _172_1390 = (let _172_1389 = (let _172_1388 = (let _172_1387 = (let _172_1386 = (let _172_1385 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _172_1384 = (let _172_1383 = (let _172_1382 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _172_1381 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_172_1382, _172_1381)))
in (FStar_SMTEncoding_Term.mkEq _172_1383))
in (_172_1385, _172_1384)))
in (FStar_SMTEncoding_Term.mkImp _172_1386))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _172_1387))
in (mkForall_fuel' 2 _172_1388))
in (_172_1389, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_172_1390))
in (_172_1391)::[])
in (_172_1393)::_172_1392))))))))))
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun env nm false_tm -> (
# 1109 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _172_1402 = (let _172_1401 = (let _172_1400 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_172_1400, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1401))
in (_172_1402)::[])))
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun env conj _83_1797 -> (
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
let valid = (let _172_1411 = (let _172_1410 = (let _172_1409 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_172_1409)::[])
in ("Valid", _172_1410))
in (FStar_SMTEncoding_Term.mkApp _172_1411))
in (
# 1117 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1118 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1418 = (let _172_1417 = (let _172_1416 = (let _172_1415 = (let _172_1414 = (let _172_1413 = (let _172_1412 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_172_1412, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1413))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1414))
in (FStar_SMTEncoding_Term.mkForall _172_1415))
in (_172_1416, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1417))
in (_172_1418)::[])))))))))
in (
# 1120 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun env disj _83_1809 -> (
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
let valid = (let _172_1427 = (let _172_1426 = (let _172_1425 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_172_1425)::[])
in ("Valid", _172_1426))
in (FStar_SMTEncoding_Term.mkApp _172_1427))
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1434 = (let _172_1433 = (let _172_1432 = (let _172_1431 = (let _172_1430 = (let _172_1429 = (let _172_1428 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_172_1428, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1429))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1430))
in (FStar_SMTEncoding_Term.mkForall _172_1431))
in (_172_1432, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1433))
in (_172_1434)::[])))))))))
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
let valid = (let _172_1443 = (let _172_1442 = (let _172_1441 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_172_1441)::[])
in ("Valid", _172_1442))
in (FStar_SMTEncoding_Term.mkApp _172_1443))
in (let _172_1450 = (let _172_1449 = (let _172_1448 = (let _172_1447 = (let _172_1446 = (let _172_1445 = (let _172_1444 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_172_1444, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1445))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _172_1446))
in (FStar_SMTEncoding_Term.mkForall _172_1447))
in (_172_1448, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1449))
in (_172_1450)::[])))))))))))
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
let valid = (let _172_1459 = (let _172_1458 = (let _172_1457 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_172_1457)::[])
in ("Valid", _172_1458))
in (FStar_SMTEncoding_Term.mkApp _172_1459))
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1466 = (let _172_1465 = (let _172_1464 = (let _172_1463 = (let _172_1462 = (let _172_1461 = (let _172_1460 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_172_1460, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1461))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1462))
in (FStar_SMTEncoding_Term.mkForall _172_1463))
in (_172_1464, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1465))
in (_172_1466)::[])))))))))
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
let valid = (let _172_1475 = (let _172_1474 = (let _172_1473 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_172_1473)::[])
in ("Valid", _172_1474))
in (FStar_SMTEncoding_Term.mkApp _172_1475))
in (
# 1155 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1156 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _172_1482 = (let _172_1481 = (let _172_1480 = (let _172_1479 = (let _172_1478 = (let _172_1477 = (let _172_1476 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_172_1476, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1477))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1478))
in (FStar_SMTEncoding_Term.mkForall _172_1479))
in (_172_1480, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1481))
in (_172_1482)::[])))))))))
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
let valid = (let _172_1491 = (let _172_1490 = (let _172_1489 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_172_1489)::[])
in ("Valid", _172_1490))
in (FStar_SMTEncoding_Term.mkApp _172_1491))
in (
# 1166 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _172_1494 = (let _172_1493 = (let _172_1492 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_172_1492)::[])
in ("Valid", _172_1493))
in (FStar_SMTEncoding_Term.mkApp _172_1494))
in (let _172_1508 = (let _172_1507 = (let _172_1506 = (let _172_1505 = (let _172_1504 = (let _172_1503 = (let _172_1502 = (let _172_1501 = (let _172_1500 = (let _172_1496 = (let _172_1495 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1495)::[])
in (_172_1496)::[])
in (let _172_1499 = (let _172_1498 = (let _172_1497 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1497, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _172_1498))
in (_172_1500, (xx)::[], _172_1499)))
in (FStar_SMTEncoding_Term.mkForall _172_1501))
in (_172_1502, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1503))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1504))
in (FStar_SMTEncoding_Term.mkForall _172_1505))
in (_172_1506, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1507))
in (_172_1508)::[]))))))))))
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
let valid = (let _172_1517 = (let _172_1516 = (let _172_1515 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_172_1515)::[])
in ("Valid", _172_1516))
in (FStar_SMTEncoding_Term.mkApp _172_1517))
in (
# 1176 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _172_1520 = (let _172_1519 = (let _172_1518 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_172_1518)::[])
in ("Valid", _172_1519))
in (FStar_SMTEncoding_Term.mkApp _172_1520))
in (let _172_1534 = (let _172_1533 = (let _172_1532 = (let _172_1531 = (let _172_1530 = (let _172_1529 = (let _172_1528 = (let _172_1527 = (let _172_1526 = (let _172_1522 = (let _172_1521 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1521)::[])
in (_172_1522)::[])
in (let _172_1525 = (let _172_1524 = (let _172_1523 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_172_1523, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _172_1524))
in (_172_1526, (xx)::[], _172_1525)))
in (FStar_SMTEncoding_Term.mkExists _172_1527))
in (_172_1528, valid))
in (FStar_SMTEncoding_Term.mkIff _172_1529))
in (((valid)::[])::[], (aa)::(bb)::[], _172_1530))
in (FStar_SMTEncoding_Term.mkForall _172_1531))
in (_172_1532, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_172_1533))
in (_172_1534)::[]))))))))))
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
in (let _172_1545 = (let _172_1544 = (let _172_1543 = (let _172_1542 = (let _172_1541 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_of_ty)
in (((range_of_ty)::[])::[], (aa)::(bb)::[], _172_1541))
in (FStar_SMTEncoding_Term.mkForall _172_1542))
in (_172_1543, Some ("Range_const typing")))
in FStar_SMTEncoding_Term.Assume (_172_1544))
in (_172_1545)::[])))))))
in (
# 1190 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_of_lid, mk_range_of_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _83_1895 -> (match (_83_1895) with
| (l, _83_1894) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_83_1898, f) -> begin
(f env s tt)
end))))))))))))))))))))))

# 1213 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1214 "FStar.SMTEncoding.Encode.fst"
let _83_1904 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _172_1757 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _172_1757))
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
let _83_1912 = (encode_sigelt' env se)
in (match (_83_1912) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _172_1760 = (let _172_1759 = (let _172_1758 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1758))
in (_172_1759)::[])
in (_172_1760, e))
end
| _83_1915 -> begin
(let _172_1767 = (let _172_1766 = (let _172_1762 = (let _172_1761 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1761))
in (_172_1762)::g)
in (let _172_1765 = (let _172_1764 = (let _172_1763 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_172_1763))
in (_172_1764)::[])
in (FStar_List.append _172_1766 _172_1765)))
in (_172_1767, e))
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
let _83_1928 = (encode_free_var env lid t tt quals)
in (match (_83_1928) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _172_1781 = (let _172_1780 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _172_1780))
in (_172_1781, env))
end else begin
(decls, env)
end
end))))
in (
# 1245 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_1935 lb -> (match (_83_1935) with
| (decls, env) -> begin
(
# 1247 "FStar.SMTEncoding.Encode.fst"
let _83_1939 = (let _172_1790 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _172_1790 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_83_1939) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_1957, _83_1959, _83_1961, _83_1963) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1259 "FStar.SMTEncoding.Encode.fst"
let _83_1969 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_1969) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _83_1972, t, quals, _83_1976) -> begin
(
# 1263 "FStar.SMTEncoding.Encode.fst"
let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_12 -> (match (_83_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _83_1989 -> begin
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
let _83_1994 = (encode_top_level_val env fv t quals)
in (match (_83_1994) with
| (decls, env) -> begin
(
# 1270 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1271 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _172_1793 = (let _172_1792 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _172_1792))
in (_172_1793, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _83_2000, _83_2002) -> begin
(
# 1277 "FStar.SMTEncoding.Encode.fst"
let _83_2007 = (encode_formula f env)
in (match (_83_2007) with
| (f, decls) -> begin
(
# 1278 "FStar.SMTEncoding.Encode.fst"
let g = (let _172_1798 = (let _172_1797 = (let _172_1796 = (let _172_1795 = (let _172_1794 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _172_1794))
in Some (_172_1795))
in (f, _172_1796))
in FStar_SMTEncoding_Term.Assume (_172_1797))
in (_172_1798)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _83_2012, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_83_2017, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _83_2025; FStar_Syntax_Syntax.lbtyp = _83_2023; FStar_Syntax_Syntax.lbeff = _83_2021; FStar_Syntax_Syntax.lbdef = _83_2019}::[]), _83_2032, _83_2034, _83_2036) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1285 "FStar.SMTEncoding.Encode.fst"
let _83_2042 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2042) with
| (tname, ttok, env) -> begin
(
# 1286 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1287 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1288 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _172_1801 = (let _172_1800 = (let _172_1799 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_172_1799)::[])
in ("Valid", _172_1800))
in (FStar_SMTEncoding_Term.mkApp _172_1801))
in (
# 1289 "FStar.SMTEncoding.Encode.fst"
let decls = (let _172_1809 = (let _172_1808 = (let _172_1807 = (let _172_1806 = (let _172_1805 = (let _172_1804 = (let _172_1803 = (let _172_1802 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _172_1802))
in (FStar_SMTEncoding_Term.mkEq _172_1803))
in (((valid_b2t_x)::[])::[], (xx)::[], _172_1804))
in (FStar_SMTEncoding_Term.mkForall _172_1805))
in (_172_1806, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_172_1807))
in (_172_1808)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_172_1809)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_83_2048, _83_2050, _83_2052, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_13 -> (match (_83_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _83_2062 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _83_2068, _83_2070, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_14 -> (match (_83_14) with
| FStar_Syntax_Syntax.Projector (_83_2076) -> begin
true
end
| _83_2079 -> begin
false
end)))) -> begin
(
# 1303 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1304 "FStar.SMTEncoding.Encode.fst"
let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_83_2083) -> begin
([], env)
end
| None -> begin
(
# 1309 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _83_2091, _83_2093, quals) -> begin
(
# 1315 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1316 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1317 "FStar.SMTEncoding.Encode.fst"
let _83_2105 = (FStar_Util.first_N nbinders formals)
in (match (_83_2105) with
| (formals, extra_formals) -> begin
(
# 1318 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _83_2109 _83_2113 -> (match ((_83_2109, _83_2113)) with
| ((formal, _83_2108), (binder, _83_2112)) -> begin
(let _172_1823 = (let _172_1822 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _172_1822))
in FStar_Syntax_Syntax.NT (_172_1823))
end)) formals binders)
in (
# 1319 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _172_1827 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _83_2117 -> (match (_83_2117) with
| (x, i) -> begin
(let _172_1826 = (
# 1319 "FStar.SMTEncoding.Encode.fst"
let _83_2118 = x
in (let _172_1825 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _83_2118.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_2118.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _172_1825}))
in (_172_1826, i))
end))))
in (FStar_All.pipe_right _172_1827 FStar_Syntax_Util.name_binders))
in (
# 1320 "FStar.SMTEncoding.Encode.fst"
let body = (let _172_1834 = (FStar_Syntax_Subst.compress body)
in (let _172_1833 = (let _172_1828 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _172_1828))
in (let _172_1832 = (let _172_1831 = (let _172_1830 = (FStar_Syntax_Subst.subst subst t)
in _172_1830.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _172_1829 -> Some (_172_1829)) _172_1831))
in (FStar_Syntax_Syntax.extend_app_n _172_1834 _172_1833 _172_1832 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1323 "FStar.SMTEncoding.Encode.fst"
let destruct_bound_function = (fun flid t_norm e -> (
# 1324 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t_norm -> (match ((let _172_1845 = (FStar_Syntax_Util.unascribe e)
in _172_1845.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1327 "FStar.SMTEncoding.Encode.fst"
let _83_2137 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_83_2137) with
| (binders, body, opening) -> begin
(match ((let _172_1846 = (FStar_Syntax_Subst.compress t_norm)
in _172_1846.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1330 "FStar.SMTEncoding.Encode.fst"
let _83_2144 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2144) with
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
let _83_2151 = (FStar_Util.first_N nformals binders)
in (match (_83_2151) with
| (bs0, rest) -> begin
(
# 1337 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1338 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _83_2155 _83_2159 -> (match ((_83_2155, _83_2159)) with
| ((b, _83_2154), (x, _83_2158)) -> begin
(let _172_1850 = (let _172_1849 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _172_1849))
in FStar_Syntax_Syntax.NT (_172_1850))
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
let _83_2165 = (eta_expand binders formals body tres)
in (match (_83_2165) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _83_2168) -> begin
(aux true x.FStar_Syntax_Syntax.sort)
end
| _83_2172 when (not (norm)) -> begin
(
# 1351 "FStar.SMTEncoding.Encode.fst"
let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _83_2175 -> begin
(let _172_1853 = (let _172_1852 = (FStar_Syntax_Print.term_to_string e)
in (let _172_1851 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _172_1852 _172_1851)))
in (FStar_All.failwith _172_1853))
end)
end))
end
| _83_2177 -> begin
(match ((let _172_1854 = (FStar_Syntax_Subst.compress t_norm)
in _172_1854.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1361 "FStar.SMTEncoding.Encode.fst"
let _83_2184 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_83_2184) with
| (formals, c) -> begin
(
# 1362 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1363 "FStar.SMTEncoding.Encode.fst"
let _83_2188 = (eta_expand [] formals e tres)
in (match (_83_2188) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _83_2190 -> begin
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
# 1371 "FStar.SMTEncoding.Encode.fst"
let _83_2218 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _83_2205 lb -> (match (_83_2205) with
| (toks, typs, decls, env) -> begin
(
# 1373 "FStar.SMTEncoding.Encode.fst"
let _83_2207 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1374 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1375 "FStar.SMTEncoding.Encode.fst"
let _83_2213 = (let _172_1859 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _172_1859 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_83_2213) with
| (tok, decl, env) -> begin
(let _172_1862 = (let _172_1861 = (let _172_1860 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_172_1860, tok))
in (_172_1861)::toks)
in (_172_1862, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_83_2218) with
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
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_15 -> (match (_83_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _83_2225 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _172_1865 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _172_1865)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _83_2235; FStar_Syntax_Syntax.lbunivs = _83_2233; FStar_Syntax_Syntax.lbtyp = _83_2231; FStar_Syntax_Syntax.lbeff = _83_2229; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid_fv, (f, ftok))::[]) -> begin
(
# 1386 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1387 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1388 "FStar.SMTEncoding.Encode.fst"
let _83_2255 = (destruct_bound_function flid t_norm e)
in (match (_83_2255) with
| (binders, body, _83_2252, _83_2254) -> begin
(
# 1389 "FStar.SMTEncoding.Encode.fst"
let _83_2262 = (encode_binders None binders env)
in (match (_83_2262) with
| (vars, guards, env', binder_decls, _83_2261) -> begin
(
# 1390 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2265 -> begin
(let _172_1867 = (let _172_1866 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _172_1866))
in (FStar_SMTEncoding_Term.mkApp _172_1867))
end)
in (
# 1391 "FStar.SMTEncoding.Encode.fst"
let _83_2271 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _172_1869 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _172_1868 = (encode_formula body env')
in (_172_1869, _172_1868)))
end else begin
(let _172_1870 = (encode_term body env')
in (app, _172_1870))
end
in (match (_83_2271) with
| (app, (body, decls2)) -> begin
(
# 1395 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _172_1879 = (let _172_1878 = (let _172_1875 = (let _172_1874 = (let _172_1873 = (let _172_1872 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _172_1871 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_172_1872, _172_1871)))
in (FStar_SMTEncoding_Term.mkImp _172_1873))
in (((app)::[])::[], vars, _172_1874))
in (FStar_SMTEncoding_Term.mkForall _172_1875))
in (let _172_1877 = (let _172_1876 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_172_1876))
in (_172_1878, _172_1877)))
in FStar_SMTEncoding_Term.Assume (_172_1879))
in (let _172_1881 = (let _172_1880 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _172_1880))
in (_172_1881, env)))
end)))
end))
end))))
end
| _83_2274 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1401 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _172_1882 = (varops.fresh "fuel")
in (_172_1882, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1402 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1403 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1404 "FStar.SMTEncoding.Encode.fst"
let _83_2292 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _83_2280 _83_2285 -> (match ((_83_2280, _83_2285)) with
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
let env = (let _172_1887 = (let _172_1886 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _172_1885 -> Some (_172_1885)) _172_1886))
in (push_free_var env flid gtok _172_1887))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_83_2292) with
| (gtoks, env) -> begin
(
# 1410 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1411 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _83_2301 t_norm _83_2312 -> (match ((_83_2301, _83_2312)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _83_2311; FStar_Syntax_Syntax.lbunivs = _83_2309; FStar_Syntax_Syntax.lbtyp = _83_2307; FStar_Syntax_Syntax.lbeff = _83_2305; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1412 "FStar.SMTEncoding.Encode.fst"
let _83_2317 = (destruct_bound_function flid t_norm e)
in (match (_83_2317) with
| (binders, body, formals, tres) -> begin
(
# 1413 "FStar.SMTEncoding.Encode.fst"
let _83_2324 = (encode_binders None binders env)
in (match (_83_2324) with
| (vars, guards, env', binder_decls, _83_2323) -> begin
(
# 1414 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _172_1898 = (let _172_1897 = (let _172_1896 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_172_1896)
in (g, _172_1897, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_172_1898))
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
let gsapp = (let _172_1901 = (let _172_1900 = (let _172_1899 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_172_1899)::vars_tm)
in (g, _172_1900))
in (FStar_SMTEncoding_Term.mkApp _172_1901))
in (
# 1420 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _172_1904 = (let _172_1903 = (let _172_1902 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_172_1902)::vars_tm)
in (g, _172_1903))
in (FStar_SMTEncoding_Term.mkApp _172_1904))
in (
# 1421 "FStar.SMTEncoding.Encode.fst"
let _83_2334 = (encode_term body env')
in (match (_83_2334) with
| (body_tm, decls2) -> begin
(
# 1422 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _172_1913 = (let _172_1912 = (let _172_1909 = (let _172_1908 = (let _172_1907 = (let _172_1906 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _172_1905 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_172_1906, _172_1905)))
in (FStar_SMTEncoding_Term.mkImp _172_1907))
in (((gsapp)::[])::[], (fuel)::vars, _172_1908))
in (FStar_SMTEncoding_Term.mkForall _172_1909))
in (let _172_1911 = (let _172_1910 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_172_1910))
in (_172_1912, _172_1911)))
in FStar_SMTEncoding_Term.Assume (_172_1913))
in (
# 1424 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _172_1917 = (let _172_1916 = (let _172_1915 = (let _172_1914 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _172_1914))
in (FStar_SMTEncoding_Term.mkForall _172_1915))
in (_172_1916, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_172_1917))
in (
# 1426 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _172_1926 = (let _172_1925 = (let _172_1924 = (let _172_1923 = (let _172_1922 = (let _172_1921 = (let _172_1920 = (let _172_1919 = (let _172_1918 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_172_1918)::vars_tm)
in (g, _172_1919))
in (FStar_SMTEncoding_Term.mkApp _172_1920))
in (gsapp, _172_1921))
in (FStar_SMTEncoding_Term.mkEq _172_1922))
in (((gsapp)::[])::[], (fuel)::vars, _172_1923))
in (FStar_SMTEncoding_Term.mkForall _172_1924))
in (_172_1925, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_172_1926))
in (
# 1428 "FStar.SMTEncoding.Encode.fst"
let _83_2357 = (
# 1429 "FStar.SMTEncoding.Encode.fst"
let _83_2344 = (encode_binders None formals env0)
in (match (_83_2344) with
| (vars, v_guards, env, binder_decls, _83_2343) -> begin
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
let tok_app = (let _172_1927 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _172_1927 ((fuel)::vars)))
in (let _172_1931 = (let _172_1930 = (let _172_1929 = (let _172_1928 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _172_1928))
in (FStar_SMTEncoding_Term.mkForall _172_1929))
in (_172_1930, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_172_1931)))
in (
# 1436 "FStar.SMTEncoding.Encode.fst"
let _83_2354 = (
# 1437 "FStar.SMTEncoding.Encode.fst"
let _83_2351 = (encode_term_pred None tres env gapp)
in (match (_83_2351) with
| (g_typing, d3) -> begin
(let _172_1939 = (let _172_1938 = (let _172_1937 = (let _172_1936 = (let _172_1935 = (let _172_1934 = (let _172_1933 = (let _172_1932 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_172_1932, g_typing))
in (FStar_SMTEncoding_Term.mkImp _172_1933))
in (((gapp)::[])::[], (fuel)::vars, _172_1934))
in (FStar_SMTEncoding_Term.mkForall _172_1935))
in (_172_1936, Some ("Typing correspondence of token to term")))
in FStar_SMTEncoding_Term.Assume (_172_1937))
in (_172_1938)::[])
in (d3, _172_1939))
end))
in (match (_83_2354) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_83_2357) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1441 "FStar.SMTEncoding.Encode.fst"
let _83_2373 = (let _172_1942 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _83_2361 _83_2365 -> (match ((_83_2361, _83_2365)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1442 "FStar.SMTEncoding.Encode.fst"
let _83_2369 = (encode_one_binding env0 gtok ty bs)
in (match (_83_2369) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _172_1942))
in (match (_83_2373) with
| (decls, eqns, env0) -> begin
(
# 1444 "FStar.SMTEncoding.Encode.fst"
let _83_2382 = (let _172_1944 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _172_1944 (FStar_List.partition (fun _83_16 -> (match (_83_16) with
| FStar_SMTEncoding_Term.DeclFun (_83_2376) -> begin
true
end
| _83_2379 -> begin
false
end)))))
in (match (_83_2382) with
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
end)
with
| Let_rec_unencodeable -> begin
(
# 1450 "FStar.SMTEncoding.Encode.fst"
let msg = (let _172_1947 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _172_1947 (FStar_String.concat " and ")))
in (
# 1451 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _83_2386, _83_2388, _83_2390) -> begin
(
# 1456 "FStar.SMTEncoding.Encode.fst"
let _83_2395 = (encode_signature env ses)
in (match (_83_2395) with
| (g, env) -> begin
(
# 1457 "FStar.SMTEncoding.Encode.fst"
let _83_2407 = (FStar_All.pipe_right g (FStar_List.partition (fun _83_17 -> (match (_83_17) with
| FStar_SMTEncoding_Term.Assume (_83_2398, Some ("inversion axiom")) -> begin
false
end
| _83_2404 -> begin
true
end))))
in (match (_83_2407) with
| (g', inversions) -> begin
(
# 1460 "FStar.SMTEncoding.Encode.fst"
let _83_2416 = (FStar_All.pipe_right g' (FStar_List.partition (fun _83_18 -> (match (_83_18) with
| FStar_SMTEncoding_Term.DeclFun (_83_2410) -> begin
true
end
| _83_2413 -> begin
false
end))))
in (match (_83_2416) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _83_2419, tps, k, _83_2423, datas, quals, _83_2427) -> begin
(
# 1466 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _83_19 -> (match (_83_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _83_2434 -> begin
false
end))))
in (
# 1467 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1469 "FStar.SMTEncoding.Encode.fst"
let _83_2446 = c
in (match (_83_2446) with
| (name, args, _83_2441, _83_2443, _83_2445) -> begin
(let _172_1955 = (let _172_1954 = (let _172_1953 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _172_1953, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_1954))
in (_172_1955)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1473 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _172_1961 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _172_1961 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1477 "FStar.SMTEncoding.Encode.fst"
let _83_2453 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_83_2453) with
| (xxsym, xx) -> begin
(
# 1478 "FStar.SMTEncoding.Encode.fst"
let _83_2489 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _83_2456 l -> (match (_83_2456) with
| (out, decls) -> begin
(
# 1479 "FStar.SMTEncoding.Encode.fst"
let _83_2461 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_83_2461) with
| (_83_2459, data_t) -> begin
(
# 1480 "FStar.SMTEncoding.Encode.fst"
let _83_2464 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_83_2464) with
| (args, res) -> begin
(
# 1481 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _172_1964 = (FStar_Syntax_Subst.compress res)
in _172_1964.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_83_2466, indices) -> begin
indices
end
| _83_2471 -> begin
[]
end)
in (
# 1484 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _83_2477 -> (match (_83_2477) with
| (x, _83_2476) -> begin
(let _172_1969 = (let _172_1968 = (let _172_1967 = (mk_term_projector_name l x)
in (_172_1967, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _172_1968))
in (push_term_var env x _172_1969))
end)) env))
in (
# 1487 "FStar.SMTEncoding.Encode.fst"
let _83_2481 = (encode_args indices env)
in (match (_83_2481) with
| (indices, decls') -> begin
(
# 1488 "FStar.SMTEncoding.Encode.fst"
let _83_2482 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1490 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _172_1974 = (FStar_List.map2 (fun v a -> (let _172_1973 = (let _172_1972 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_172_1972, a))
in (FStar_SMTEncoding_Term.mkEq _172_1973))) vars indices)
in (FStar_All.pipe_right _172_1974 FStar_SMTEncoding_Term.mk_and_l))
in (let _172_1979 = (let _172_1978 = (let _172_1977 = (let _172_1976 = (let _172_1975 = (mk_data_tester env l xx)
in (_172_1975, eqs))
in (FStar_SMTEncoding_Term.mkAnd _172_1976))
in (out, _172_1977))
in (FStar_SMTEncoding_Term.mkOr _172_1978))
in (_172_1979, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_83_2489) with
| (data_ax, decls) -> begin
(
# 1492 "FStar.SMTEncoding.Encode.fst"
let _83_2492 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2492) with
| (ffsym, ff) -> begin
(
# 1493 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _172_1980 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _172_1980 xx tapp))
in (let _172_1987 = (let _172_1986 = (let _172_1985 = (let _172_1984 = (let _172_1983 = (let _172_1982 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _172_1981 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _172_1982, _172_1981)))
in (FStar_SMTEncoding_Term.mkForall _172_1983))
in (_172_1984, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_172_1985))
in (_172_1986)::[])
in (FStar_List.append decls _172_1987)))
end))
end))
end))
end)
in (
# 1497 "FStar.SMTEncoding.Encode.fst"
let _83_2502 = (match ((let _172_1988 = (FStar_Syntax_Subst.compress k)
in _172_1988.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _83_2499 -> begin
(tps, k)
end)
in (match (_83_2502) with
| (formals, res) -> begin
(
# 1503 "FStar.SMTEncoding.Encode.fst"
let _83_2505 = (FStar_Syntax_Subst.open_term formals res)
in (match (_83_2505) with
| (formals, res) -> begin
(
# 1504 "FStar.SMTEncoding.Encode.fst"
let _83_2512 = (encode_binders None formals env)
in (match (_83_2512) with
| (vars, guards, env', binder_decls, _83_2511) -> begin
(
# 1506 "FStar.SMTEncoding.Encode.fst"
let _83_2516 = (new_term_constant_and_tok_from_lid env t)
in (match (_83_2516) with
| (tname, ttok, env) -> begin
(
# 1507 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1508 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1509 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _172_1990 = (let _172_1989 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _172_1989))
in (FStar_SMTEncoding_Term.mkApp _172_1990))
in (
# 1510 "FStar.SMTEncoding.Encode.fst"
let _83_2537 = (
# 1511 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _172_1994 = (let _172_1993 = (FStar_All.pipe_right vars (FStar_List.map (fun _83_2522 -> (match (_83_2522) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _172_1992 = (varops.next_id ())
in (tname, _172_1993, FStar_SMTEncoding_Term.Term_sort, _172_1992, false)))
in (constructor_or_logic_type_decl _172_1994))
in (
# 1512 "FStar.SMTEncoding.Encode.fst"
let _83_2534 = (match (vars) with
| [] -> begin
(let _172_1998 = (let _172_1997 = (let _172_1996 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _172_1995 -> Some (_172_1995)) _172_1996))
in (push_free_var env t tname _172_1997))
in ([], _172_1998))
end
| _83_2526 -> begin
(
# 1515 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1516 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _172_1999 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _172_1999))
in (
# 1517 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1518 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1521 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _172_2003 = (let _172_2002 = (let _172_2001 = (let _172_2000 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _172_2000))
in (FStar_SMTEncoding_Term.mkForall' _172_2001))
in (_172_2002, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_172_2003))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_83_2534) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_83_2537) with
| (decls, env) -> begin
(
# 1524 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1525 "FStar.SMTEncoding.Encode.fst"
let _83_2540 = (encode_term_pred None res env' tapp)
in (match (_83_2540) with
| (k, decls) -> begin
(
# 1526 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _172_2007 = (let _172_2006 = (let _172_2005 = (let _172_2004 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _172_2004))
in (_172_2005, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_172_2006))
in (_172_2007)::[])
end else begin
[]
end
in (let _172_2013 = (let _172_2012 = (let _172_2011 = (let _172_2010 = (let _172_2009 = (let _172_2008 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _172_2008))
in (FStar_SMTEncoding_Term.mkForall _172_2009))
in (_172_2010, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_172_2011))
in (_172_2012)::[])
in (FStar_List.append (FStar_List.append decls karr) _172_2013)))
end))
in (
# 1531 "FStar.SMTEncoding.Encode.fst"
let aux = (let _172_2017 = (let _172_2014 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _172_2014))
in (let _172_2016 = (let _172_2015 = (pretype_axiom tapp vars)
in (_172_2015)::[])
in (FStar_List.append _172_2017 _172_2016)))
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
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2547, _83_2549, _83_2551, _83_2553, _83_2555, _83_2557, _83_2559) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _83_2564, t, _83_2567, n_tps, quals, _83_2571, drange) -> begin
(
# 1544 "FStar.SMTEncoding.Encode.fst"
let _83_2578 = (new_term_constant_and_tok_from_lid env d)
in (match (_83_2578) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1545 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1546 "FStar.SMTEncoding.Encode.fst"
let _83_2582 = (FStar_Syntax_Util.arrow_formals t)
in (match (_83_2582) with
| (formals, t_res) -> begin
(
# 1547 "FStar.SMTEncoding.Encode.fst"
let _83_2585 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_83_2585) with
| (fuel_var, fuel_tm) -> begin
(
# 1548 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1549 "FStar.SMTEncoding.Encode.fst"
let _83_2592 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2592) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1550 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _172_2019 = (mk_term_projector_name d x)
in (_172_2019, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1551 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _172_2021 = (let _172_2020 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _172_2020, true))
in (FStar_All.pipe_right _172_2021 FStar_SMTEncoding_Term.constructor_to_decl))
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
let _83_2602 = (encode_term_pred None t env ddtok_tm)
in (match (_83_2602) with
| (tok_typing, decls3) -> begin
(
# 1559 "FStar.SMTEncoding.Encode.fst"
let _83_2609 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_83_2609) with
| (vars', guards', env'', decls_formals, _83_2608) -> begin
(
# 1560 "FStar.SMTEncoding.Encode.fst"
let _83_2614 = (
# 1561 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1562 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_83_2614) with
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
| _83_2618 -> begin
(let _172_2023 = (let _172_2022 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _172_2022))
in (_172_2023)::[])
end)
in (
# 1569 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _83_2621 -> (match (()) with
| () -> begin
(
# 1570 "FStar.SMTEncoding.Encode.fst"
let _83_2624 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_83_2624) with
| (head, args) -> begin
(match ((let _172_2026 = (FStar_Syntax_Subst.compress head)
in _172_2026.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(
# 1574 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (
# 1575 "FStar.SMTEncoding.Encode.fst"
let _83_2642 = (encode_args args env')
in (match (_83_2642) with
| (encoded_args, arg_decls) -> begin
(
# 1576 "FStar.SMTEncoding.Encode.fst"
let _83_2657 = (FStar_List.fold_left (fun _83_2646 arg -> (match (_83_2646) with
| (env, arg_vars, eqns) -> begin
(
# 1577 "FStar.SMTEncoding.Encode.fst"
let _83_2652 = (let _172_2029 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _172_2029))
in (match (_83_2652) with
| (_83_2649, xv, env) -> begin
(let _172_2031 = (let _172_2030 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_172_2030)::eqns)
in (env, (xv)::arg_vars, _172_2031))
end))
end)) (env', [], []) encoded_args)
in (match (_83_2657) with
| (_83_2654, arg_vars, eqns) -> begin
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
let typing_inversion = (let _172_2038 = (let _172_2037 = (let _172_2036 = (let _172_2035 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _172_2034 = (let _172_2033 = (let _172_2032 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _172_2032))
in (FStar_SMTEncoding_Term.mkImp _172_2033))
in (((ty_pred)::[])::[], _172_2035, _172_2034)))
in (FStar_SMTEncoding_Term.mkForall _172_2036))
in (_172_2037, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_172_2038))
in (
# 1590 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1592 "FStar.SMTEncoding.Encode.fst"
let x = (let _172_2039 = (varops.fresh "x")
in (_172_2039, FStar_SMTEncoding_Term.Term_sort))
in (
# 1593 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _172_2049 = (let _172_2048 = (let _172_2047 = (let _172_2046 = (let _172_2041 = (let _172_2040 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_172_2040)::[])
in (_172_2041)::[])
in (let _172_2045 = (let _172_2044 = (let _172_2043 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _172_2042 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_172_2043, _172_2042)))
in (FStar_SMTEncoding_Term.mkImp _172_2044))
in (_172_2046, (x)::[], _172_2045)))
in (FStar_SMTEncoding_Term.mkForall _172_2047))
in (_172_2048, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_172_2049))))
end else begin
(
# 1596 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _172_2052 = (let _172_2051 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _172_2051 dapp))
in (_172_2052)::[])
end
| _83_2671 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _172_2059 = (let _172_2058 = (let _172_2057 = (let _172_2056 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _172_2055 = (let _172_2054 = (let _172_2053 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _172_2053))
in (FStar_SMTEncoding_Term.mkImp _172_2054))
in (((ty_pred)::[])::[], _172_2056, _172_2055)))
in (FStar_SMTEncoding_Term.mkForall _172_2057))
in (_172_2058, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_172_2059)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _83_2675 -> begin
(
# 1604 "FStar.SMTEncoding.Encode.fst"
let _83_2676 = (let _172_2062 = (let _172_2061 = (FStar_Syntax_Print.lid_to_string d)
in (let _172_2060 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _172_2061 _172_2060)))
in (FStar_TypeChecker_Errors.warn drange _172_2062))
in ([], []))
end)
end))
end))
in (
# 1607 "FStar.SMTEncoding.Encode.fst"
let _83_2680 = (encode_elim ())
in (match (_83_2680) with
| (decls2, elim) -> begin
(
# 1608 "FStar.SMTEncoding.Encode.fst"
let g = (let _172_2087 = (let _172_2086 = (let _172_2071 = (let _172_2070 = (let _172_2069 = (let _172_2068 = (let _172_2067 = (let _172_2066 = (let _172_2065 = (let _172_2064 = (let _172_2063 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _172_2063))
in Some (_172_2064))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _172_2065))
in FStar_SMTEncoding_Term.DeclFun (_172_2066))
in (_172_2067)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _172_2068))
in (FStar_List.append _172_2069 proxy_fresh))
in (FStar_List.append _172_2070 decls_formals))
in (FStar_List.append _172_2071 decls_pred))
in (let _172_2085 = (let _172_2084 = (let _172_2083 = (let _172_2075 = (let _172_2074 = (let _172_2073 = (let _172_2072 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _172_2072))
in (FStar_SMTEncoding_Term.mkForall _172_2073))
in (_172_2074, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_172_2075))
in (let _172_2082 = (let _172_2081 = (let _172_2080 = (let _172_2079 = (let _172_2078 = (let _172_2077 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _172_2076 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _172_2077, _172_2076)))
in (FStar_SMTEncoding_Term.mkForall _172_2078))
in (_172_2079, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_172_2080))
in (_172_2081)::[])
in (_172_2083)::_172_2082))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_172_2084)
in (FStar_List.append _172_2086 _172_2085)))
in (FStar_List.append _172_2087 elim))
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
let _83_2689 = (encode_free_var env x t t_norm [])
in (match (_83_2689) with
| (decls, env) -> begin
(
# 1627 "FStar.SMTEncoding.Encode.fst"
let _83_2694 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_83_2694) with
| (n, x', _83_2693) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _83_2698) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (
# 1633 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1634 "FStar.SMTEncoding.Encode.fst"
let _83_2707 = (encode_function_type_as_formula None None t env)
in (match (_83_2707) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (
# 1638 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _172_2100 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _172_2100)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1641 "FStar.SMTEncoding.Encode.fst"
let _83_2717 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2717) with
| (vname, vtok, env) -> begin
(
# 1642 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _172_2101 = (FStar_Syntax_Subst.compress t_norm)
in _172_2101.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _83_2720) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _83_2723 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _83_2726 -> begin
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
let _83_2741 = (
# 1655 "FStar.SMTEncoding.Encode.fst"
let _83_2736 = (curried_arrow_formals_comp t_norm)
in (match (_83_2736) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _172_2103 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _172_2103))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_83_2741) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1659 "FStar.SMTEncoding.Encode.fst"
let _83_2745 = (new_term_constant_and_tok_from_lid env lid)
in (match (_83_2745) with
| (vname, vtok, env) -> begin
(
# 1660 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _83_2748 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1663 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _83_20 -> (match (_83_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1665 "FStar.SMTEncoding.Encode.fst"
let _83_2764 = (FStar_Util.prefix vars)
in (match (_83_2764) with
| (_83_2759, (xxsym, _83_2762)) -> begin
(
# 1666 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _172_2120 = (let _172_2119 = (let _172_2118 = (let _172_2117 = (let _172_2116 = (let _172_2115 = (let _172_2114 = (let _172_2113 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _172_2113))
in (vapp, _172_2114))
in (FStar_SMTEncoding_Term.mkEq _172_2115))
in (((vapp)::[])::[], vars, _172_2116))
in (FStar_SMTEncoding_Term.mkForall _172_2117))
in (_172_2118, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_172_2119))
in (_172_2120)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1671 "FStar.SMTEncoding.Encode.fst"
let _83_2776 = (FStar_Util.prefix vars)
in (match (_83_2776) with
| (_83_2771, (xxsym, _83_2774)) -> begin
(
# 1672 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1673 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1674 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _172_2122 = (let _172_2121 = (mk_term_projector_name d f)
in (_172_2121, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _172_2122))
in (let _172_2127 = (let _172_2126 = (let _172_2125 = (let _172_2124 = (let _172_2123 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _172_2123))
in (FStar_SMTEncoding_Term.mkForall _172_2124))
in (_172_2125, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_172_2126))
in (_172_2127)::[]))))
end))
end
| _83_2781 -> begin
[]
end)))))
in (
# 1678 "FStar.SMTEncoding.Encode.fst"
let _83_2788 = (encode_binders None formals env)
in (match (_83_2788) with
| (vars, guards, env', decls1, _83_2787) -> begin
(
# 1679 "FStar.SMTEncoding.Encode.fst"
let _83_2797 = (match (pre_opt) with
| None -> begin
(let _172_2128 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_172_2128, decls1))
end
| Some (p) -> begin
(
# 1681 "FStar.SMTEncoding.Encode.fst"
let _83_2794 = (encode_formula p env')
in (match (_83_2794) with
| (g, ds) -> begin
(let _172_2129 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_172_2129, (FStar_List.append decls1 ds)))
end))
end)
in (match (_83_2797) with
| (guard, decls1) -> begin
(
# 1682 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1684 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _172_2131 = (let _172_2130 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _172_2130))
in (FStar_SMTEncoding_Term.mkApp _172_2131))
in (
# 1685 "FStar.SMTEncoding.Encode.fst"
let _83_2821 = (
# 1686 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _172_2134 = (let _172_2133 = (FStar_All.pipe_right formals (FStar_List.map (fun _83_2800 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _172_2133, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_172_2134))
in (
# 1687 "FStar.SMTEncoding.Encode.fst"
let _83_2808 = (
# 1688 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1688 "FStar.SMTEncoding.Encode.fst"
let _83_2803 = env
in {bindings = _83_2803.bindings; depth = _83_2803.depth; tcenv = _83_2803.tcenv; warn = _83_2803.warn; cache = _83_2803.cache; nolabels = _83_2803.nolabels; use_zfuel_name = _83_2803.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_83_2808) with
| (tok_typing, decls2) -> begin
(
# 1692 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1693 "FStar.SMTEncoding.Encode.fst"
let _83_2818 = (match (formals) with
| [] -> begin
(let _172_2138 = (let _172_2137 = (let _172_2136 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _172_2135 -> Some (_172_2135)) _172_2136))
in (push_free_var env lid vname _172_2137))
in ((FStar_List.append decls2 ((tok_typing)::[])), _172_2138))
end
| _83_2812 -> begin
(
# 1696 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1697 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _172_2139 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _172_2139))
in (
# 1698 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _172_2143 = (let _172_2142 = (let _172_2141 = (let _172_2140 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _172_2140))
in (FStar_SMTEncoding_Term.mkForall _172_2141))
in (_172_2142, Some ("Name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_172_2143))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_83_2818) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_83_2821) with
| (decls2, env) -> begin
(
# 1701 "FStar.SMTEncoding.Encode.fst"
let _83_2829 = (
# 1702 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1703 "FStar.SMTEncoding.Encode.fst"
let _83_2825 = (encode_term res_t env')
in (match (_83_2825) with
| (encoded_res_t, decls) -> begin
(let _172_2144 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _172_2144, decls))
end)))
in (match (_83_2829) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1705 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _172_2148 = (let _172_2147 = (let _172_2146 = (let _172_2145 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _172_2145))
in (FStar_SMTEncoding_Term.mkForall _172_2146))
in (_172_2147, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_172_2148))
in (
# 1706 "FStar.SMTEncoding.Encode.fst"
let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _172_2154 = (let _172_2151 = (let _172_2150 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _172_2149 = (varops.next_id ())
in (vname, _172_2150, FStar_SMTEncoding_Term.Term_sort, _172_2149)))
in (FStar_SMTEncoding_Term.fresh_constructor _172_2151))
in (let _172_2153 = (let _172_2152 = (pretype_axiom vapp vars)
in (_172_2152)::[])
in (_172_2154)::_172_2153))
end else begin
[]
end
in (
# 1711 "FStar.SMTEncoding.Encode.fst"
let g = (let _172_2156 = (let _172_2155 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_172_2155)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _172_2156))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _83_2837 se -> (match (_83_2837) with
| (g, env) -> begin
(
# 1717 "FStar.SMTEncoding.Encode.fst"
let _83_2841 = (encode_sigelt env se)
in (match (_83_2841) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1720 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1745 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _83_2848 -> (match (_83_2848) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_83_2850) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1750 "FStar.SMTEncoding.Encode.fst"
let _83_2857 = (new_term_constant env x)
in (match (_83_2857) with
| (xxsym, xx, env') -> begin
(
# 1751 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1752 "FStar.SMTEncoding.Encode.fst"
let _83_2859 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _172_2171 = (FStar_Syntax_Print.bv_to_string x)
in (let _172_2170 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _172_2169 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _172_2171 _172_2170 _172_2169))))
end else begin
()
end
in (
# 1754 "FStar.SMTEncoding.Encode.fst"
let _83_2863 = (encode_term_pred None t1 env xx)
in (match (_83_2863) with
| (t, decls') -> begin
(
# 1755 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _172_2175 = (let _172_2174 = (FStar_Syntax_Print.bv_to_string x)
in (let _172_2173 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _172_2172 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _172_2174 _172_2173 _172_2172))))
in Some (_172_2175))
end else begin
None
end
in (
# 1759 "FStar.SMTEncoding.Encode.fst"
let g = (let _172_2180 = (let _172_2179 = (let _172_2178 = (let _172_2177 = (FStar_All.pipe_left (fun _172_2176 -> Some (_172_2176)) (Prims.strcat "Encoding " xxsym))
in (t, _172_2177))
in FStar_SMTEncoding_Term.Assume (_172_2178))
in (_172_2179)::[])
in (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') _172_2180))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_83_2868, t)) -> begin
(
# 1765 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1766 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (
# 1768 "FStar.SMTEncoding.Encode.fst"
let _83_2877 = (encode_free_var env fv t t_norm [])
in (match (_83_2877) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1773 "FStar.SMTEncoding.Encode.fst"
let _83_2891 = (encode_sigelt env se)
in (match (_83_2891) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1778 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1779 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _83_2898 -> (match (_83_2898) with
| (l, _83_2895, _83_2897) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1780 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _83_2905 -> (match (_83_2905) with
| (l, _83_2902, _83_2904) -> begin
(let _172_2188 = (FStar_All.pipe_left (fun _172_2184 -> FStar_SMTEncoding_Term.Echo (_172_2184)) (Prims.fst l))
in (let _172_2187 = (let _172_2186 = (let _172_2185 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_172_2185))
in (_172_2186)::[])
in (_172_2188)::_172_2187))
end))))
in (prefix, suffix))))

# 1784 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1785 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _172_2193 = (let _172_2192 = (let _172_2191 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _172_2191; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_172_2192)::[])
in (FStar_ST.op_Colon_Equals last_env _172_2193)))

# 1788 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_83_2911 -> begin
(
# 1790 "FStar.SMTEncoding.Encode.fst"
let _83_2914 = e
in {bindings = _83_2914.bindings; depth = _83_2914.depth; tcenv = tcenv; warn = _83_2914.warn; cache = _83_2914.cache; nolabels = _83_2914.nolabels; use_zfuel_name = _83_2914.use_zfuel_name; encode_non_total_function_typ = _83_2914.encode_non_total_function_typ})
end))

# 1791 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _83_2920::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1794 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _83_2922 -> (match (()) with
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
let _83_2928 = hd
in {bindings = _83_2928.bindings; depth = _83_2928.depth; tcenv = _83_2928.tcenv; warn = _83_2928.warn; cache = refs; nolabels = _83_2928.nolabels; use_zfuel_name = _83_2928.use_zfuel_name; encode_non_total_function_typ = _83_2928.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1800 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _83_2931 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _83_2935::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1803 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _83_2937 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1804 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _83_2938 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1805 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _83_2939 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_83_2942::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _83_2947 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1811 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1812 "FStar.SMTEncoding.Encode.fst"
let _83_2949 = (init_env tcenv)
in (
# 1813 "FStar.SMTEncoding.Encode.fst"
let _83_2951 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1815 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1816 "FStar.SMTEncoding.Encode.fst"
let _83_2954 = (push_env ())
in (
# 1817 "FStar.SMTEncoding.Encode.fst"
let _83_2956 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1819 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1820 "FStar.SMTEncoding.Encode.fst"
let _83_2959 = (let _172_2214 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _172_2214))
in (
# 1821 "FStar.SMTEncoding.Encode.fst"
let _83_2961 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1823 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1824 "FStar.SMTEncoding.Encode.fst"
let _83_2964 = (mark_env ())
in (
# 1825 "FStar.SMTEncoding.Encode.fst"
let _83_2966 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1827 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1828 "FStar.SMTEncoding.Encode.fst"
let _83_2969 = (reset_mark_env ())
in (
# 1829 "FStar.SMTEncoding.Encode.fst"
let _83_2971 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1831 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1832 "FStar.SMTEncoding.Encode.fst"
let _83_2974 = (commit_mark_env ())
in (
# 1833 "FStar.SMTEncoding.Encode.fst"
let _83_2976 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1835 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1836 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _172_2230 = (let _172_2229 = (let _172_2228 = (let _172_2227 = (let _172_2226 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _172_2226 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _172_2227 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _172_2228))
in FStar_SMTEncoding_Term.Caption (_172_2229))
in (_172_2230)::decls)
end else begin
decls
end)
in (
# 1840 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1841 "FStar.SMTEncoding.Encode.fst"
let _83_2985 = (encode_sigelt env se)
in (match (_83_2985) with
| (decls, env) -> begin
(
# 1842 "FStar.SMTEncoding.Encode.fst"
let _83_2986 = (set_env env)
in (let _172_2231 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _172_2231)))
end)))))

# 1845 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1846 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1847 "FStar.SMTEncoding.Encode.fst"
let _83_2991 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _172_2236 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _172_2236))
end else begin
()
end
in (
# 1849 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1850 "FStar.SMTEncoding.Encode.fst"
let _83_2998 = (encode_signature (
# 1850 "FStar.SMTEncoding.Encode.fst"
let _83_2994 = env
in {bindings = _83_2994.bindings; depth = _83_2994.depth; tcenv = _83_2994.tcenv; warn = false; cache = _83_2994.cache; nolabels = _83_2994.nolabels; use_zfuel_name = _83_2994.use_zfuel_name; encode_non_total_function_typ = _83_2994.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_83_2998) with
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
let _83_3004 = (set_env (
# 1856 "FStar.SMTEncoding.Encode.fst"
let _83_3002 = env
in {bindings = _83_3002.bindings; depth = _83_3002.depth; tcenv = _83_3002.tcenv; warn = true; cache = _83_3002.cache; nolabels = _83_3002.nolabels; use_zfuel_name = _83_3002.use_zfuel_name; encode_non_total_function_typ = _83_3002.encode_non_total_function_typ}))
in (
# 1857 "FStar.SMTEncoding.Encode.fst"
let _83_3006 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1858 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1861 "FStar.SMTEncoding.Encode.fst"
let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (
# 1862 "FStar.SMTEncoding.Encode.fst"
let _83_3012 = (let _172_2255 = (let _172_2254 = (let _172_2253 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _172_2253))
in (FStar_Util.format1 "Starting query at %s" _172_2254))
in (push _172_2255))
in (
# 1863 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _83_3015 -> (match (()) with
| () -> begin
(let _172_2260 = (let _172_2259 = (let _172_2258 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _172_2258))
in (FStar_Util.format1 "Ending query at %s" _172_2259))
in (pop _172_2260))
end))
in (
# 1864 "FStar.SMTEncoding.Encode.fst"
let _83_3069 = (
# 1865 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1866 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1867 "FStar.SMTEncoding.Encode.fst"
let _83_3039 = (
# 1868 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1870 "FStar.SMTEncoding.Encode.fst"
let _83_3028 = (aux rest)
in (match (_83_3028) with
| (out, rest) -> begin
(
# 1871 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _172_2266 = (let _172_2265 = (FStar_Syntax_Syntax.mk_binder (
# 1872 "FStar.SMTEncoding.Encode.fst"
let _83_3030 = x
in {FStar_Syntax_Syntax.ppname = _83_3030.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _83_3030.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_172_2265)::out)
in (_172_2266, rest)))
end))
end
| _83_3033 -> begin
([], bindings)
end))
in (
# 1874 "FStar.SMTEncoding.Encode.fst"
let _83_3036 = (aux bindings)
in (match (_83_3036) with
| (closing, bindings) -> begin
(let _172_2267 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_172_2267, bindings))
end)))
in (match (_83_3039) with
| (q, bindings) -> begin
(
# 1876 "FStar.SMTEncoding.Encode.fst"
let _83_3048 = (let _172_2269 = (FStar_List.filter (fun _83_21 -> (match (_83_21) with
| FStar_TypeChecker_Env.Binding_sig (_83_3042) -> begin
false
end
| _83_3045 -> begin
true
end)) bindings)
in (encode_env_bindings env _172_2269))
in (match (_83_3048) with
| (env_decls, env) -> begin
(
# 1877 "FStar.SMTEncoding.Encode.fst"
let _83_3049 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _172_2270 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _172_2270))
end else begin
()
end
in (
# 1880 "FStar.SMTEncoding.Encode.fst"
let _83_3053 = (encode_formula q env)
in (match (_83_3053) with
| (phi, qdecls) -> begin
(
# 1881 "FStar.SMTEncoding.Encode.fst"
let _83_3058 = (let _172_2271 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _172_2271 phi))
in (match (_83_3058) with
| (phi, labels, _83_3057) -> begin
(
# 1882 "FStar.SMTEncoding.Encode.fst"
let _83_3061 = (encode_labels labels)
in (match (_83_3061) with
| (label_prefix, label_suffix) -> begin
(
# 1883 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1887 "FStar.SMTEncoding.Encode.fst"
let qry = (let _172_2273 = (let _172_2272 = (FStar_SMTEncoding_Term.mkNot phi)
in (_172_2272, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_172_2273))
in (
# 1888 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_83_3069) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _83_3076); FStar_SMTEncoding_Term.hash = _83_3073; FStar_SMTEncoding_Term.freevars = _83_3071}, _83_3081) -> begin
(
# 1891 "FStar.SMTEncoding.Encode.fst"
let _83_3084 = (pop ())
in ())
end
| _83_3087 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1892 "FStar.SMTEncoding.Encode.fst"
let _83_3088 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _83_3092) -> begin
(
# 1894 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1895 "FStar.SMTEncoding.Encode.fst"
let _83_3096 = (FStar_SMTEncoding_ErrorReporting.askZ3_and_report_errors tcenv fresh labels prefix qry suffix)
in (pop ())))
end
| _83_3099 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1901 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1902 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1903 "FStar.SMTEncoding.Encode.fst"
let _83_3103 = (push "query")
in (
# 1904 "FStar.SMTEncoding.Encode.fst"
let _83_3108 = (encode_formula q env)
in (match (_83_3108) with
| (f, _83_3107) -> begin
(
# 1905 "FStar.SMTEncoding.Encode.fst"
let _83_3109 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _83_3113) -> begin
true
end
| _83_3117 -> begin
false
end))
end)))))

# 1910 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1924 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _83_3118 -> ()); FStar_TypeChecker_Env.push = (fun _83_3120 -> ()); FStar_TypeChecker_Env.pop = (fun _83_3122 -> ()); FStar_TypeChecker_Env.mark = (fun _83_3124 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _83_3126 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _83_3128 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _83_3130 _83_3132 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _83_3134 _83_3136 -> ()); FStar_TypeChecker_Env.solve = (fun _83_3138 _83_3140 _83_3142 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _83_3144 _83_3146 -> false); FStar_TypeChecker_Env.finish = (fun _83_3148 -> ()); FStar_TypeChecker_Env.refresh = (fun _83_3149 -> ())}





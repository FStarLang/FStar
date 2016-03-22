
open Prims
# 34 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 35 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _78_27 -> (match (_78_27) with
| (a, b) -> begin
(a, b, c)
end))

# 36 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _78_1 -> (match (_78_1) with
| (FStar_Util.Inl (_78_31), _78_34) -> begin
false
end
| _78_37 -> begin
true
end)) args))

# 37 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _162_13 = (let _162_12 = (let _162_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _162_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _162_12))
in Some (_162_13))
end))

# 42 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 43 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _78_46 = a
in (let _162_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _162_20; FStar_Syntax_Syntax.index = _78_46.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _78_46.FStar_Syntax_Syntax.sort}))
in (let _162_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _162_21))))

# 46 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _78_53 -> (match (()) with
| () -> begin
(let _162_31 = (let _162_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _162_30 lid.FStar_Ident.str))
in (FStar_All.failwith _162_31))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _78_57 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_78_57) with
| (_78_55, t) -> begin
(match ((let _162_32 = (FStar_Syntax_Subst.compress t)
in _162_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _78_65 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_78_65) with
| (binders, _78_64) -> begin
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
| _78_68 -> begin
(fail ())
end)
end))))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _162_38 = (let _162_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _162_37))
in (FStar_All.pipe_left escape _162_38)))

# 58 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _162_44 = (let _162_43 = (mk_term_projector_name lid a)
in (_162_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _162_44)))

# 60 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _162_50 = (let _162_49 = (mk_term_projector_name_by_pos lid i)
in (_162_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _162_50)))

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
let new_scope = (fun _78_92 -> (match (()) with
| () -> begin
(let _162_154 = (FStar_Util.smap_create 100)
in (let _162_153 = (FStar_Util.smap_create 100)
in (_162_154, _162_153)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _162_156 = (let _162_155 = (new_scope ())
in (_162_155)::[])
in (FStar_Util.mk_ref _162_156))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _162_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _162_160 (fun _78_100 -> (match (_78_100) with
| (names, _78_99) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_78_103) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _78_105 = (FStar_Util.incr ctr)
in (let _162_162 = (let _162_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _162_161))
in (Prims.strcat (Prims.strcat y "__") _162_162)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _162_164 = (let _162_163 = (FStar_ST.read scopes)
in (FStar_List.hd _162_163))
in (FStar_All.pipe_left Prims.fst _162_164))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _78_109 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _162_171 = (let _162_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _162_169 "__"))
in (let _162_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _162_171 _162_170))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _78_117 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _78_118 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _162_179 = (let _162_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _162_178))
in (FStar_Util.format2 "%s_%s" pfx _162_179)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _162_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _162_183 (fun _78_127 -> (match (_78_127) with
| (_78_125, strings) -> begin
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
let f = (let _162_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _162_184))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _162_186 = (let _162_185 = (FStar_ST.read scopes)
in (FStar_List.hd _162_185))
in (FStar_All.pipe_left Prims.snd _162_186))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _78_134 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _78_137 -> (match (()) with
| () -> begin
(let _162_191 = (let _162_190 = (new_scope ())
in (let _162_189 = (FStar_ST.read scopes)
in (_162_190)::_162_189))
in (FStar_ST.op_Colon_Equals scopes _162_191))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _78_139 -> (match (()) with
| () -> begin
(let _162_195 = (let _162_194 = (FStar_ST.read scopes)
in (FStar_List.tl _162_194))
in (FStar_ST.op_Colon_Equals scopes _162_195))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _78_141 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _78_143 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _78_145 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _78_158 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _78_163 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _78_166 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 122 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _78_168 = x
in (let _162_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _162_210; FStar_Syntax_Syntax.index = _78_168.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _78_168.FStar_Syntax_Syntax.sort})))

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
| Binding_var (_78_172) -> begin
_78_172
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_78_175) -> begin
_78_175
end))

# 131 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 132 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 142 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _162_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _78_2 -> (match (_78_2) with
| Binding_var (x, _78_190) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _78_195, _78_197, _78_199) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _162_268 (FStar_String.concat ", "))))

# 147 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_162_278))
end else begin
None
end)

# 154 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _162_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _162_283))))

# 158 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _162_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _162_288))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _78_213 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _78_213.tcenv; warn = _78_213.warn; cache = _78_213.cache; nolabels = _78_213.nolabels; use_zfuel_name = _78_213.use_zfuel_name; encode_non_total_function_typ = _78_213.encode_non_total_function_typ})))))

# 162 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _78_219 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _78_219.depth; tcenv = _78_219.tcenv; warn = _78_219.warn; cache = _78_219.cache; nolabels = _78_219.nolabels; use_zfuel_name = _78_219.use_zfuel_name; encode_non_total_function_typ = _78_219.encode_non_total_function_typ})))))

# 166 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _78_224 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _78_224.depth; tcenv = _78_224.tcenv; warn = _78_224.warn; cache = _78_224.cache; nolabels = _78_224.nolabels; use_zfuel_name = _78_224.use_zfuel_name; encode_non_total_function_typ = _78_224.encode_non_total_function_typ}))

# 168 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _78_3 -> (match (_78_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _78_234 -> begin
None
end)))) with
| None -> begin
(let _162_305 = (let _162_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _162_304))
in (FStar_All.failwith _162_305))
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
in (let _162_316 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _78_244 = env
in (let _162_315 = (let _162_314 = (let _162_313 = (let _162_312 = (let _162_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _162_310 -> Some (_162_310)) _162_311))
in (x, fname, _162_312, None))
in Binding_fvar (_162_313))
in (_162_314)::env.bindings)
in {bindings = _162_315; depth = _78_244.depth; tcenv = _78_244.tcenv; warn = _78_244.warn; cache = _78_244.cache; nolabels = _78_244.nolabels; use_zfuel_name = _78_244.use_zfuel_name; encode_non_total_function_typ = _78_244.encode_non_total_function_typ}))
in (fname, ftok, _162_316)))))

# 179 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _78_4 -> (match (_78_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _78_256 -> begin
None
end))))

# 181 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _162_327 = (let _162_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _162_326))
in (FStar_All.failwith _162_327))
end
| Some (s) -> begin
s
end))

# 185 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _78_266 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _78_266.depth; tcenv = _78_266.tcenv; warn = _78_266.warn; cache = _78_266.cache; nolabels = _78_266.nolabels; use_zfuel_name = _78_266.use_zfuel_name; encode_non_total_function_typ = _78_266.encode_non_total_function_typ}))

# 187 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _78_275 = (lookup_lid env x)
in (match (_78_275) with
| (t1, t2, _78_274) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _162_344 = (let _162_343 = (let _162_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_162_342)::[])
in (f, _162_343))
in (FStar_SMTEncoding_Term.mkApp _162_344))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _78_277 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _78_277.depth; tcenv = _78_277.tcenv; warn = _78_277.warn; cache = _78_277.cache; nolabels = _78_277.nolabels; use_zfuel_name = _78_277.use_zfuel_name; encode_non_total_function_typ = _78_277.encode_non_total_function_typ}))
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
| _78_290 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_78_294, fuel::[]) -> begin
if (let _162_350 = (let _162_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _162_349 Prims.fst))
in (FStar_Util.starts_with _162_350 "fuel")) then begin
(let _162_353 = (let _162_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _162_352 fuel))
in (FStar_All.pipe_left (fun _162_351 -> Some (_162_351)) _162_353))
end else begin
Some (t)
end
end
| _78_300 -> begin
Some (t)
end)
end
| _78_302 -> begin
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
(let _162_357 = (let _162_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _162_356))
in (FStar_All.failwith _162_357))
end))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _78_315 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_78_315) with
| (x, _78_312, _78_314) -> begin
x
end)))

# 213 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _78_321 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_78_321) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _78_325; FStar_SMTEncoding_Term.freevars = _78_323}) when env.use_zfuel_name -> begin
(g, zf)
end
| _78_333 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _78_343 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 225 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _78_5 -> (match (_78_5) with
| Binding_fvar (_78_348, nm', tok, _78_352) when (nm = nm') -> begin
tok
end
| _78_356 -> begin
None
end))))

# 234 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _78_361 -> (match (_78_361) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _78_363 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _78_366 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_366) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _78_376 -> begin
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
(let _162_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _162_374))
end
| _78_389 -> begin
(let _162_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _162_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _78_392 -> begin
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
(let _162_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _162_381 FStar_Option.isNone))
end
| _78_431 -> begin
false
end)))

# 269 "FStar.SMTEncoding.Encode.fst"
let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _162_386 = (FStar_Syntax_Util.un_uinst t)
in _162_386.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_78_435) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _162_387 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _162_387 FStar_Option.isSome))
end
| _78_440 -> begin
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
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _162_400 = (let _162_398 = (FStar_Syntax_Syntax.null_binder t)
in (_162_398)::[])
in (let _162_399 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _162_400 _162_399 None))))

# 284 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _162_407 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _162_407))
end
| s -> begin
(
# 287 "FStar.SMTEncoding.Encode.fst"
let _78_452 = ()
in (let _162_408 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _162_408)))
end)) e)))

# 288 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 290 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _78_6 -> (match (_78_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _78_462 -> begin
false
end))

# 295 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 296 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _78_473; FStar_SMTEncoding_Term.freevars = _78_471}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _78_491) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _78_498 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_78_500, []) -> begin
(
# 307 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _78_506 -> begin
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
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _78_7 -> (match (_78_7) with
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
(let _162_462 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _162_462))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _162_463 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _162_463))
end
| FStar_Const.Const_int (i) -> begin
(let _162_464 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _162_464))
end
| FStar_Const.Const_int32 (i) -> begin
(let _162_468 = (let _162_467 = (let _162_466 = (let _162_465 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _162_465))
in (_162_466)::[])
in ("FStar.Int32.Int32", _162_467))
in (FStar_SMTEncoding_Term.mkApp _162_468))
end
| FStar_Const.Const_string (bytes, _78_528) -> begin
(let _162_469 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _162_469))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _162_471 = (let _162_470 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _162_470))
in (FStar_All.failwith _162_471))
end))

# 361 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 362 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 363 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_78_542) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_78_545) -> begin
(let _162_480 = (FStar_Syntax_Util.unrefine t)
in (aux true _162_480))
end
| _78_548 -> begin
if norm then begin
(let _162_481 = (whnf env t)
in (aux false _162_481))
end else begin
(let _162_484 = (let _162_483 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _162_482 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _162_483 _162_482)))
in (FStar_All.failwith _162_484))
end
end)))
in (aux true t0)))

# 372 "FStar.SMTEncoding.Encode.fst"
let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (
# 373 "FStar.SMTEncoding.Encode.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _78_556 -> begin
(let _162_487 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _162_487))
end)))

# 379 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 386 "FStar.SMTEncoding.Encode.fst"
let _78_560 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_535 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _162_535))
end else begin
()
end
in (
# 388 "FStar.SMTEncoding.Encode.fst"
let _78_588 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _78_567 b -> (match (_78_567) with
| (vars, guards, env, decls, names) -> begin
(
# 389 "FStar.SMTEncoding.Encode.fst"
let _78_582 = (
# 390 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 391 "FStar.SMTEncoding.Encode.fst"
let _78_573 = (gen_term_var env x)
in (match (_78_573) with
| (xxsym, xx, env') -> begin
(
# 392 "FStar.SMTEncoding.Encode.fst"
let _78_576 = (let _162_538 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _162_538 env xx))
in (match (_78_576) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_78_582) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_78_588) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 407 "FStar.SMTEncoding.Encode.fst"
let _78_595 = (encode_term t env)
in (match (_78_595) with
| (t, decls) -> begin
(let _162_543 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_162_543, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 411 "FStar.SMTEncoding.Encode.fst"
let _78_602 = (encode_term t env)
in (match (_78_602) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _162_548 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_162_548, decls))
end
| Some (f) -> begin
(let _162_549 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_162_549, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 419 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 420 "FStar.SMTEncoding.Encode.fst"
let _78_609 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _162_554 = (FStar_Syntax_Print.tag_of_term t)
in (let _162_553 = (FStar_Syntax_Print.tag_of_term t0)
in (let _162_552 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _162_554 _162_553 _162_552))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _162_559 = (let _162_558 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _162_557 = (FStar_Syntax_Print.tag_of_term t0)
in (let _162_556 = (FStar_Syntax_Print.term_to_string t0)
in (let _162_555 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _162_558 _162_557 _162_556 _162_555)))))
in (FStar_All.failwith _162_559))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _162_561 = (let _162_560 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _162_560))
in (FStar_All.failwith _162_561))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _78_620) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _78_625) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 436 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _162_562 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_162_562, []))
end
| FStar_Syntax_Syntax.Tm_type (_78_634) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _78_638) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _162_563 = (encode_const c)
in (_162_563, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 452 "FStar.SMTEncoding.Encode.fst"
let _78_649 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_78_649) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 456 "FStar.SMTEncoding.Encode.fst"
let _78_656 = (encode_binders None binders env)
in (match (_78_656) with
| (vars, guards, env', decls, _78_655) -> begin
(
# 457 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _162_564 = (varops.fresh "f")
in (_162_564, FStar_SMTEncoding_Term.Term_sort))
in (
# 458 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 459 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 460 "FStar.SMTEncoding.Encode.fst"
let _78_662 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_78_662) with
| (pre_opt, res_t) -> begin
(
# 461 "FStar.SMTEncoding.Encode.fst"
let _78_665 = (encode_term_pred None res_t env' app)
in (match (_78_665) with
| (res_pred, decls') -> begin
(
# 462 "FStar.SMTEncoding.Encode.fst"
let _78_674 = (match (pre_opt) with
| None -> begin
(let _162_565 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_162_565, decls))
end
| Some (pre) -> begin
(
# 465 "FStar.SMTEncoding.Encode.fst"
let _78_671 = (encode_formula pre env')
in (match (_78_671) with
| (guard, decls0) -> begin
(let _162_566 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_162_566, (FStar_List.append decls decls0)))
end))
end)
in (match (_78_674) with
| (guards, guard_decls) -> begin
(
# 467 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _162_568 = (let _162_567 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _162_567))
in (FStar_SMTEncoding_Term.mkForall _162_568))
in (
# 472 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _162_570 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _162_570 (FStar_List.filter (fun _78_679 -> (match (_78_679) with
| (x, _78_678) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 473 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _78_685) -> begin
(let _162_573 = (let _162_572 = (let _162_571 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _162_571))
in (FStar_SMTEncoding_Term.mkApp _162_572))
in (_162_573, []))
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
(let _162_574 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_162_574))
end else begin
None
end
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let t = (let _162_576 = (let _162_575 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _162_575))
in (FStar_SMTEncoding_Term.mkApp _162_576))
in (
# 489 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 491 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _162_578 = (let _162_577 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_162_577, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_162_578))
in (
# 493 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 495 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _162_585 = (let _162_584 = (let _162_583 = (let _162_582 = (let _162_581 = (let _162_580 = (let _162_579 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _162_579))
in (f_has_t, _162_580))
in (FStar_SMTEncoding_Term.mkImp _162_581))
in (((f_has_t)::[])::[], (fsym)::cvars, _162_582))
in (mkForall_fuel _162_583))
in (_162_584, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_162_585))
in (
# 496 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _162_589 = (let _162_588 = (let _162_587 = (let _162_586 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _162_586))
in (FStar_SMTEncoding_Term.mkForall _162_587))
in (_162_588, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_162_589))
in (
# 499 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 500 "FStar.SMTEncoding.Encode.fst"
let _78_701 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
let t_kinding = (let _162_591 = (let _162_590 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_162_590, None))
in FStar_SMTEncoding_Term.Assume (_162_591))
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
let t_interp = (let _162_598 = (let _162_597 = (let _162_596 = (let _162_595 = (let _162_594 = (let _162_593 = (let _162_592 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _162_592))
in (f_has_t, _162_593))
in (FStar_SMTEncoding_Term.mkImp _162_594))
in (((f_has_t)::[])::[], (fsym)::[], _162_595))
in (mkForall_fuel _162_596))
in (_162_597, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_162_598))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_78_712) -> begin
(
# 518 "FStar.SMTEncoding.Encode.fst"
let _78_732 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _78_719; FStar_Syntax_Syntax.pos = _78_717; FStar_Syntax_Syntax.vars = _78_715} -> begin
(
# 520 "FStar.SMTEncoding.Encode.fst"
let _78_727 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_78_727) with
| (b, f) -> begin
(let _162_600 = (let _162_599 = (FStar_List.hd b)
in (Prims.fst _162_599))
in (_162_600, f))
end))
end
| _78_729 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_78_732) with
| (x, f) -> begin
(
# 524 "FStar.SMTEncoding.Encode.fst"
let _78_735 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_78_735) with
| (base_t, decls) -> begin
(
# 525 "FStar.SMTEncoding.Encode.fst"
let _78_739 = (gen_term_var env x)
in (match (_78_739) with
| (x, xtm, env') -> begin
(
# 526 "FStar.SMTEncoding.Encode.fst"
let _78_742 = (encode_formula f env')
in (match (_78_742) with
| (refinement, decls') -> begin
(
# 528 "FStar.SMTEncoding.Encode.fst"
let _78_745 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_745) with
| (fsym, fterm) -> begin
(
# 530 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _162_602 = (let _162_601 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_162_601, refinement))
in (FStar_SMTEncoding_Term.mkAnd _162_602))
in (
# 532 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _162_604 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _162_604 (FStar_List.filter (fun _78_750 -> (match (_78_750) with
| (y, _78_749) -> begin
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
| Some (t, _78_757, _78_759) -> begin
(let _162_607 = (let _162_606 = (let _162_605 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _162_605))
in (FStar_SMTEncoding_Term.mkApp _162_606))
in (_162_607, []))
end
| None -> begin
(
# 542 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Typ_refine")
in (
# 543 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 544 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 545 "FStar.SMTEncoding.Encode.fst"
let t = (let _162_609 = (let _162_608 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _162_608))
in (FStar_SMTEncoding_Term.mkApp _162_609))
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
let assumption = (let _162_611 = (let _162_610 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _162_610))
in (FStar_SMTEncoding_Term.mkForall _162_611))
in (
# 553 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _162_618 = (let _162_617 = (let _162_616 = (let _162_615 = (let _162_614 = (let _162_613 = (let _162_612 = (FStar_Syntax_Print.term_to_string t0)
in Some (_162_612))
in (assumption, _162_613))
in FStar_SMTEncoding_Term.Assume (_162_614))
in (_162_615)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, None)))::_162_616)
in (tdecl)::_162_617)
in (FStar_List.append (FStar_List.append decls decls') _162_618))
in (
# 558 "FStar.SMTEncoding.Encode.fst"
let _78_772 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
let ttm = (let _162_619 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _162_619))
in (
# 564 "FStar.SMTEncoding.Encode.fst"
let _78_781 = (encode_term_pred None k env ttm)
in (match (_78_781) with
| (t_has_k, decls) -> begin
(
# 565 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_78_784) -> begin
(
# 569 "FStar.SMTEncoding.Encode.fst"
let _78_788 = (FStar_Syntax_Util.head_and_args t0)
in (match (_78_788) with
| (head, args_e) -> begin
(match ((let _162_621 = (let _162_620 = (FStar_Syntax_Subst.compress head)
in _162_620.FStar_Syntax_Syntax.n)
in (_162_621, args_e))) with
| (_78_790, _78_792) when (head_redex env head) -> begin
(let _162_622 = (whnf env t)
in (encode_term _162_622 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), _::(v1, _)::(v2, _)::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let _78_832 = (encode_term v1 env)
in (match (_78_832) with
| (v1, decls1) -> begin
(
# 577 "FStar.SMTEncoding.Encode.fst"
let _78_835 = (encode_term v2 env)
in (match (_78_835) with
| (v2, decls2) -> begin
(let _162_623 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_162_623, (FStar_List.append decls1 decls2)))
end))
end))
end
| _78_837 -> begin
(
# 581 "FStar.SMTEncoding.Encode.fst"
let _78_840 = (encode_args args_e env)
in (match (_78_840) with
| (args, decls) -> begin
(
# 583 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 584 "FStar.SMTEncoding.Encode.fst"
let _78_845 = (encode_term head env)
in (match (_78_845) with
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
let _78_854 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_78_854) with
| (formals, rest) -> begin
(
# 590 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _78_858 _78_862 -> (match ((_78_858, _78_862)) with
| ((bv, _78_857), (a, _78_861)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 591 "FStar.SMTEncoding.Encode.fst"
let ty = (let _162_628 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _162_628 (FStar_Syntax_Subst.subst subst)))
in (
# 592 "FStar.SMTEncoding.Encode.fst"
let _78_867 = (encode_term_pred None ty env app_tm)
in (match (_78_867) with
| (has_type, decls'') -> begin
(
# 593 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 594 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _162_630 = (let _162_629 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_162_629, None))
in FStar_SMTEncoding_Term.Assume (_162_630))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 598 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 599 "FStar.SMTEncoding.Encode.fst"
let _78_874 = (lookup_free_var_sym env fv)
in (match (_78_874) with
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
(let _162_634 = (let _162_633 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _162_633 Prims.snd))
in Some (_162_634))
end
| FStar_Syntax_Syntax.Tm_ascribed (_78_906, t, _78_909) -> begin
Some (t)
end
| _78_913 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 616 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _162_635 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _162_635))
in (
# 617 "FStar.SMTEncoding.Encode.fst"
let _78_921 = (curried_arrow_formals_comp head_type)
in (match (_78_921) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _78_937 -> begin
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
let _78_946 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_78_946) with
| (bs, body, opening) -> begin
(
# 632 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _78_948 -> (match (()) with
| () -> begin
(
# 633 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 634 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _162_638 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_162_638, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 639 "FStar.SMTEncoding.Encode.fst"
let _78_952 = (let _162_640 = (let _162_639 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _162_639))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _162_640))
in (fallback ()))
end
| Some (lc) -> begin
if (let _162_641 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _162_641)) then begin
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
let _78_964 = (encode_binders None bs env)
in (match (_78_964) with
| (vars, guards, envbody, decls, _78_963) -> begin
(
# 650 "FStar.SMTEncoding.Encode.fst"
let _78_967 = (encode_term body envbody)
in (match (_78_967) with
| (body, decls') -> begin
(
# 651 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _162_645 = (let _162_644 = (let _162_643 = (let _162_642 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_162_642, body))
in (FStar_SMTEncoding_Term.mkImp _162_643))
in ([], vars, _162_644))
in (FStar_SMTEncoding_Term.mkForall _162_645))
in (
# 652 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 653 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _78_973, _78_975) -> begin
(let _162_648 = (let _162_647 = (let _162_646 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _162_646))
in (FStar_SMTEncoding_Term.mkApp _162_647))
in (_162_648, []))
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
let f = (let _162_650 = (let _162_649 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _162_649))
in (FStar_SMTEncoding_Term.mkApp _162_650))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 667 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let _78_990 = (encode_term_pred None tfun env f)
in (match (_78_990) with
| (f_has_t, decls'') -> begin
(
# 669 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _162_652 = (let _162_651 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_162_651, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_162_652))
in (
# 671 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _162_659 = (let _162_658 = (let _162_657 = (let _162_656 = (let _162_655 = (let _162_654 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _162_653 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_162_654, _162_653)))
in (FStar_SMTEncoding_Term.mkImp _162_655))
in (((app)::[])::[], (FStar_List.append vars cvars), _162_656))
in (FStar_SMTEncoding_Term.mkForall _162_657))
in (_162_658, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_162_659))
in (
# 673 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 674 "FStar.SMTEncoding.Encode.fst"
let _78_994 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_78_997, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_78_1009); FStar_Syntax_Syntax.lbunivs = _78_1007; FStar_Syntax_Syntax.lbtyp = _78_1005; FStar_Syntax_Syntax.lbeff = _78_1003; FStar_Syntax_Syntax.lbdef = _78_1001}::_78_999), _78_1015) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _78_1024; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _78_1021; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_78_1034) -> begin
(
# 687 "FStar.SMTEncoding.Encode.fst"
let _78_1036 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 688 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 689 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _162_660 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_162_660, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 696 "FStar.SMTEncoding.Encode.fst"
let _78_1052 = (encode_term e1 env)
in (match (_78_1052) with
| (ee1, decls1) -> begin
(
# 697 "FStar.SMTEncoding.Encode.fst"
let _78_1055 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_78_1055) with
| (xs, e2) -> begin
(
# 698 "FStar.SMTEncoding.Encode.fst"
let _78_1059 = (FStar_List.hd xs)
in (match (_78_1059) with
| (x, _78_1058) -> begin
(
# 699 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 700 "FStar.SMTEncoding.Encode.fst"
let _78_1063 = (encode_body e2 env')
in (match (_78_1063) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 704 "FStar.SMTEncoding.Encode.fst"
let _78_1071 = (encode_term e env)
in (match (_78_1071) with
| (scr, decls) -> begin
(
# 705 "FStar.SMTEncoding.Encode.fst"
let _78_1108 = (FStar_List.fold_right (fun b _78_1075 -> (match (_78_1075) with
| (else_case, decls) -> begin
(
# 706 "FStar.SMTEncoding.Encode.fst"
let _78_1079 = (FStar_Syntax_Subst.open_branch b)
in (match (_78_1079) with
| (p, w, br) -> begin
(
# 707 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _78_1083 _78_1086 -> (match ((_78_1083, _78_1086)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 709 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 710 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 711 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _78_1092 -> (match (_78_1092) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 712 "FStar.SMTEncoding.Encode.fst"
let _78_1102 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 715 "FStar.SMTEncoding.Encode.fst"
let _78_1099 = (encode_term w env)
in (match (_78_1099) with
| (w, decls2) -> begin
(let _162_694 = (let _162_693 = (let _162_692 = (let _162_691 = (let _162_690 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _162_690))
in (FStar_SMTEncoding_Term.mkEq _162_691))
in (guard, _162_692))
in (FStar_SMTEncoding_Term.mkAnd _162_693))
in (_162_694, decls2))
end))
end)
in (match (_78_1102) with
| (guard, decls2) -> begin
(
# 717 "FStar.SMTEncoding.Encode.fst"
let _78_1105 = (encode_br br env)
in (match (_78_1105) with
| (br, decls3) -> begin
(let _162_695 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_162_695, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_78_1108) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _78_1114 -> begin
(let _162_698 = (encode_one_pat env pat)
in (_162_698)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 731 "FStar.SMTEncoding.Encode.fst"
let _78_1117 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_701 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _162_701))
end else begin
()
end
in (
# 732 "FStar.SMTEncoding.Encode.fst"
let _78_1121 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_78_1121) with
| (vars, pat_term) -> begin
(
# 734 "FStar.SMTEncoding.Encode.fst"
let _78_1133 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _78_1124 v -> (match (_78_1124) with
| (env, vars) -> begin
(
# 735 "FStar.SMTEncoding.Encode.fst"
let _78_1130 = (gen_term_var env v)
in (match (_78_1130) with
| (xx, _78_1128, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_78_1133) with
| (env, vars) -> begin
(
# 738 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_78_1138) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _162_709 = (let _162_708 = (encode_const c)
in (scrutinee, _162_708))
in (FStar_SMTEncoding_Term.mkEq _162_709))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(
# 746 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (
# 747 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _78_1160 -> (match (_78_1160) with
| (arg, _78_1159) -> begin
(
# 748 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _162_712 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _162_712)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 752 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_78_1167) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_78_1177) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _162_720 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _78_1187 -> (match (_78_1187) with
| (arg, _78_1186) -> begin
(
# 764 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _162_719 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _162_719)))
end))))
in (FStar_All.pipe_right _162_720 FStar_List.flatten))
end))
in (
# 768 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _78_1190 -> (match (()) with
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
let _78_1206 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _78_1196 _78_1200 -> (match ((_78_1196, _78_1200)) with
| ((tms, decls), (t, _78_1199)) -> begin
(
# 781 "FStar.SMTEncoding.Encode.fst"
let _78_1203 = (encode_term t env)
in (match (_78_1203) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_78_1206) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 787 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let _78_1215 = (let _162_733 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _162_733))
in (match (_78_1215) with
| (head, args) -> begin
(match ((let _162_735 = (let _162_734 = (FStar_Syntax_Util.un_uinst head)
in _162_734.FStar_Syntax_Syntax.n)
in (_162_735, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _78_1219) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _78_1232::(hd, _78_1229)::(tl, _78_1225)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _162_736 = (list_elements tl)
in (hd)::_162_736)
end
| _78_1236 -> begin
(
# 793 "FStar.SMTEncoding.Encode.fst"
let _78_1237 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 795 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 796 "FStar.SMTEncoding.Encode.fst"
let _78_1243 = (let _162_739 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _162_739 FStar_Syntax_Util.head_and_args))
in (match (_78_1243) with
| (head, args) -> begin
(match ((let _162_741 = (let _162_740 = (FStar_Syntax_Util.un_uinst head)
in _162_740.FStar_Syntax_Syntax.n)
in (_162_741, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_78_1251, _78_1253)::(e, _78_1248)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _78_1261)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _78_1266 -> begin
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
let _78_1274 = (let _162_746 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _162_746 FStar_Syntax_Util.head_and_args))
in (match (_78_1274) with
| (head, args) -> begin
(match ((let _162_748 = (let _162_747 = (FStar_Syntax_Util.un_uinst head)
in _162_747.FStar_Syntax_Syntax.n)
in (_162_748, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _78_1279)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _78_1284 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _162_751 = (list_elements e)
in (FStar_All.pipe_right _162_751 (FStar_List.map (fun branch -> (let _162_750 = (list_elements branch)
in (FStar_All.pipe_right _162_750 (FStar_List.map one_pat)))))))
end
| _78_1291 -> begin
(let _162_752 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_162_752)::[])
end)
end
| _78_1293 -> begin
(let _162_753 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_162_753)::[])
end))))
in (
# 819 "FStar.SMTEncoding.Encode.fst"
let _78_1327 = (match ((let _162_754 = (FStar_Syntax_Subst.compress t)
in _162_754.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 821 "FStar.SMTEncoding.Encode.fst"
let _78_1300 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_78_1300) with
| (binders, c) -> begin
(
# 822 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _78_1312)::(post, _78_1308)::(pats, _78_1304)::[] -> begin
(
# 825 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _162_755 = (lemma_pats pats')
in (binders, pre, post, _162_755)))
end
| _78_1320 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _78_1322 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_78_1327) with
| (binders, pre, post, patterns) -> begin
(
# 833 "FStar.SMTEncoding.Encode.fst"
let _78_1334 = (encode_binders None binders env)
in (match (_78_1334) with
| (vars, guards, env, decls, _78_1333) -> begin
(
# 836 "FStar.SMTEncoding.Encode.fst"
let _78_1347 = (let _162_759 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 837 "FStar.SMTEncoding.Encode.fst"
let _78_1344 = (let _162_758 = (FStar_All.pipe_right branch (FStar_List.map (fun _78_1339 -> (match (_78_1339) with
| (t, _78_1338) -> begin
(encode_term t (
# 837 "FStar.SMTEncoding.Encode.fst"
let _78_1340 = env
in {bindings = _78_1340.bindings; depth = _78_1340.depth; tcenv = _78_1340.tcenv; warn = _78_1340.warn; cache = _78_1340.cache; nolabels = _78_1340.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _78_1340.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _162_758 FStar_List.unzip))
in (match (_78_1344) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _162_759 FStar_List.unzip))
in (match (_78_1347) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _162_762 = (let _162_761 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _162_761 e))
in (_162_762)::p))))
end
| _78_1357 -> begin
(
# 850 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _162_768 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_162_768)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _162_770 = (let _162_769 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _162_769 tl))
in (aux _162_770 vars))
end
| _78_1369 -> begin
pats
end))
in (let _162_771 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _162_771 vars)))
end)
end)
in (
# 857 "FStar.SMTEncoding.Encode.fst"
let env = (
# 857 "FStar.SMTEncoding.Encode.fst"
let _78_1371 = env
in {bindings = _78_1371.bindings; depth = _78_1371.depth; tcenv = _78_1371.tcenv; warn = _78_1371.warn; cache = _78_1371.cache; nolabels = true; use_zfuel_name = _78_1371.use_zfuel_name; encode_non_total_function_typ = _78_1371.encode_non_total_function_typ})
in (
# 858 "FStar.SMTEncoding.Encode.fst"
let _78_1376 = (let _162_772 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _162_772 env))
in (match (_78_1376) with
| (pre, decls'') -> begin
(
# 859 "FStar.SMTEncoding.Encode.fst"
let _78_1379 = (let _162_773 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _162_773 env))
in (match (_78_1379) with
| (post, decls''') -> begin
(
# 860 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _162_778 = (let _162_777 = (let _162_776 = (let _162_775 = (let _162_774 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_162_774, post))
in (FStar_SMTEncoding_Term.mkImp _162_775))
in (pats, vars, _162_776))
in (FStar_SMTEncoding_Term.mkForall _162_777))
in (_162_778, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 864 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 865 "FStar.SMTEncoding.Encode.fst"
let _78_1393 = (FStar_Util.fold_map (fun decls x -> (
# 865 "FStar.SMTEncoding.Encode.fst"
let _78_1390 = (encode_term (Prims.fst x) env)
in (match (_78_1390) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_78_1393) with
| (decls, args) -> begin
(let _162_796 = (f args)
in (_162_796, decls))
end)))
in (
# 868 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _78_1396 -> (f, []))
in (
# 869 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _162_810 = (FStar_List.hd l)
in (FStar_All.pipe_left f _162_810)))
in (
# 870 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _78_8 -> (match (_78_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _78_1407 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 874 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 875 "FStar.SMTEncoding.Encode.fst"
let _78_1424 = (FStar_List.fold_right (fun _78_1415 _78_1418 -> (match ((_78_1415, _78_1418)) with
| ((t, _78_1414), (phis, decls)) -> begin
(
# 877 "FStar.SMTEncoding.Encode.fst"
let _78_1421 = (encode_formula t env)
in (match (_78_1421) with
| (phi, decls') -> begin
((phi)::phis, (FStar_List.append decls' decls))
end))
end)) l ([], []))
in (match (_78_1424) with
| (phis, decls) -> begin
(let _162_835 = (f phis)
in (_162_835, decls))
end)))
in (
# 882 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _78_9 -> (match (_78_9) with
| _78_1431::_78_1429::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 886 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _78_10 -> (match (_78_10) with
| (lhs, _78_1442)::(rhs, _78_1438)::[] -> begin
(
# 888 "FStar.SMTEncoding.Encode.fst"
let _78_1447 = (encode_formula rhs env)
in (match (_78_1447) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _78_1450) -> begin
(l1, decls1)
end
| _78_1454 -> begin
(
# 892 "FStar.SMTEncoding.Encode.fst"
let _78_1457 = (encode_formula lhs env)
in (match (_78_1457) with
| (l2, decls2) -> begin
(let _162_840 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_162_840, (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _78_1459 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 897 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _78_11 -> (match (_78_11) with
| (guard, _78_1472)::(_then, _78_1468)::(_else, _78_1464)::[] -> begin
(
# 899 "FStar.SMTEncoding.Encode.fst"
let _78_1477 = (encode_formula guard env)
in (match (_78_1477) with
| (g, decls1) -> begin
(
# 900 "FStar.SMTEncoding.Encode.fst"
let _78_1480 = (encode_formula _then env)
in (match (_78_1480) with
| (t, decls2) -> begin
(
# 901 "FStar.SMTEncoding.Encode.fst"
let _78_1483 = (encode_formula _else env)
in (match (_78_1483) with
| (e, decls3) -> begin
(
# 902 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _78_1486 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 907 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _162_852 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _162_852)))
in (
# 908 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _162_905 = (let _162_861 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _162_861))
in (let _162_904 = (let _162_903 = (let _162_867 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _162_867))
in (let _162_902 = (let _162_901 = (let _162_900 = (let _162_876 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _162_876))
in (let _162_899 = (let _162_898 = (let _162_897 = (let _162_885 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _162_885))
in (_162_897)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_162_898)
in (_162_900)::_162_899))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_162_901)
in (_162_903)::_162_902))
in (_162_905)::_162_904))
in (
# 920 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 922 "FStar.SMTEncoding.Encode.fst"
let _78_1504 = (encode_formula phi' env)
in (match (_78_1504) with
| (phi, decls) -> begin
(let _162_908 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_162_908, decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 926 "FStar.SMTEncoding.Encode.fst"
let _78_1511 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_78_1511) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _78_1518; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _78_1515; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 930 "FStar.SMTEncoding.Encode.fst"
let _78_1529 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_78_1529) with
| (t, decls) -> begin
(t, decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 934 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _78_1546::(x, _78_1543)::(t, _78_1539)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(
# 937 "FStar.SMTEncoding.Encode.fst"
let _78_1551 = (encode_term x env)
in (match (_78_1551) with
| (x, decls) -> begin
(
# 938 "FStar.SMTEncoding.Encode.fst"
let _78_1554 = (encode_term t env)
in (match (_78_1554) with
| (t, decls') -> begin
(let _162_909 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_162_909, (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _78_1572::_78_1570::(r, _78_1567)::(msg, _78_1563)::(phi, _78_1559)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _162_913 = (let _162_910 = (FStar_Syntax_Subst.compress r)
in _162_910.FStar_Syntax_Syntax.n)
in (let _162_912 = (let _162_911 = (FStar_Syntax_Subst.compress msg)
in _162_911.FStar_Syntax_Syntax.n)
in (_162_913, _162_912)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _78_1580))) -> begin
(
# 944 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _78_1587 -> begin
(fallback phi)
end)
end
| _78_1589 when (head_redex env head) -> begin
(let _162_914 = (whnf env phi)
in (encode_formula _162_914 env))
end
| _78_1591 -> begin
(
# 954 "FStar.SMTEncoding.Encode.fst"
let _78_1594 = (encode_term phi env)
in (match (_78_1594) with
| (tt, decls) -> begin
(let _162_915 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_162_915, decls))
end))
end))
end
| _78_1596 -> begin
(
# 959 "FStar.SMTEncoding.Encode.fst"
let _78_1599 = (encode_term phi env)
in (match (_78_1599) with
| (tt, decls) -> begin
(let _162_916 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_162_916, decls))
end))
end))
in (
# 962 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 963 "FStar.SMTEncoding.Encode.fst"
let _78_1611 = (encode_binders None bs env)
in (match (_78_1611) with
| (vars, guards, env, decls, _78_1610) -> begin
(
# 964 "FStar.SMTEncoding.Encode.fst"
let _78_1624 = (let _162_928 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 965 "FStar.SMTEncoding.Encode.fst"
let _78_1621 = (let _162_927 = (FStar_All.pipe_right p (FStar_List.map (fun _78_1616 -> (match (_78_1616) with
| (t, _78_1615) -> begin
(encode_term t (
# 965 "FStar.SMTEncoding.Encode.fst"
let _78_1617 = env
in {bindings = _78_1617.bindings; depth = _78_1617.depth; tcenv = _78_1617.tcenv; warn = _78_1617.warn; cache = _78_1617.cache; nolabels = _78_1617.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _78_1617.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _162_927 FStar_List.unzip))
in (match (_78_1621) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _162_928 FStar_List.unzip))
in (match (_78_1624) with
| (pats, decls') -> begin
(
# 967 "FStar.SMTEncoding.Encode.fst"
let _78_1627 = (encode_formula body env)
in (match (_78_1627) with
| (body, decls'') -> begin
(let _162_929 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _162_929, body, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 970 "FStar.SMTEncoding.Encode.fst"
let _78_1628 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_930 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _162_930))
end else begin
()
end
in (
# 972 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _78_1640 -> (match (_78_1640) with
| (l, _78_1639) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_78_1643, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 982 "FStar.SMTEncoding.Encode.fst"
let _78_1653 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_947 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _162_947))
end else begin
()
end
in (
# 985 "FStar.SMTEncoding.Encode.fst"
let _78_1660 = (encode_q_body env vars pats body)
in (match (_78_1660) with
| (vars, pats, guard, body, decls) -> begin
(let _162_950 = (let _162_949 = (let _162_948 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _162_948))
in (FStar_SMTEncoding_Term.mkForall _162_949))
in (_162_950, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 989 "FStar.SMTEncoding.Encode.fst"
let _78_1672 = (encode_q_body env vars pats body)
in (match (_78_1672) with
| (vars, pats, guard, body, decls) -> begin
(let _162_953 = (let _162_952 = (let _162_951 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _162_951))
in (FStar_SMTEncoding_Term.mkExists _162_952))
in (_162_953, decls))
end))
end))))))))))))))))

# 998 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 998 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1004 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 1005 "FStar.SMTEncoding.Encode.fst"
let _78_1678 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_1678) with
| (asym, a) -> begin
(
# 1006 "FStar.SMTEncoding.Encode.fst"
let _78_1681 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_1681) with
| (xsym, x) -> begin
(
# 1007 "FStar.SMTEncoding.Encode.fst"
let _78_1684 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_1684) with
| (ysym, y) -> begin
(
# 1008 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 1009 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1010 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _162_996 = (let _162_995 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _162_995))
in (FStar_SMTEncoding_Term.mkApp _162_996))
in (
# 1011 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _162_998 = (let _162_997 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _162_997, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_162_998))
in (let _162_1004 = (let _162_1003 = (let _162_1002 = (let _162_1001 = (let _162_1000 = (let _162_999 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _162_999))
in (FStar_SMTEncoding_Term.mkForall _162_1000))
in (_162_1001, None))
in FStar_SMTEncoding_Term.Assume (_162_1002))
in (_162_1003)::[])
in (vname_decl)::_162_1004))))
in (
# 1014 "FStar.SMTEncoding.Encode.fst"
let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1015 "FStar.SMTEncoding.Encode.fst"
let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1016 "FStar.SMTEncoding.Encode.fst"
let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1017 "FStar.SMTEncoding.Encode.fst"
let prims = (let _162_1164 = (let _162_1013 = (let _162_1012 = (let _162_1011 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1011))
in (quant axy _162_1012))
in (FStar_Syntax_Const.op_Eq, _162_1013))
in (let _162_1163 = (let _162_1162 = (let _162_1020 = (let _162_1019 = (let _162_1018 = (let _162_1017 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _162_1017))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1018))
in (quant axy _162_1019))
in (FStar_Syntax_Const.op_notEq, _162_1020))
in (let _162_1161 = (let _162_1160 = (let _162_1029 = (let _162_1028 = (let _162_1027 = (let _162_1026 = (let _162_1025 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1024 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1025, _162_1024)))
in (FStar_SMTEncoding_Term.mkLT _162_1026))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1027))
in (quant xy _162_1028))
in (FStar_Syntax_Const.op_LT, _162_1029))
in (let _162_1159 = (let _162_1158 = (let _162_1038 = (let _162_1037 = (let _162_1036 = (let _162_1035 = (let _162_1034 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1033 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1034, _162_1033)))
in (FStar_SMTEncoding_Term.mkLTE _162_1035))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1036))
in (quant xy _162_1037))
in (FStar_Syntax_Const.op_LTE, _162_1038))
in (let _162_1157 = (let _162_1156 = (let _162_1047 = (let _162_1046 = (let _162_1045 = (let _162_1044 = (let _162_1043 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1042 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1043, _162_1042)))
in (FStar_SMTEncoding_Term.mkGT _162_1044))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1045))
in (quant xy _162_1046))
in (FStar_Syntax_Const.op_GT, _162_1047))
in (let _162_1155 = (let _162_1154 = (let _162_1056 = (let _162_1055 = (let _162_1054 = (let _162_1053 = (let _162_1052 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1051 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1052, _162_1051)))
in (FStar_SMTEncoding_Term.mkGTE _162_1053))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1054))
in (quant xy _162_1055))
in (FStar_Syntax_Const.op_GTE, _162_1056))
in (let _162_1153 = (let _162_1152 = (let _162_1065 = (let _162_1064 = (let _162_1063 = (let _162_1062 = (let _162_1061 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1060 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1061, _162_1060)))
in (FStar_SMTEncoding_Term.mkSub _162_1062))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1063))
in (quant xy _162_1064))
in (FStar_Syntax_Const.op_Subtraction, _162_1065))
in (let _162_1151 = (let _162_1150 = (let _162_1072 = (let _162_1071 = (let _162_1070 = (let _162_1069 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _162_1069))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1070))
in (quant qx _162_1071))
in (FStar_Syntax_Const.op_Minus, _162_1072))
in (let _162_1149 = (let _162_1148 = (let _162_1081 = (let _162_1080 = (let _162_1079 = (let _162_1078 = (let _162_1077 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1076 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1077, _162_1076)))
in (FStar_SMTEncoding_Term.mkAdd _162_1078))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1079))
in (quant xy _162_1080))
in (FStar_Syntax_Const.op_Addition, _162_1081))
in (let _162_1147 = (let _162_1146 = (let _162_1090 = (let _162_1089 = (let _162_1088 = (let _162_1087 = (let _162_1086 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1085 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1086, _162_1085)))
in (FStar_SMTEncoding_Term.mkMul _162_1087))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1088))
in (quant xy _162_1089))
in (FStar_Syntax_Const.op_Multiply, _162_1090))
in (let _162_1145 = (let _162_1144 = (let _162_1099 = (let _162_1098 = (let _162_1097 = (let _162_1096 = (let _162_1095 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1094 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1095, _162_1094)))
in (FStar_SMTEncoding_Term.mkDiv _162_1096))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1097))
in (quant xy _162_1098))
in (FStar_Syntax_Const.op_Division, _162_1099))
in (let _162_1143 = (let _162_1142 = (let _162_1108 = (let _162_1107 = (let _162_1106 = (let _162_1105 = (let _162_1104 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1103 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1104, _162_1103)))
in (FStar_SMTEncoding_Term.mkMod _162_1105))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1106))
in (quant xy _162_1107))
in (FStar_Syntax_Const.op_Modulus, _162_1108))
in (let _162_1141 = (let _162_1140 = (let _162_1117 = (let _162_1116 = (let _162_1115 = (let _162_1114 = (let _162_1113 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _162_1112 = (FStar_SMTEncoding_Term.unboxBool y)
in (_162_1113, _162_1112)))
in (FStar_SMTEncoding_Term.mkAnd _162_1114))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1115))
in (quant xy _162_1116))
in (FStar_Syntax_Const.op_And, _162_1117))
in (let _162_1139 = (let _162_1138 = (let _162_1126 = (let _162_1125 = (let _162_1124 = (let _162_1123 = (let _162_1122 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _162_1121 = (FStar_SMTEncoding_Term.unboxBool y)
in (_162_1122, _162_1121)))
in (FStar_SMTEncoding_Term.mkOr _162_1123))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1124))
in (quant xy _162_1125))
in (FStar_Syntax_Const.op_Or, _162_1126))
in (let _162_1137 = (let _162_1136 = (let _162_1133 = (let _162_1132 = (let _162_1131 = (let _162_1130 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _162_1130))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1131))
in (quant qx _162_1132))
in (FStar_Syntax_Const.op_Negation, _162_1133))
in (_162_1136)::[])
in (_162_1138)::_162_1137))
in (_162_1140)::_162_1139))
in (_162_1142)::_162_1141))
in (_162_1144)::_162_1143))
in (_162_1146)::_162_1145))
in (_162_1148)::_162_1147))
in (_162_1150)::_162_1149))
in (_162_1152)::_162_1151))
in (_162_1154)::_162_1153))
in (_162_1156)::_162_1155))
in (_162_1158)::_162_1157))
in (_162_1160)::_162_1159))
in (_162_1162)::_162_1161))
in (_162_1164)::_162_1163))
in (
# 1034 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _162_1196 = (FStar_All.pipe_right prims (FStar_List.filter (fun _78_1704 -> (match (_78_1704) with
| (l', _78_1703) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _162_1196 (FStar_List.collect (fun _78_1708 -> (match (_78_1708) with
| (_78_1706, b) -> begin
(b v)
end))))))
in (
# 1036 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _78_1714 -> (match (_78_1714) with
| (l', _78_1713) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1041 "FStar.SMTEncoding.Encode.fst"
let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (
# 1042 "FStar.SMTEncoding.Encode.fst"
let _78_1720 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_1720) with
| (xxsym, xx) -> begin
(
# 1043 "FStar.SMTEncoding.Encode.fst"
let _78_1723 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_1723) with
| (ffsym, ff) -> begin
(
# 1044 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _162_1222 = (let _162_1221 = (let _162_1220 = (let _162_1219 = (let _162_1218 = (let _162_1217 = (let _162_1216 = (let _162_1215 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _162_1215))
in (FStar_SMTEncoding_Term.mkEq _162_1216))
in (xx_has_type, _162_1217))
in (FStar_SMTEncoding_Term.mkImp _162_1218))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _162_1219))
in (FStar_SMTEncoding_Term.mkForall _162_1220))
in (_162_1221, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_162_1222)))
end))
end)))

# 1048 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1049 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1050 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1052 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1053 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1055 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun env nm tt -> (
# 1056 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _162_1243 = (let _162_1234 = (let _162_1233 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_162_1233, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_162_1234))
in (let _162_1242 = (let _162_1241 = (let _162_1240 = (let _162_1239 = (let _162_1238 = (let _162_1237 = (let _162_1236 = (let _162_1235 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _162_1235))
in (FStar_SMTEncoding_Term.mkImp _162_1236))
in (((typing_pred)::[])::[], (xx)::[], _162_1237))
in (mkForall_fuel _162_1238))
in (_162_1239, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1240))
in (_162_1241)::[])
in (_162_1243)::_162_1242))))
in (
# 1059 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun env nm tt -> (
# 1060 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1061 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1062 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _162_1266 = (let _162_1255 = (let _162_1254 = (let _162_1253 = (let _162_1252 = (let _162_1251 = (let _162_1250 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _162_1250))
in (FStar_SMTEncoding_Term.mkImp _162_1251))
in (((typing_pred)::[])::[], (xx)::[], _162_1252))
in (mkForall_fuel _162_1253))
in (_162_1254, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1255))
in (let _162_1265 = (let _162_1264 = (let _162_1263 = (let _162_1262 = (let _162_1261 = (let _162_1260 = (let _162_1257 = (let _162_1256 = (FStar_SMTEncoding_Term.boxBool b)
in (_162_1256)::[])
in (_162_1257)::[])
in (let _162_1259 = (let _162_1258 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _162_1258 tt))
in (_162_1260, (bb)::[], _162_1259)))
in (FStar_SMTEncoding_Term.mkForall _162_1261))
in (_162_1262, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_162_1263))
in (_162_1264)::[])
in (_162_1266)::_162_1265))))))
in (
# 1065 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun env nm tt -> (
# 1066 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1067 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1068 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1069 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1070 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1071 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1072 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _162_1280 = (let _162_1279 = (let _162_1278 = (let _162_1277 = (let _162_1276 = (let _162_1275 = (FStar_SMTEncoding_Term.boxInt a)
in (let _162_1274 = (let _162_1273 = (FStar_SMTEncoding_Term.boxInt b)
in (_162_1273)::[])
in (_162_1275)::_162_1274))
in (tt)::_162_1276)
in (tt)::_162_1277)
in ("Prims.Precedes", _162_1278))
in (FStar_SMTEncoding_Term.mkApp _162_1279))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _162_1280))
in (
# 1073 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _162_1281 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _162_1281))
in (let _162_1323 = (let _162_1287 = (let _162_1286 = (let _162_1285 = (let _162_1284 = (let _162_1283 = (let _162_1282 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _162_1282))
in (FStar_SMTEncoding_Term.mkImp _162_1283))
in (((typing_pred)::[])::[], (xx)::[], _162_1284))
in (mkForall_fuel _162_1285))
in (_162_1286, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1287))
in (let _162_1322 = (let _162_1321 = (let _162_1295 = (let _162_1294 = (let _162_1293 = (let _162_1292 = (let _162_1289 = (let _162_1288 = (FStar_SMTEncoding_Term.boxInt b)
in (_162_1288)::[])
in (_162_1289)::[])
in (let _162_1291 = (let _162_1290 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _162_1290 tt))
in (_162_1292, (bb)::[], _162_1291)))
in (FStar_SMTEncoding_Term.mkForall _162_1293))
in (_162_1294, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_162_1295))
in (let _162_1320 = (let _162_1319 = (let _162_1318 = (let _162_1317 = (let _162_1316 = (let _162_1315 = (let _162_1314 = (let _162_1313 = (let _162_1312 = (let _162_1311 = (let _162_1310 = (let _162_1309 = (let _162_1298 = (let _162_1297 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1296 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_162_1297, _162_1296)))
in (FStar_SMTEncoding_Term.mkGT _162_1298))
in (let _162_1308 = (let _162_1307 = (let _162_1301 = (let _162_1300 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _162_1299 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_162_1300, _162_1299)))
in (FStar_SMTEncoding_Term.mkGTE _162_1301))
in (let _162_1306 = (let _162_1305 = (let _162_1304 = (let _162_1303 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _162_1302 = (FStar_SMTEncoding_Term.unboxInt x)
in (_162_1303, _162_1302)))
in (FStar_SMTEncoding_Term.mkLT _162_1304))
in (_162_1305)::[])
in (_162_1307)::_162_1306))
in (_162_1309)::_162_1308))
in (typing_pred_y)::_162_1310)
in (typing_pred)::_162_1311)
in (FStar_SMTEncoding_Term.mk_and_l _162_1312))
in (_162_1313, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _162_1314))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _162_1315))
in (mkForall_fuel _162_1316))
in (_162_1317, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_162_1318))
in (_162_1319)::[])
in (_162_1321)::_162_1320))
in (_162_1323)::_162_1322)))))))))))
in (
# 1085 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun env nm tt -> (let _162_1334 = (let _162_1333 = (let _162_1332 = (let _162_1331 = (let _162_1330 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _162_1330))
in (FStar_SMTEncoding_Term.mkEq _162_1331))
in (_162_1332, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_162_1333))
in (_162_1334)::[]))
in (
# 1087 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun env nm tt -> (
# 1088 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1089 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1090 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _162_1357 = (let _162_1346 = (let _162_1345 = (let _162_1344 = (let _162_1343 = (let _162_1342 = (let _162_1341 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _162_1341))
in (FStar_SMTEncoding_Term.mkImp _162_1342))
in (((typing_pred)::[])::[], (xx)::[], _162_1343))
in (mkForall_fuel _162_1344))
in (_162_1345, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1346))
in (let _162_1356 = (let _162_1355 = (let _162_1354 = (let _162_1353 = (let _162_1352 = (let _162_1351 = (let _162_1348 = (let _162_1347 = (FStar_SMTEncoding_Term.boxString b)
in (_162_1347)::[])
in (_162_1348)::[])
in (let _162_1350 = (let _162_1349 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _162_1349 tt))
in (_162_1351, (bb)::[], _162_1350)))
in (FStar_SMTEncoding_Term.mkForall _162_1352))
in (_162_1353, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_162_1354))
in (_162_1355)::[])
in (_162_1357)::_162_1356))))))
in (
# 1093 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun env reft_name _78_1766 -> (
# 1094 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1096 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1097 "FStar.SMTEncoding.Encode.fst"
let refa = (let _162_1366 = (let _162_1365 = (let _162_1364 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_162_1364)::[])
in (reft_name, _162_1365))
in (FStar_SMTEncoding_Term.mkApp _162_1366))
in (
# 1098 "FStar.SMTEncoding.Encode.fst"
let refb = (let _162_1369 = (let _162_1368 = (let _162_1367 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_162_1367)::[])
in (reft_name, _162_1368))
in (FStar_SMTEncoding_Term.mkApp _162_1369))
in (
# 1099 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1100 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _162_1388 = (let _162_1375 = (let _162_1374 = (let _162_1373 = (let _162_1372 = (let _162_1371 = (let _162_1370 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _162_1370))
in (FStar_SMTEncoding_Term.mkImp _162_1371))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _162_1372))
in (mkForall_fuel _162_1373))
in (_162_1374, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1375))
in (let _162_1387 = (let _162_1386 = (let _162_1385 = (let _162_1384 = (let _162_1383 = (let _162_1382 = (let _162_1381 = (let _162_1380 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _162_1379 = (let _162_1378 = (let _162_1377 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _162_1376 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_162_1377, _162_1376)))
in (FStar_SMTEncoding_Term.mkEq _162_1378))
in (_162_1380, _162_1379)))
in (FStar_SMTEncoding_Term.mkImp _162_1381))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _162_1382))
in (mkForall_fuel' 2 _162_1383))
in (_162_1384, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_162_1385))
in (_162_1386)::[])
in (_162_1388)::_162_1387))))))))))
in (
# 1103 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun env nm false_tm -> (
# 1104 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _162_1397 = (let _162_1396 = (let _162_1395 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_162_1395, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1396))
in (_162_1397)::[])))
in (
# 1106 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun env conj _78_1783 -> (
# 1107 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1109 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1110 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1406 = (let _162_1405 = (let _162_1404 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_162_1404)::[])
in ("Valid", _162_1405))
in (FStar_SMTEncoding_Term.mkApp _162_1406))
in (
# 1112 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1113 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _162_1413 = (let _162_1412 = (let _162_1411 = (let _162_1410 = (let _162_1409 = (let _162_1408 = (let _162_1407 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_162_1407, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1408))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1409))
in (FStar_SMTEncoding_Term.mkForall _162_1410))
in (_162_1411, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1412))
in (_162_1413)::[])))))))))
in (
# 1115 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun env disj _78_1795 -> (
# 1116 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1117 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1118 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1119 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1120 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1422 = (let _162_1421 = (let _162_1420 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_162_1420)::[])
in ("Valid", _162_1421))
in (FStar_SMTEncoding_Term.mkApp _162_1422))
in (
# 1121 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1122 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _162_1429 = (let _162_1428 = (let _162_1427 = (let _162_1426 = (let _162_1425 = (let _162_1424 = (let _162_1423 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_162_1423, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1424))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1425))
in (FStar_SMTEncoding_Term.mkForall _162_1426))
in (_162_1427, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1428))
in (_162_1429)::[])))))))))
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun env eq2 tt -> (
# 1125 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1128 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1129 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1130 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1131 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1132 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1438 = (let _162_1437 = (let _162_1436 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_162_1436)::[])
in ("Valid", _162_1437))
in (FStar_SMTEncoding_Term.mkApp _162_1438))
in (let _162_1445 = (let _162_1444 = (let _162_1443 = (let _162_1442 = (let _162_1441 = (let _162_1440 = (let _162_1439 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_162_1439, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1440))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _162_1441))
in (FStar_SMTEncoding_Term.mkForall _162_1442))
in (_162_1443, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1444))
in (_162_1445)::[])))))))))))
in (
# 1135 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun env imp tt -> (
# 1136 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1137 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1138 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1139 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1140 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1454 = (let _162_1453 = (let _162_1452 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_162_1452)::[])
in ("Valid", _162_1453))
in (FStar_SMTEncoding_Term.mkApp _162_1454))
in (
# 1141 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1142 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _162_1461 = (let _162_1460 = (let _162_1459 = (let _162_1458 = (let _162_1457 = (let _162_1456 = (let _162_1455 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_162_1455, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1456))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1457))
in (FStar_SMTEncoding_Term.mkForall _162_1458))
in (_162_1459, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1460))
in (_162_1461)::[])))))))))
in (
# 1144 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun env iff tt -> (
# 1145 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1148 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1149 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1470 = (let _162_1469 = (let _162_1468 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_162_1468)::[])
in ("Valid", _162_1469))
in (FStar_SMTEncoding_Term.mkApp _162_1470))
in (
# 1150 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1151 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _162_1477 = (let _162_1476 = (let _162_1475 = (let _162_1474 = (let _162_1473 = (let _162_1472 = (let _162_1471 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_162_1471, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1472))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1473))
in (FStar_SMTEncoding_Term.mkForall _162_1474))
in (_162_1475, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1476))
in (_162_1477)::[])))))))))
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun env for_all tt -> (
# 1154 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1155 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1156 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1157 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1158 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1159 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1160 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1486 = (let _162_1485 = (let _162_1484 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_162_1484)::[])
in ("Valid", _162_1485))
in (FStar_SMTEncoding_Term.mkApp _162_1486))
in (
# 1161 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _162_1489 = (let _162_1488 = (let _162_1487 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_162_1487)::[])
in ("Valid", _162_1488))
in (FStar_SMTEncoding_Term.mkApp _162_1489))
in (let _162_1503 = (let _162_1502 = (let _162_1501 = (let _162_1500 = (let _162_1499 = (let _162_1498 = (let _162_1497 = (let _162_1496 = (let _162_1495 = (let _162_1491 = (let _162_1490 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_162_1490)::[])
in (_162_1491)::[])
in (let _162_1494 = (let _162_1493 = (let _162_1492 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_162_1492, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _162_1493))
in (_162_1495, (xx)::[], _162_1494)))
in (FStar_SMTEncoding_Term.mkForall _162_1496))
in (_162_1497, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1498))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1499))
in (FStar_SMTEncoding_Term.mkForall _162_1500))
in (_162_1501, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1502))
in (_162_1503)::[]))))))))))
in (
# 1163 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun env for_some tt -> (
# 1164 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1165 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1166 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1167 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1168 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1169 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1170 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1512 = (let _162_1511 = (let _162_1510 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_162_1510)::[])
in ("Valid", _162_1511))
in (FStar_SMTEncoding_Term.mkApp _162_1512))
in (
# 1171 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _162_1515 = (let _162_1514 = (let _162_1513 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_162_1513)::[])
in ("Valid", _162_1514))
in (FStar_SMTEncoding_Term.mkApp _162_1515))
in (let _162_1529 = (let _162_1528 = (let _162_1527 = (let _162_1526 = (let _162_1525 = (let _162_1524 = (let _162_1523 = (let _162_1522 = (let _162_1521 = (let _162_1517 = (let _162_1516 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_162_1516)::[])
in (_162_1517)::[])
in (let _162_1520 = (let _162_1519 = (let _162_1518 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_162_1518, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _162_1519))
in (_162_1521, (xx)::[], _162_1520)))
in (FStar_SMTEncoding_Term.mkExists _162_1522))
in (_162_1523, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1524))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1525))
in (FStar_SMTEncoding_Term.mkForall _162_1526))
in (_162_1527, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1528))
in (_162_1529)::[]))))))))))
in (
# 1173 "FStar.SMTEncoding.Encode.fst"
let mk_range_of_interp = (fun env range_of tt -> (
# 1174 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1175 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1176 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1177 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1178 "FStar.SMTEncoding.Encode.fst"
let range_of_ty = (FStar_SMTEncoding_Term.mkApp (range_of, (a)::(b)::[]))
in (let _162_1540 = (let _162_1539 = (let _162_1538 = (let _162_1537 = (let _162_1536 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_of_ty)
in (((range_of_ty)::[])::[], (aa)::(bb)::[], _162_1536))
in (FStar_SMTEncoding_Term.mkForall _162_1537))
in (_162_1538, Some ("Range_const typing")))
in FStar_SMTEncoding_Term.Assume (_162_1539))
in (_162_1540)::[])))))))
in (
# 1185 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_of_lid, mk_range_of_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _78_1881 -> (match (_78_1881) with
| (l, _78_1880) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_78_1884, f) -> begin
(f env s tt)
end))))))))))))))))))))))

# 1208 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1209 "FStar.SMTEncoding.Encode.fst"
let _78_1890 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _162_1752 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _162_1752))
end else begin
()
end
in (
# 1212 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1215 "FStar.SMTEncoding.Encode.fst"
let _78_1898 = (encode_sigelt' env se)
in (match (_78_1898) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _162_1755 = (let _162_1754 = (let _162_1753 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_162_1753))
in (_162_1754)::[])
in (_162_1755, e))
end
| _78_1901 -> begin
(let _162_1762 = (let _162_1761 = (let _162_1757 = (let _162_1756 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_162_1756))
in (_162_1757)::g)
in (let _162_1760 = (let _162_1759 = (let _162_1758 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_162_1758))
in (_162_1759)::[])
in (FStar_List.append _162_1761 _162_1760)))
in (_162_1762, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1221 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1227 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1228 "FStar.SMTEncoding.Encode.fst"
let tt = (norm env t)
in (
# 1234 "FStar.SMTEncoding.Encode.fst"
let _78_1914 = (encode_free_var env lid t tt quals)
in (match (_78_1914) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _162_1776 = (let _162_1775 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _162_1775))
in (_162_1776, env))
end else begin
(decls, env)
end
end))))
in (
# 1240 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _78_1921 lb -> (match (_78_1921) with
| (decls, env) -> begin
(
# 1242 "FStar.SMTEncoding.Encode.fst"
let _78_1925 = (let _162_1785 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _162_1785 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_78_1925) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _78_1943, _78_1945, _78_1947, _78_1949) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1254 "FStar.SMTEncoding.Encode.fst"
let _78_1955 = (new_term_constant_and_tok_from_lid env lid)
in (match (_78_1955) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _78_1958, t, quals, _78_1962) -> begin
(
# 1258 "FStar.SMTEncoding.Encode.fst"
let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_12 -> (match (_78_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _78_1975 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(
# 1263 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (
# 1264 "FStar.SMTEncoding.Encode.fst"
let _78_1980 = (encode_top_level_val env fv t quals)
in (match (_78_1980) with
| (decls, env) -> begin
(
# 1265 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1266 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _162_1788 = (let _162_1787 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _162_1787))
in (_162_1788, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _78_1986, _78_1988) -> begin
(
# 1272 "FStar.SMTEncoding.Encode.fst"
let _78_1993 = (encode_formula f env)
in (match (_78_1993) with
| (f, decls) -> begin
(
# 1273 "FStar.SMTEncoding.Encode.fst"
let g = (let _162_1793 = (let _162_1792 = (let _162_1791 = (let _162_1790 = (let _162_1789 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _162_1789))
in Some (_162_1790))
in (f, _162_1791))
in FStar_SMTEncoding_Term.Assume (_162_1792))
in (_162_1793)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _78_1998, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_78_2003, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _78_2011; FStar_Syntax_Syntax.lbtyp = _78_2009; FStar_Syntax_Syntax.lbeff = _78_2007; FStar_Syntax_Syntax.lbdef = _78_2005}::[]), _78_2018, _78_2020, _78_2022) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1280 "FStar.SMTEncoding.Encode.fst"
let _78_2028 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_78_2028) with
| (tname, ttok, env) -> begin
(
# 1281 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1282 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1283 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _162_1796 = (let _162_1795 = (let _162_1794 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_162_1794)::[])
in ("Valid", _162_1795))
in (FStar_SMTEncoding_Term.mkApp _162_1796))
in (
# 1284 "FStar.SMTEncoding.Encode.fst"
let decls = (let _162_1804 = (let _162_1803 = (let _162_1802 = (let _162_1801 = (let _162_1800 = (let _162_1799 = (let _162_1798 = (let _162_1797 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _162_1797))
in (FStar_SMTEncoding_Term.mkEq _162_1798))
in (((valid_b2t_x)::[])::[], (xx)::[], _162_1799))
in (FStar_SMTEncoding_Term.mkForall _162_1800))
in (_162_1801, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_162_1802))
in (_162_1803)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_162_1804)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_78_2034, _78_2036, _78_2038, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_13 -> (match (_78_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _78_2048 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _78_2054, _78_2056, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_14 -> (match (_78_14) with
| FStar_Syntax_Syntax.Projector (_78_2062) -> begin
true
end
| _78_2065 -> begin
false
end)))) -> begin
(
# 1298 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1299 "FStar.SMTEncoding.Encode.fst"
let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_78_2069) -> begin
([], env)
end
| None -> begin
(
# 1304 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _78_2077, _78_2079, quals) -> begin
(
# 1310 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1311 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1312 "FStar.SMTEncoding.Encode.fst"
let _78_2091 = (FStar_Util.first_N nbinders formals)
in (match (_78_2091) with
| (formals, extra_formals) -> begin
(
# 1313 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _78_2095 _78_2099 -> (match ((_78_2095, _78_2099)) with
| ((formal, _78_2094), (binder, _78_2098)) -> begin
(let _162_1818 = (let _162_1817 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _162_1817))
in FStar_Syntax_Syntax.NT (_162_1818))
end)) formals binders)
in (
# 1314 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _162_1822 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _78_2103 -> (match (_78_2103) with
| (x, i) -> begin
(let _162_1821 = (
# 1314 "FStar.SMTEncoding.Encode.fst"
let _78_2104 = x
in (let _162_1820 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _78_2104.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _78_2104.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _162_1820}))
in (_162_1821, i))
end))))
in (FStar_All.pipe_right _162_1822 FStar_Syntax_Util.name_binders))
in (
# 1315 "FStar.SMTEncoding.Encode.fst"
let body = (let _162_1829 = (FStar_Syntax_Subst.compress body)
in (let _162_1828 = (let _162_1823 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _162_1823))
in (let _162_1827 = (let _162_1826 = (let _162_1825 = (FStar_Syntax_Subst.subst subst t)
in _162_1825.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _162_1824 -> Some (_162_1824)) _162_1826))
in (FStar_Syntax_Syntax.extend_app_n _162_1829 _162_1828 _162_1827 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1318 "FStar.SMTEncoding.Encode.fst"
let destruct_bound_function = (fun flid t_norm e -> (
# 1319 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t_norm -> (match ((let _162_1840 = (FStar_Syntax_Util.unascribe e)
in _162_1840.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1322 "FStar.SMTEncoding.Encode.fst"
let _78_2123 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_78_2123) with
| (binders, body, opening) -> begin
(match ((let _162_1841 = (FStar_Syntax_Subst.compress t_norm)
in _162_1841.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1325 "FStar.SMTEncoding.Encode.fst"
let _78_2130 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_78_2130) with
| (formals, c) -> begin
(
# 1326 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1327 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1328 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1330 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1331 "FStar.SMTEncoding.Encode.fst"
let _78_2137 = (FStar_Util.first_N nformals binders)
in (match (_78_2137) with
| (bs0, rest) -> begin
(
# 1332 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1333 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _78_2141 _78_2145 -> (match ((_78_2141, _78_2145)) with
| ((b, _78_2140), (x, _78_2144)) -> begin
(let _162_1845 = (let _162_1844 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _162_1844))
in FStar_Syntax_Syntax.NT (_162_1845))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1335 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1338 "FStar.SMTEncoding.Encode.fst"
let _78_2151 = (eta_expand binders formals body tres)
in (match (_78_2151) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _78_2154) -> begin
(aux true x.FStar_Syntax_Syntax.sort)
end
| _78_2158 when (not (norm)) -> begin
(
# 1346 "FStar.SMTEncoding.Encode.fst"
let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _78_2161 -> begin
(let _162_1848 = (let _162_1847 = (FStar_Syntax_Print.term_to_string e)
in (let _162_1846 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _162_1847 _162_1846)))
in (FStar_All.failwith _162_1848))
end)
end))
end
| _78_2163 -> begin
(match ((let _162_1849 = (FStar_Syntax_Subst.compress t_norm)
in _162_1849.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1356 "FStar.SMTEncoding.Encode.fst"
let _78_2170 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_78_2170) with
| (formals, c) -> begin
(
# 1357 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1358 "FStar.SMTEncoding.Encode.fst"
let _78_2174 = (eta_expand [] formals e tres)
in (match (_78_2174) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _78_2176 -> begin
([], e, [], t_norm)
end)
end))
in (aux false t_norm)))
in (FStar_All.try_with (fun _78_2178 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1366 "FStar.SMTEncoding.Encode.fst"
let _78_2204 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _78_2191 lb -> (match (_78_2191) with
| (toks, typs, decls, env) -> begin
(
# 1368 "FStar.SMTEncoding.Encode.fst"
let _78_2193 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1369 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1370 "FStar.SMTEncoding.Encode.fst"
let _78_2199 = (let _162_1854 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _162_1854 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_78_2199) with
| (tok, decl, env) -> begin
(let _162_1857 = (let _162_1856 = (let _162_1855 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_162_1855, tok))
in (_162_1856)::toks)
in (_162_1857, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_78_2204) with
| (toks, typs, decls, env) -> begin
(
# 1372 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1373 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1374 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_15 -> (match (_78_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _78_2211 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _162_1860 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _162_1860)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _78_2221; FStar_Syntax_Syntax.lbunivs = _78_2219; FStar_Syntax_Syntax.lbtyp = _78_2217; FStar_Syntax_Syntax.lbeff = _78_2215; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid_fv, (f, ftok))::[]) -> begin
(
# 1381 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1382 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1383 "FStar.SMTEncoding.Encode.fst"
let _78_2241 = (destruct_bound_function flid t_norm e)
in (match (_78_2241) with
| (binders, body, _78_2238, _78_2240) -> begin
(
# 1384 "FStar.SMTEncoding.Encode.fst"
let _78_2248 = (encode_binders None binders env)
in (match (_78_2248) with
| (vars, guards, env', binder_decls, _78_2247) -> begin
(
# 1385 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _78_2251 -> begin
(let _162_1862 = (let _162_1861 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _162_1861))
in (FStar_SMTEncoding_Term.mkApp _162_1862))
end)
in (
# 1386 "FStar.SMTEncoding.Encode.fst"
let _78_2257 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _162_1864 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _162_1863 = (encode_formula body env')
in (_162_1864, _162_1863)))
end else begin
(let _162_1865 = (encode_term body env')
in (app, _162_1865))
end
in (match (_78_2257) with
| (app, (body, decls2)) -> begin
(
# 1390 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _162_1874 = (let _162_1873 = (let _162_1870 = (let _162_1869 = (let _162_1868 = (let _162_1867 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _162_1866 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_162_1867, _162_1866)))
in (FStar_SMTEncoding_Term.mkImp _162_1868))
in (((app)::[])::[], vars, _162_1869))
in (FStar_SMTEncoding_Term.mkForall _162_1870))
in (let _162_1872 = (let _162_1871 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_162_1871))
in (_162_1873, _162_1872)))
in FStar_SMTEncoding_Term.Assume (_162_1874))
in (let _162_1876 = (let _162_1875 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _162_1875))
in (_162_1876, env)))
end)))
end))
end))))
end
| _78_2260 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1396 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _162_1877 = (varops.fresh "fuel")
in (_162_1877, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1397 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1398 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1399 "FStar.SMTEncoding.Encode.fst"
let _78_2278 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _78_2266 _78_2271 -> (match ((_78_2266, _78_2271)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(
# 1400 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1401 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1402 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1403 "FStar.SMTEncoding.Encode.fst"
let env = (let _162_1882 = (let _162_1881 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _162_1880 -> Some (_162_1880)) _162_1881))
in (push_free_var env flid gtok _162_1882))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_78_2278) with
| (gtoks, env) -> begin
(
# 1405 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1406 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _78_2287 t_norm _78_2298 -> (match ((_78_2287, _78_2298)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _78_2297; FStar_Syntax_Syntax.lbunivs = _78_2295; FStar_Syntax_Syntax.lbtyp = _78_2293; FStar_Syntax_Syntax.lbeff = _78_2291; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1407 "FStar.SMTEncoding.Encode.fst"
let _78_2303 = (destruct_bound_function flid t_norm e)
in (match (_78_2303) with
| (binders, body, formals, tres) -> begin
(
# 1408 "FStar.SMTEncoding.Encode.fst"
let _78_2310 = (encode_binders None binders env)
in (match (_78_2310) with
| (vars, guards, env', binder_decls, _78_2309) -> begin
(
# 1409 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _162_1893 = (let _162_1892 = (let _162_1891 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_162_1891)
in (g, _162_1892, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_162_1893))
in (
# 1410 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1411 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1412 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1413 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1414 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _162_1896 = (let _162_1895 = (let _162_1894 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_162_1894)::vars_tm)
in (g, _162_1895))
in (FStar_SMTEncoding_Term.mkApp _162_1896))
in (
# 1415 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _162_1899 = (let _162_1898 = (let _162_1897 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_162_1897)::vars_tm)
in (g, _162_1898))
in (FStar_SMTEncoding_Term.mkApp _162_1899))
in (
# 1416 "FStar.SMTEncoding.Encode.fst"
let _78_2320 = (encode_term body env')
in (match (_78_2320) with
| (body_tm, decls2) -> begin
(
# 1417 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _162_1908 = (let _162_1907 = (let _162_1904 = (let _162_1903 = (let _162_1902 = (let _162_1901 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _162_1900 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_162_1901, _162_1900)))
in (FStar_SMTEncoding_Term.mkImp _162_1902))
in (((gsapp)::[])::[], (fuel)::vars, _162_1903))
in (FStar_SMTEncoding_Term.mkForall _162_1904))
in (let _162_1906 = (let _162_1905 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_162_1905))
in (_162_1907, _162_1906)))
in FStar_SMTEncoding_Term.Assume (_162_1908))
in (
# 1419 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _162_1912 = (let _162_1911 = (let _162_1910 = (let _162_1909 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _162_1909))
in (FStar_SMTEncoding_Term.mkForall _162_1910))
in (_162_1911, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_162_1912))
in (
# 1421 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _162_1921 = (let _162_1920 = (let _162_1919 = (let _162_1918 = (let _162_1917 = (let _162_1916 = (let _162_1915 = (let _162_1914 = (let _162_1913 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_162_1913)::vars_tm)
in (g, _162_1914))
in (FStar_SMTEncoding_Term.mkApp _162_1915))
in (gsapp, _162_1916))
in (FStar_SMTEncoding_Term.mkEq _162_1917))
in (((gsapp)::[])::[], (fuel)::vars, _162_1918))
in (FStar_SMTEncoding_Term.mkForall _162_1919))
in (_162_1920, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_162_1921))
in (
# 1423 "FStar.SMTEncoding.Encode.fst"
let _78_2343 = (
# 1424 "FStar.SMTEncoding.Encode.fst"
let _78_2330 = (encode_binders None formals env0)
in (match (_78_2330) with
| (vars, v_guards, env, binder_decls, _78_2329) -> begin
(
# 1425 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1426 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1427 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1428 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _162_1922 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _162_1922 ((fuel)::vars)))
in (let _162_1926 = (let _162_1925 = (let _162_1924 = (let _162_1923 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _162_1923))
in (FStar_SMTEncoding_Term.mkForall _162_1924))
in (_162_1925, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_162_1926)))
in (
# 1431 "FStar.SMTEncoding.Encode.fst"
let _78_2340 = (
# 1432 "FStar.SMTEncoding.Encode.fst"
let _78_2337 = (encode_term_pred None tres env gapp)
in (match (_78_2337) with
| (g_typing, d3) -> begin
(let _162_1934 = (let _162_1933 = (let _162_1932 = (let _162_1931 = (let _162_1930 = (let _162_1929 = (let _162_1928 = (let _162_1927 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_162_1927, g_typing))
in (FStar_SMTEncoding_Term.mkImp _162_1928))
in (((gapp)::[])::[], (fuel)::vars, _162_1929))
in (FStar_SMTEncoding_Term.mkForall _162_1930))
in (_162_1931, None))
in FStar_SMTEncoding_Term.Assume (_162_1932))
in (_162_1933)::[])
in (d3, _162_1934))
end))
in (match (_78_2340) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_78_2343) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1436 "FStar.SMTEncoding.Encode.fst"
let _78_2359 = (let _162_1937 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _78_2347 _78_2351 -> (match ((_78_2347, _78_2351)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1437 "FStar.SMTEncoding.Encode.fst"
let _78_2355 = (encode_one_binding env0 gtok ty bs)
in (match (_78_2355) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _162_1937))
in (match (_78_2359) with
| (decls, eqns, env0) -> begin
(
# 1439 "FStar.SMTEncoding.Encode.fst"
let _78_2368 = (let _162_1939 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _162_1939 (FStar_List.partition (fun _78_16 -> (match (_78_16) with
| FStar_SMTEncoding_Term.DeclFun (_78_2362) -> begin
true
end
| _78_2365 -> begin
false
end)))))
in (match (_78_2368) with
| (prefix_decls, rest) -> begin
(
# 1442 "FStar.SMTEncoding.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _78_2177 -> (match (_78_2177) with
| Let_rec_unencodeable -> begin
(
# 1445 "FStar.SMTEncoding.Encode.fst"
let msg = (let _162_1942 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _162_1942 (FStar_String.concat " and ")))
in (
# 1446 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _78_2372, _78_2374, _78_2376) -> begin
(
# 1451 "FStar.SMTEncoding.Encode.fst"
let _78_2381 = (encode_signature env ses)
in (match (_78_2381) with
| (g, env) -> begin
(
# 1452 "FStar.SMTEncoding.Encode.fst"
let _78_2393 = (FStar_All.pipe_right g (FStar_List.partition (fun _78_17 -> (match (_78_17) with
| FStar_SMTEncoding_Term.Assume (_78_2384, Some ("inversion axiom")) -> begin
false
end
| _78_2390 -> begin
true
end))))
in (match (_78_2393) with
| (g', inversions) -> begin
(
# 1455 "FStar.SMTEncoding.Encode.fst"
let _78_2402 = (FStar_All.pipe_right g' (FStar_List.partition (fun _78_18 -> (match (_78_18) with
| FStar_SMTEncoding_Term.DeclFun (_78_2396) -> begin
true
end
| _78_2399 -> begin
false
end))))
in (match (_78_2402) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _78_2405, tps, k, _78_2409, datas, quals, _78_2413) -> begin
(
# 1461 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_19 -> (match (_78_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _78_2420 -> begin
false
end))))
in (
# 1462 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1464 "FStar.SMTEncoding.Encode.fst"
let _78_2432 = c
in (match (_78_2432) with
| (name, args, _78_2427, _78_2429, _78_2431) -> begin
(let _162_1950 = (let _162_1949 = (let _162_1948 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _162_1948, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_162_1949))
in (_162_1950)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1468 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _162_1956 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _162_1956 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1472 "FStar.SMTEncoding.Encode.fst"
let _78_2439 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_2439) with
| (xxsym, xx) -> begin
(
# 1473 "FStar.SMTEncoding.Encode.fst"
let _78_2475 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _78_2442 l -> (match (_78_2442) with
| (out, decls) -> begin
(
# 1474 "FStar.SMTEncoding.Encode.fst"
let _78_2447 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_78_2447) with
| (_78_2445, data_t) -> begin
(
# 1475 "FStar.SMTEncoding.Encode.fst"
let _78_2450 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_78_2450) with
| (args, res) -> begin
(
# 1476 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _162_1959 = (FStar_Syntax_Subst.compress res)
in _162_1959.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_78_2452, indices) -> begin
indices
end
| _78_2457 -> begin
[]
end)
in (
# 1479 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _78_2463 -> (match (_78_2463) with
| (x, _78_2462) -> begin
(let _162_1964 = (let _162_1963 = (let _162_1962 = (mk_term_projector_name l x)
in (_162_1962, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _162_1963))
in (push_term_var env x _162_1964))
end)) env))
in (
# 1482 "FStar.SMTEncoding.Encode.fst"
let _78_2467 = (encode_args indices env)
in (match (_78_2467) with
| (indices, decls') -> begin
(
# 1483 "FStar.SMTEncoding.Encode.fst"
let _78_2468 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1485 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _162_1969 = (FStar_List.map2 (fun v a -> (let _162_1968 = (let _162_1967 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_162_1967, a))
in (FStar_SMTEncoding_Term.mkEq _162_1968))) vars indices)
in (FStar_All.pipe_right _162_1969 FStar_SMTEncoding_Term.mk_and_l))
in (let _162_1974 = (let _162_1973 = (let _162_1972 = (let _162_1971 = (let _162_1970 = (mk_data_tester env l xx)
in (_162_1970, eqs))
in (FStar_SMTEncoding_Term.mkAnd _162_1971))
in (out, _162_1972))
in (FStar_SMTEncoding_Term.mkOr _162_1973))
in (_162_1974, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_78_2475) with
| (data_ax, decls) -> begin
(
# 1487 "FStar.SMTEncoding.Encode.fst"
let _78_2478 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_2478) with
| (ffsym, ff) -> begin
(
# 1488 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _162_1975 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _162_1975 xx tapp))
in (let _162_1982 = (let _162_1981 = (let _162_1980 = (let _162_1979 = (let _162_1978 = (let _162_1977 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _162_1976 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _162_1977, _162_1976)))
in (FStar_SMTEncoding_Term.mkForall _162_1978))
in (_162_1979, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_162_1980))
in (_162_1981)::[])
in (FStar_List.append decls _162_1982)))
end))
end))
end))
end)
in (
# 1492 "FStar.SMTEncoding.Encode.fst"
let _78_2488 = (match ((let _162_1983 = (FStar_Syntax_Subst.compress k)
in _162_1983.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _78_2485 -> begin
(tps, k)
end)
in (match (_78_2488) with
| (formals, res) -> begin
(
# 1498 "FStar.SMTEncoding.Encode.fst"
let _78_2491 = (FStar_Syntax_Subst.open_term formals res)
in (match (_78_2491) with
| (formals, res) -> begin
(
# 1499 "FStar.SMTEncoding.Encode.fst"
let _78_2498 = (encode_binders None formals env)
in (match (_78_2498) with
| (vars, guards, env', binder_decls, _78_2497) -> begin
(
# 1501 "FStar.SMTEncoding.Encode.fst"
let _78_2502 = (new_term_constant_and_tok_from_lid env t)
in (match (_78_2502) with
| (tname, ttok, env) -> begin
(
# 1502 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1503 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1504 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _162_1985 = (let _162_1984 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _162_1984))
in (FStar_SMTEncoding_Term.mkApp _162_1985))
in (
# 1505 "FStar.SMTEncoding.Encode.fst"
let _78_2523 = (
# 1506 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _162_1989 = (let _162_1988 = (FStar_All.pipe_right vars (FStar_List.map (fun _78_2508 -> (match (_78_2508) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _162_1987 = (varops.next_id ())
in (tname, _162_1988, FStar_SMTEncoding_Term.Term_sort, _162_1987, false)))
in (constructor_or_logic_type_decl _162_1989))
in (
# 1507 "FStar.SMTEncoding.Encode.fst"
let _78_2520 = (match (vars) with
| [] -> begin
(let _162_1993 = (let _162_1992 = (let _162_1991 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _162_1990 -> Some (_162_1990)) _162_1991))
in (push_free_var env t tname _162_1992))
in ([], _162_1993))
end
| _78_2512 -> begin
(
# 1510 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1511 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _162_1994 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _162_1994))
in (
# 1512 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1513 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1516 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _162_1998 = (let _162_1997 = (let _162_1996 = (let _162_1995 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _162_1995))
in (FStar_SMTEncoding_Term.mkForall' _162_1996))
in (_162_1997, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_162_1998))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_78_2520) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_78_2523) with
| (decls, env) -> begin
(
# 1519 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1520 "FStar.SMTEncoding.Encode.fst"
let _78_2526 = (encode_term_pred None res env' tapp)
in (match (_78_2526) with
| (k, decls) -> begin
(
# 1521 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _162_2002 = (let _162_2001 = (let _162_2000 = (let _162_1999 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _162_1999))
in (_162_2000, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_162_2001))
in (_162_2002)::[])
end else begin
[]
end
in (let _162_2008 = (let _162_2007 = (let _162_2006 = (let _162_2005 = (let _162_2004 = (let _162_2003 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _162_2003))
in (FStar_SMTEncoding_Term.mkForall _162_2004))
in (_162_2005, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_162_2006))
in (_162_2007)::[])
in (FStar_List.append (FStar_List.append decls karr) _162_2008)))
end))
in (
# 1526 "FStar.SMTEncoding.Encode.fst"
let aux = (let _162_2012 = (let _162_2009 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _162_2009))
in (let _162_2011 = (let _162_2010 = (pretype_axiom tapp vars)
in (_162_2010)::[])
in (FStar_List.append _162_2012 _162_2011)))
in (
# 1531 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _78_2533, _78_2535, _78_2537, _78_2539, _78_2541, _78_2543, _78_2545) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _78_2550, t, _78_2553, n_tps, quals, _78_2557, drange) -> begin
(
# 1539 "FStar.SMTEncoding.Encode.fst"
let _78_2564 = (new_term_constant_and_tok_from_lid env d)
in (match (_78_2564) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1540 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1541 "FStar.SMTEncoding.Encode.fst"
let _78_2568 = (FStar_Syntax_Util.arrow_formals t)
in (match (_78_2568) with
| (formals, t_res) -> begin
(
# 1542 "FStar.SMTEncoding.Encode.fst"
let _78_2571 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_2571) with
| (fuel_var, fuel_tm) -> begin
(
# 1543 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1544 "FStar.SMTEncoding.Encode.fst"
let _78_2578 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_78_2578) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1545 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _162_2014 = (mk_term_projector_name d x)
in (_162_2014, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1546 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _162_2016 = (let _162_2015 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _162_2015, true))
in (FStar_All.pipe_right _162_2016 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1547 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1548 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1549 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1550 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1552 "FStar.SMTEncoding.Encode.fst"
let _78_2588 = (encode_term_pred None t env ddtok_tm)
in (match (_78_2588) with
| (tok_typing, decls3) -> begin
(
# 1554 "FStar.SMTEncoding.Encode.fst"
let _78_2595 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_78_2595) with
| (vars', guards', env'', decls_formals, _78_2594) -> begin
(
# 1555 "FStar.SMTEncoding.Encode.fst"
let _78_2600 = (
# 1556 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1557 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_78_2600) with
| (ty_pred', decls_pred) -> begin
(
# 1559 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1560 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _78_2604 -> begin
(let _162_2018 = (let _162_2017 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _162_2017))
in (_162_2018)::[])
end)
in (
# 1564 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _78_2607 -> (match (()) with
| () -> begin
(
# 1565 "FStar.SMTEncoding.Encode.fst"
let _78_2610 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_78_2610) with
| (head, args) -> begin
(match ((let _162_2021 = (FStar_Syntax_Subst.compress head)
in _162_2021.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(
# 1569 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (
# 1570 "FStar.SMTEncoding.Encode.fst"
let _78_2628 = (encode_args args env')
in (match (_78_2628) with
| (encoded_args, arg_decls) -> begin
(
# 1571 "FStar.SMTEncoding.Encode.fst"
let _78_2643 = (FStar_List.fold_left (fun _78_2632 arg -> (match (_78_2632) with
| (env, arg_vars, eqns) -> begin
(
# 1572 "FStar.SMTEncoding.Encode.fst"
let _78_2638 = (let _162_2024 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _162_2024))
in (match (_78_2638) with
| (_78_2635, xv, env) -> begin
(let _162_2026 = (let _162_2025 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_162_2025)::eqns)
in (env, (xv)::arg_vars, _162_2026))
end))
end)) (env', [], []) encoded_args)
in (match (_78_2643) with
| (_78_2640, arg_vars, eqns) -> begin
(
# 1574 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1575 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1576 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1577 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1578 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1579 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1580 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _162_2033 = (let _162_2032 = (let _162_2031 = (let _162_2030 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _162_2029 = (let _162_2028 = (let _162_2027 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _162_2027))
in (FStar_SMTEncoding_Term.mkImp _162_2028))
in (((ty_pred)::[])::[], _162_2030, _162_2029)))
in (FStar_SMTEncoding_Term.mkForall _162_2031))
in (_162_2032, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_162_2033))
in (
# 1585 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1587 "FStar.SMTEncoding.Encode.fst"
let x = (let _162_2034 = (varops.fresh "x")
in (_162_2034, FStar_SMTEncoding_Term.Term_sort))
in (
# 1588 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _162_2044 = (let _162_2043 = (let _162_2042 = (let _162_2041 = (let _162_2036 = (let _162_2035 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_162_2035)::[])
in (_162_2036)::[])
in (let _162_2040 = (let _162_2039 = (let _162_2038 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _162_2037 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_162_2038, _162_2037)))
in (FStar_SMTEncoding_Term.mkImp _162_2039))
in (_162_2041, (x)::[], _162_2040)))
in (FStar_SMTEncoding_Term.mkForall _162_2042))
in (_162_2043, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_162_2044))))
end else begin
(
# 1591 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _162_2047 = (let _162_2046 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _162_2046 dapp))
in (_162_2047)::[])
end
| _78_2657 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _162_2054 = (let _162_2053 = (let _162_2052 = (let _162_2051 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _162_2050 = (let _162_2049 = (let _162_2048 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _162_2048))
in (FStar_SMTEncoding_Term.mkImp _162_2049))
in (((ty_pred)::[])::[], _162_2051, _162_2050)))
in (FStar_SMTEncoding_Term.mkForall _162_2052))
in (_162_2053, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_162_2054)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _78_2661 -> begin
(
# 1599 "FStar.SMTEncoding.Encode.fst"
let _78_2662 = (let _162_2057 = (let _162_2056 = (FStar_Syntax_Print.lid_to_string d)
in (let _162_2055 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _162_2056 _162_2055)))
in (FStar_TypeChecker_Errors.warn drange _162_2057))
in ([], []))
end)
end))
end))
in (
# 1602 "FStar.SMTEncoding.Encode.fst"
let _78_2666 = (encode_elim ())
in (match (_78_2666) with
| (decls2, elim) -> begin
(
# 1603 "FStar.SMTEncoding.Encode.fst"
let g = (let _162_2082 = (let _162_2081 = (let _162_2066 = (let _162_2065 = (let _162_2064 = (let _162_2063 = (let _162_2062 = (let _162_2061 = (let _162_2060 = (let _162_2059 = (let _162_2058 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _162_2058))
in Some (_162_2059))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _162_2060))
in FStar_SMTEncoding_Term.DeclFun (_162_2061))
in (_162_2062)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _162_2063))
in (FStar_List.append _162_2064 proxy_fresh))
in (FStar_List.append _162_2065 decls_formals))
in (FStar_List.append _162_2066 decls_pred))
in (let _162_2080 = (let _162_2079 = (let _162_2078 = (let _162_2070 = (let _162_2069 = (let _162_2068 = (let _162_2067 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _162_2067))
in (FStar_SMTEncoding_Term.mkForall _162_2068))
in (_162_2069, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_162_2070))
in (let _162_2077 = (let _162_2076 = (let _162_2075 = (let _162_2074 = (let _162_2073 = (let _162_2072 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _162_2071 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _162_2072, _162_2071)))
in (FStar_SMTEncoding_Term.mkForall _162_2073))
in (_162_2074, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_162_2075))
in (_162_2076)::[])
in (_162_2078)::_162_2077))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_162_2079)
in (FStar_List.append _162_2081 _162_2080)))
in (FStar_List.append _162_2082 elim))
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
# 1621 "FStar.SMTEncoding.Encode.fst"
let _78_2675 = (encode_free_var env x t t_norm [])
in (match (_78_2675) with
| (decls, env) -> begin
(
# 1622 "FStar.SMTEncoding.Encode.fst"
let _78_2680 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_78_2680) with
| (n, x', _78_2679) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _78_2684) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (
# 1628 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1629 "FStar.SMTEncoding.Encode.fst"
let _78_2693 = (encode_function_type_as_formula None None t env)
in (match (_78_2693) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (
# 1633 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _162_2095 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _162_2095)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1636 "FStar.SMTEncoding.Encode.fst"
let _78_2703 = (new_term_constant_and_tok_from_lid env lid)
in (match (_78_2703) with
| (vname, vtok, env) -> begin
(
# 1637 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _162_2096 = (FStar_Syntax_Subst.compress t_norm)
in _162_2096.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _78_2706) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _78_2709 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _78_2712 -> begin
[]
end)
in (
# 1640 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1641 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1644 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1645 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1646 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1648 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1649 "FStar.SMTEncoding.Encode.fst"
let _78_2727 = (
# 1650 "FStar.SMTEncoding.Encode.fst"
let _78_2722 = (curried_arrow_formals_comp t_norm)
in (match (_78_2722) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _162_2098 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _162_2098))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_78_2727) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1654 "FStar.SMTEncoding.Encode.fst"
let _78_2731 = (new_term_constant_and_tok_from_lid env lid)
in (match (_78_2731) with
| (vname, vtok, env) -> begin
(
# 1655 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _78_2734 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1658 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _78_20 -> (match (_78_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1660 "FStar.SMTEncoding.Encode.fst"
let _78_2750 = (FStar_Util.prefix vars)
in (match (_78_2750) with
| (_78_2745, (xxsym, _78_2748)) -> begin
(
# 1661 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _162_2115 = (let _162_2114 = (let _162_2113 = (let _162_2112 = (let _162_2111 = (let _162_2110 = (let _162_2109 = (let _162_2108 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_2108))
in (vapp, _162_2109))
in (FStar_SMTEncoding_Term.mkEq _162_2110))
in (((vapp)::[])::[], vars, _162_2111))
in (FStar_SMTEncoding_Term.mkForall _162_2112))
in (_162_2113, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_162_2114))
in (_162_2115)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1666 "FStar.SMTEncoding.Encode.fst"
let _78_2762 = (FStar_Util.prefix vars)
in (match (_78_2762) with
| (_78_2757, (xxsym, _78_2760)) -> begin
(
# 1667 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1668 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1669 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _162_2117 = (let _162_2116 = (mk_term_projector_name d f)
in (_162_2116, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _162_2117))
in (let _162_2122 = (let _162_2121 = (let _162_2120 = (let _162_2119 = (let _162_2118 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _162_2118))
in (FStar_SMTEncoding_Term.mkForall _162_2119))
in (_162_2120, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_162_2121))
in (_162_2122)::[]))))
end))
end
| _78_2767 -> begin
[]
end)))))
in (
# 1673 "FStar.SMTEncoding.Encode.fst"
let _78_2774 = (encode_binders None formals env)
in (match (_78_2774) with
| (vars, guards, env', decls1, _78_2773) -> begin
(
# 1674 "FStar.SMTEncoding.Encode.fst"
let _78_2783 = (match (pre_opt) with
| None -> begin
(let _162_2123 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_162_2123, decls1))
end
| Some (p) -> begin
(
# 1676 "FStar.SMTEncoding.Encode.fst"
let _78_2780 = (encode_formula p env')
in (match (_78_2780) with
| (g, ds) -> begin
(let _162_2124 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_162_2124, (FStar_List.append decls1 ds)))
end))
end)
in (match (_78_2783) with
| (guard, decls1) -> begin
(
# 1677 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1679 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _162_2126 = (let _162_2125 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _162_2125))
in (FStar_SMTEncoding_Term.mkApp _162_2126))
in (
# 1680 "FStar.SMTEncoding.Encode.fst"
let _78_2807 = (
# 1681 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _162_2129 = (let _162_2128 = (FStar_All.pipe_right formals (FStar_List.map (fun _78_2786 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _162_2128, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_162_2129))
in (
# 1682 "FStar.SMTEncoding.Encode.fst"
let _78_2794 = (
# 1683 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1683 "FStar.SMTEncoding.Encode.fst"
let _78_2789 = env
in {bindings = _78_2789.bindings; depth = _78_2789.depth; tcenv = _78_2789.tcenv; warn = _78_2789.warn; cache = _78_2789.cache; nolabels = _78_2789.nolabels; use_zfuel_name = _78_2789.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_78_2794) with
| (tok_typing, decls2) -> begin
(
# 1687 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1688 "FStar.SMTEncoding.Encode.fst"
let _78_2804 = (match (formals) with
| [] -> begin
(let _162_2133 = (let _162_2132 = (let _162_2131 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _162_2130 -> Some (_162_2130)) _162_2131))
in (push_free_var env lid vname _162_2132))
in ((FStar_List.append decls2 ((tok_typing)::[])), _162_2133))
end
| _78_2798 -> begin
(
# 1691 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1692 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _162_2134 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _162_2134))
in (
# 1693 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _162_2138 = (let _162_2137 = (let _162_2136 = (let _162_2135 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _162_2135))
in (FStar_SMTEncoding_Term.mkForall _162_2136))
in (_162_2137, None))
in FStar_SMTEncoding_Term.Assume (_162_2138))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_78_2804) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_78_2807) with
| (decls2, env) -> begin
(
# 1696 "FStar.SMTEncoding.Encode.fst"
let _78_2815 = (
# 1697 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1698 "FStar.SMTEncoding.Encode.fst"
let _78_2811 = (encode_term res_t env')
in (match (_78_2811) with
| (encoded_res_t, decls) -> begin
(let _162_2139 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _162_2139, decls))
end)))
in (match (_78_2815) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1700 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _162_2143 = (let _162_2142 = (let _162_2141 = (let _162_2140 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _162_2140))
in (FStar_SMTEncoding_Term.mkForall _162_2141))
in (_162_2142, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_162_2143))
in (
# 1701 "FStar.SMTEncoding.Encode.fst"
let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _162_2149 = (let _162_2146 = (let _162_2145 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _162_2144 = (varops.next_id ())
in (vname, _162_2145, FStar_SMTEncoding_Term.Term_sort, _162_2144)))
in (FStar_SMTEncoding_Term.fresh_constructor _162_2146))
in (let _162_2148 = (let _162_2147 = (pretype_axiom vapp vars)
in (_162_2147)::[])
in (_162_2149)::_162_2148))
end else begin
[]
end
in (
# 1706 "FStar.SMTEncoding.Encode.fst"
let g = (let _162_2151 = (let _162_2150 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_162_2150)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _162_2151))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _78_2823 se -> (match (_78_2823) with
| (g, env) -> begin
(
# 1712 "FStar.SMTEncoding.Encode.fst"
let _78_2827 = (encode_sigelt env se)
in (match (_78_2827) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1715 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1740 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _78_2834 -> (match (_78_2834) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_78_2836) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1745 "FStar.SMTEncoding.Encode.fst"
let _78_2843 = (new_term_constant env x)
in (match (_78_2843) with
| (xxsym, xx, env') -> begin
(
# 1746 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1747 "FStar.SMTEncoding.Encode.fst"
let _78_2845 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _162_2166 = (FStar_Syntax_Print.bv_to_string x)
in (let _162_2165 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _162_2164 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _162_2166 _162_2165 _162_2164))))
end else begin
()
end
in (
# 1749 "FStar.SMTEncoding.Encode.fst"
let _78_2849 = (encode_term_pred None t1 env xx)
in (match (_78_2849) with
| (t, decls') -> begin
(
# 1750 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_2170 = (let _162_2169 = (FStar_Syntax_Print.bv_to_string x)
in (let _162_2168 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _162_2167 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _162_2169 _162_2168 _162_2167))))
in Some (_162_2170))
end else begin
None
end
in (
# 1754 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((FStar_SMTEncoding_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_78_2854, t)) -> begin
(
# 1760 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1761 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (
# 1763 "FStar.SMTEncoding.Encode.fst"
let _78_2863 = (encode_free_var env fv t t_norm [])
in (match (_78_2863) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1768 "FStar.SMTEncoding.Encode.fst"
let _78_2877 = (encode_sigelt env se)
in (match (_78_2877) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1773 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1774 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _78_2884 -> (match (_78_2884) with
| (l, _78_2881, _78_2883) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1775 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _78_2891 -> (match (_78_2891) with
| (l, _78_2888, _78_2890) -> begin
(let _162_2178 = (FStar_All.pipe_left (fun _162_2174 -> FStar_SMTEncoding_Term.Echo (_162_2174)) (Prims.fst l))
in (let _162_2177 = (let _162_2176 = (let _162_2175 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_162_2175))
in (_162_2176)::[])
in (_162_2178)::_162_2177))
end))))
in (prefix, suffix))))

# 1779 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1780 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _162_2183 = (let _162_2182 = (let _162_2181 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _162_2181; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_162_2182)::[])
in (FStar_ST.op_Colon_Equals last_env _162_2183)))

# 1783 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_78_2897 -> begin
(
# 1785 "FStar.SMTEncoding.Encode.fst"
let _78_2900 = e
in {bindings = _78_2900.bindings; depth = _78_2900.depth; tcenv = tcenv; warn = _78_2900.warn; cache = _78_2900.cache; nolabels = _78_2900.nolabels; use_zfuel_name = _78_2900.use_zfuel_name; encode_non_total_function_typ = _78_2900.encode_non_total_function_typ})
end))

# 1786 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _78_2906::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1789 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _78_2908 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1792 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1793 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1793 "FStar.SMTEncoding.Encode.fst"
let _78_2914 = hd
in {bindings = _78_2914.bindings; depth = _78_2914.depth; tcenv = _78_2914.tcenv; warn = _78_2914.warn; cache = refs; nolabels = _78_2914.nolabels; use_zfuel_name = _78_2914.use_zfuel_name; encode_non_total_function_typ = _78_2914.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1795 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _78_2917 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _78_2921::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1798 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _78_2923 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1799 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _78_2924 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1800 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _78_2925 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_78_2928::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _78_2933 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1806 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1807 "FStar.SMTEncoding.Encode.fst"
let _78_2935 = (init_env tcenv)
in (
# 1808 "FStar.SMTEncoding.Encode.fst"
let _78_2937 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1810 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1811 "FStar.SMTEncoding.Encode.fst"
let _78_2940 = (push_env ())
in (
# 1812 "FStar.SMTEncoding.Encode.fst"
let _78_2942 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1814 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1815 "FStar.SMTEncoding.Encode.fst"
let _78_2945 = (let _162_2204 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _162_2204))
in (
# 1816 "FStar.SMTEncoding.Encode.fst"
let _78_2947 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1818 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1819 "FStar.SMTEncoding.Encode.fst"
let _78_2950 = (mark_env ())
in (
# 1820 "FStar.SMTEncoding.Encode.fst"
let _78_2952 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1822 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1823 "FStar.SMTEncoding.Encode.fst"
let _78_2955 = (reset_mark_env ())
in (
# 1824 "FStar.SMTEncoding.Encode.fst"
let _78_2957 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1826 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1827 "FStar.SMTEncoding.Encode.fst"
let _78_2960 = (commit_mark_env ())
in (
# 1828 "FStar.SMTEncoding.Encode.fst"
let _78_2962 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1830 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1831 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_2220 = (let _162_2219 = (let _162_2218 = (let _162_2217 = (let _162_2216 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _162_2216 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _162_2217 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _162_2218))
in FStar_SMTEncoding_Term.Caption (_162_2219))
in (_162_2220)::decls)
end else begin
decls
end)
in (
# 1835 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1836 "FStar.SMTEncoding.Encode.fst"
let _78_2971 = (encode_sigelt env se)
in (match (_78_2971) with
| (decls, env) -> begin
(
# 1837 "FStar.SMTEncoding.Encode.fst"
let _78_2972 = (set_env env)
in (let _162_2221 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _162_2221)))
end)))))

# 1840 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1841 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1842 "FStar.SMTEncoding.Encode.fst"
let _78_2977 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _162_2226 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _162_2226))
end else begin
()
end
in (
# 1844 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1845 "FStar.SMTEncoding.Encode.fst"
let _78_2984 = (encode_signature (
# 1845 "FStar.SMTEncoding.Encode.fst"
let _78_2980 = env
in {bindings = _78_2980.bindings; depth = _78_2980.depth; tcenv = _78_2980.tcenv; warn = false; cache = _78_2980.cache; nolabels = _78_2980.nolabels; use_zfuel_name = _78_2980.use_zfuel_name; encode_non_total_function_typ = _78_2980.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_78_2984) with
| (decls, env) -> begin
(
# 1846 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1848 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1851 "FStar.SMTEncoding.Encode.fst"
let _78_2990 = (set_env (
# 1851 "FStar.SMTEncoding.Encode.fst"
let _78_2988 = env
in {bindings = _78_2988.bindings; depth = _78_2988.depth; tcenv = _78_2988.tcenv; warn = true; cache = _78_2988.cache; nolabels = _78_2988.nolabels; use_zfuel_name = _78_2988.use_zfuel_name; encode_non_total_function_typ = _78_2988.encode_non_total_function_typ}))
in (
# 1852 "FStar.SMTEncoding.Encode.fst"
let _78_2992 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1853 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1856 "FStar.SMTEncoding.Encode.fst"
let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (
# 1857 "FStar.SMTEncoding.Encode.fst"
let _78_2998 = (let _162_2245 = (let _162_2244 = (let _162_2243 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _162_2243))
in (FStar_Util.format1 "Starting query at %s" _162_2244))
in (push _162_2245))
in (
# 1858 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _78_3001 -> (match (()) with
| () -> begin
(let _162_2250 = (let _162_2249 = (let _162_2248 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _162_2248))
in (FStar_Util.format1 "Ending query at %s" _162_2249))
in (pop _162_2250))
end))
in (
# 1859 "FStar.SMTEncoding.Encode.fst"
let _78_3055 = (
# 1860 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1861 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1862 "FStar.SMTEncoding.Encode.fst"
let _78_3025 = (
# 1863 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1865 "FStar.SMTEncoding.Encode.fst"
let _78_3014 = (aux rest)
in (match (_78_3014) with
| (out, rest) -> begin
(
# 1866 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _162_2256 = (let _162_2255 = (FStar_Syntax_Syntax.mk_binder (
# 1867 "FStar.SMTEncoding.Encode.fst"
let _78_3016 = x
in {FStar_Syntax_Syntax.ppname = _78_3016.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _78_3016.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_162_2255)::out)
in (_162_2256, rest)))
end))
end
| _78_3019 -> begin
([], bindings)
end))
in (
# 1869 "FStar.SMTEncoding.Encode.fst"
let _78_3022 = (aux bindings)
in (match (_78_3022) with
| (closing, bindings) -> begin
(let _162_2257 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_162_2257, bindings))
end)))
in (match (_78_3025) with
| (q, bindings) -> begin
(
# 1871 "FStar.SMTEncoding.Encode.fst"
let _78_3034 = (let _162_2259 = (FStar_List.filter (fun _78_21 -> (match (_78_21) with
| FStar_TypeChecker_Env.Binding_sig (_78_3028) -> begin
false
end
| _78_3031 -> begin
true
end)) bindings)
in (encode_env_bindings env _162_2259))
in (match (_78_3034) with
| (env_decls, env) -> begin
(
# 1872 "FStar.SMTEncoding.Encode.fst"
let _78_3035 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _162_2260 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _162_2260))
end else begin
()
end
in (
# 1875 "FStar.SMTEncoding.Encode.fst"
let _78_3039 = (encode_formula q env)
in (match (_78_3039) with
| (phi, qdecls) -> begin
(
# 1876 "FStar.SMTEncoding.Encode.fst"
let _78_3044 = (let _162_2261 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _162_2261 phi))
in (match (_78_3044) with
| (phi, labels, _78_3043) -> begin
(
# 1877 "FStar.SMTEncoding.Encode.fst"
let _78_3047 = (encode_labels labels)
in (match (_78_3047) with
| (label_prefix, label_suffix) -> begin
(
# 1878 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1882 "FStar.SMTEncoding.Encode.fst"
let qry = (let _162_2263 = (let _162_2262 = (FStar_SMTEncoding_Term.mkNot phi)
in (_162_2262, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_162_2263))
in (
# 1883 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_78_3055) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _78_3062); FStar_SMTEncoding_Term.hash = _78_3059; FStar_SMTEncoding_Term.freevars = _78_3057}, _78_3067) -> begin
(
# 1886 "FStar.SMTEncoding.Encode.fst"
let _78_3070 = (pop ())
in ())
end
| _78_3073 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1887 "FStar.SMTEncoding.Encode.fst"
let _78_3074 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _78_3078) -> begin
(
# 1889 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1890 "FStar.SMTEncoding.Encode.fst"
let _78_3082 = (FStar_SMTEncoding_ErrorReporting.askZ3_and_report_errors tcenv fresh labels prefix qry suffix)
in (pop ())))
end
| _78_3085 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1896 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1897 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1898 "FStar.SMTEncoding.Encode.fst"
let _78_3089 = (push "query")
in (
# 1899 "FStar.SMTEncoding.Encode.fst"
let _78_3094 = (encode_formula q env)
in (match (_78_3094) with
| (f, _78_3093) -> begin
(
# 1900 "FStar.SMTEncoding.Encode.fst"
let _78_3095 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _78_3099) -> begin
true
end
| _78_3103 -> begin
false
end))
end)))))

# 1905 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1919 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _78_3104 -> ()); FStar_TypeChecker_Env.push = (fun _78_3106 -> ()); FStar_TypeChecker_Env.pop = (fun _78_3108 -> ()); FStar_TypeChecker_Env.mark = (fun _78_3110 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _78_3112 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _78_3114 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _78_3116 _78_3118 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _78_3120 _78_3122 -> ()); FStar_TypeChecker_Env.solve = (fun _78_3124 _78_3126 _78_3128 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _78_3130 _78_3132 -> false); FStar_TypeChecker_Env.finish = (fun _78_3134 -> ()); FStar_TypeChecker_Env.refresh = (fun _78_3135 -> ())}





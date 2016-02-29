
open Prims
# 34 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 35 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _76_28 -> (match (_76_28) with
| (a, b) -> begin
(a, b, c)
end))

# 36 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _76_1 -> (match (_76_1) with
| (FStar_Util.Inl (_76_32), _76_35) -> begin
false
end
| _76_38 -> begin
true
end)) args))

# 37 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _158_13 = (let _158_12 = (let _158_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _158_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _158_12))
in Some (_158_13))
end))

# 42 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 43 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _76_47 = a
in (let _158_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _158_20; FStar_Syntax_Syntax.index = _76_47.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _76_47.FStar_Syntax_Syntax.sort}))
in (let _158_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _158_21))))

# 46 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _76_54 -> (match (()) with
| () -> begin
(let _158_31 = (let _158_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _158_30 lid.FStar_Ident.str))
in (FStar_All.failwith _158_31))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _76_58 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_76_58) with
| (_76_56, t) -> begin
(match ((let _158_32 = (FStar_Syntax_Subst.compress t)
in _158_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _76_66 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_76_66) with
| (binders, _76_65) -> begin
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
| _76_69 -> begin
(fail ())
end)
end))))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _158_38 = (let _158_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _158_37))
in (FStar_All.pipe_left escape _158_38)))

# 58 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _158_44 = (let _158_43 = (mk_term_projector_name lid a)
in (_158_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _158_44)))

# 60 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _158_50 = (let _158_49 = (mk_term_projector_name_by_pos lid i)
in (_158_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _158_50)))

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
let initial_ctr = 10
in (
# 79 "FStar.SMTEncoding.Encode.fst"
let ctr = (FStar_Util.mk_ref initial_ctr)
in (
# 80 "FStar.SMTEncoding.Encode.fst"
let new_scope = (fun _76_93 -> (match (()) with
| () -> begin
(let _158_154 = (FStar_Util.smap_create 100)
in (let _158_153 = (FStar_Util.smap_create 100)
in (_158_154, _158_153)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _158_156 = (let _158_155 = (new_scope ())
in (_158_155)::[])
in (FStar_Util.mk_ref _158_156))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _158_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _158_160 (fun _76_101 -> (match (_76_101) with
| (names, _76_100) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_76_104) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _76_106 = (FStar_Util.incr ctr)
in (let _158_162 = (let _158_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _158_161))
in (Prims.strcat (Prims.strcat y "__") _158_162)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _158_164 = (let _158_163 = (FStar_ST.read scopes)
in (FStar_List.hd _158_163))
in (FStar_All.pipe_left Prims.fst _158_164))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _76_110 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _158_171 = (let _158_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _158_169 "__"))
in (let _158_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _158_171 _158_170))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _76_118 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _76_119 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _158_179 = (let _158_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _158_178))
in (FStar_Util.format2 "%s_%s" pfx _158_179)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _158_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _158_183 (fun _76_128 -> (match (_76_128) with
| (_76_126, strings) -> begin
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
let f = (let _158_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _158_184))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _158_186 = (let _158_185 = (FStar_ST.read scopes)
in (FStar_List.hd _158_185))
in (FStar_All.pipe_left Prims.snd _158_186))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _76_135 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _76_138 -> (match (()) with
| () -> begin
(let _158_191 = (let _158_190 = (new_scope ())
in (let _158_189 = (FStar_ST.read scopes)
in (_158_190)::_158_189))
in (FStar_ST.op_Colon_Equals scopes _158_191))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _76_140 -> (match (()) with
| () -> begin
(let _158_195 = (let _158_194 = (FStar_ST.read scopes)
in (FStar_List.tl _158_194))
in (FStar_ST.op_Colon_Equals scopes _158_195))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _76_142 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _76_144 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _76_146 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _76_159 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _76_164 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _76_167 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 122 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _76_169 = x
in (let _158_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _158_210; FStar_Syntax_Syntax.index = _76_169.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _76_169.FStar_Syntax_Syntax.sort})))

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
let ___Binding_var____0 : binding  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) = (fun projectee -> (match (projectee) with
| Binding_var (_76_173) -> begin
_76_173
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_76_176) -> begin
_76_176
end))

# 131 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 132 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 142 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _158_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _76_2 -> (match (_76_2) with
| Binding_var (x, _76_191) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _76_196, _76_198, _76_200) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _158_268 (FStar_String.concat ", "))))

# 147 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_158_278))
end else begin
None
end)

# 154 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _158_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _158_283))))

# 158 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _158_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _158_288))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _76_214 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _76_214.tcenv; warn = _76_214.warn; cache = _76_214.cache; nolabels = _76_214.nolabels; use_zfuel_name = _76_214.use_zfuel_name; encode_non_total_function_typ = _76_214.encode_non_total_function_typ})))))

# 162 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _76_220 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _76_220.depth; tcenv = _76_220.tcenv; warn = _76_220.warn; cache = _76_220.cache; nolabels = _76_220.nolabels; use_zfuel_name = _76_220.use_zfuel_name; encode_non_total_function_typ = _76_220.encode_non_total_function_typ})))))

# 166 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _76_225 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _76_225.depth; tcenv = _76_225.tcenv; warn = _76_225.warn; cache = _76_225.cache; nolabels = _76_225.nolabels; use_zfuel_name = _76_225.use_zfuel_name; encode_non_total_function_typ = _76_225.encode_non_total_function_typ}))

# 168 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _76_3 -> (match (_76_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _76_235 -> begin
None
end)))) with
| None -> begin
(let _158_305 = (let _158_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _158_304))
in (FStar_All.failwith _158_305))
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
in (let _158_316 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _76_245 = env
in (let _158_315 = (let _158_314 = (let _158_313 = (let _158_312 = (let _158_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _158_310 -> Some (_158_310)) _158_311))
in (x, fname, _158_312, None))
in Binding_fvar (_158_313))
in (_158_314)::env.bindings)
in {bindings = _158_315; depth = _76_245.depth; tcenv = _76_245.tcenv; warn = _76_245.warn; cache = _76_245.cache; nolabels = _76_245.nolabels; use_zfuel_name = _76_245.use_zfuel_name; encode_non_total_function_typ = _76_245.encode_non_total_function_typ}))
in (fname, ftok, _158_316)))))

# 179 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _76_4 -> (match (_76_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _76_257 -> begin
None
end))))

# 181 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _158_327 = (let _158_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _158_326))
in (FStar_All.failwith _158_327))
end
| Some (s) -> begin
s
end))

# 185 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _76_267 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _76_267.depth; tcenv = _76_267.tcenv; warn = _76_267.warn; cache = _76_267.cache; nolabels = _76_267.nolabels; use_zfuel_name = _76_267.use_zfuel_name; encode_non_total_function_typ = _76_267.encode_non_total_function_typ}))

# 187 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _76_276 = (lookup_lid env x)
in (match (_76_276) with
| (t1, t2, _76_275) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _158_344 = (let _158_343 = (let _158_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_158_342)::[])
in (f, _158_343))
in (FStar_SMTEncoding_Term.mkApp _158_344))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _76_278 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _76_278.depth; tcenv = _76_278.tcenv; warn = _76_278.warn; cache = _76_278.cache; nolabels = _76_278.nolabels; use_zfuel_name = _76_278.use_zfuel_name; encode_non_total_function_typ = _76_278.encode_non_total_function_typ}))
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
| _76_291 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_76_295, fuel::[]) -> begin
if (let _158_350 = (let _158_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _158_349 Prims.fst))
in (FStar_Util.starts_with _158_350 "fuel")) then begin
(let _158_353 = (let _158_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _158_352 fuel))
in (FStar_All.pipe_left (fun _158_351 -> Some (_158_351)) _158_353))
end else begin
Some (t)
end
end
| _76_301 -> begin
Some (t)
end)
end
| _76_303 -> begin
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
(let _158_357 = (let _158_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _158_356))
in (FStar_All.failwith _158_357))
end))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _76_316 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_76_316) with
| (x, _76_313, _76_315) -> begin
x
end)))

# 213 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _76_322 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_76_322) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _76_326; FStar_SMTEncoding_Term.freevars = _76_324}) when env.use_zfuel_name -> begin
(g, zf)
end
| _76_334 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _76_344 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 225 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _76_5 -> (match (_76_5) with
| Binding_fvar (_76_349, nm', tok, _76_353) when (nm = nm') -> begin
tok
end
| _76_357 -> begin
None
end))))

# 234 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _76_362 -> (match (_76_362) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _76_364 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _76_367 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_367) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _76_377 -> begin
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
(let _158_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _158_374))
end
| _76_390 -> begin
(let _158_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _158_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _76_393 -> begin
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
| (FStar_Syntax_Syntax.Tm_fvar (v, _)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _158_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv v.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _158_381 FStar_Option.isNone))
end
| _76_438 -> begin
false
end)))

# 269 "FStar.SMTEncoding.Encode.fst"
let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)

# 272 "FStar.SMTEncoding.Encode.fst"
let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))

# 274 "FStar.SMTEncoding.Encode.fst"
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _158_394 = (let _158_392 = (FStar_Syntax_Syntax.null_binder t)
in (_158_392)::[])
in (let _158_393 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
in (FStar_Syntax_Util.abs _158_394 _158_393 None))))

# 279 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _158_401 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _158_401))
end
| s -> begin
(
# 282 "FStar.SMTEncoding.Encode.fst"
let _76_450 = ()
in (let _158_402 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _158_402)))
end)) e)))

# 283 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 285 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _76_6 -> (match (_76_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _76_460 -> begin
false
end))

# 290 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 291 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _76_471; FStar_SMTEncoding_Term.freevars = _76_469}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _76_489) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _76_496 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_76_498, []) -> begin
(
# 302 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _76_504 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

# 333 "FStar.SMTEncoding.Encode.fst"
type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)

# 334 "FStar.SMTEncoding.Encode.fst"
type labels =
label Prims.list

# 335 "FStar.SMTEncoding.Encode.fst"
type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}

# 335 "FStar.SMTEncoding.Encode.fst"
let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

# 341 "FStar.SMTEncoding.Encode.fst"
exception Let_rec_unencodeable

# 341 "FStar.SMTEncoding.Encode.fst"
let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))

# 343 "FStar.SMTEncoding.Encode.fst"
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _76_7 -> (match (_76_7) with
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
(let _158_456 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _158_456))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _158_457 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _158_457))
end
| FStar_Const.Const_int (i) -> begin
(let _158_458 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _158_458))
end
| FStar_Const.Const_int32 (i) -> begin
(let _158_462 = (let _158_461 = (let _158_460 = (let _158_459 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _158_459))
in (_158_460)::[])
in ("FStar.Int32.Int32", _158_461))
in (FStar_SMTEncoding_Term.mkApp _158_462))
end
| FStar_Const.Const_string (bytes, _76_526) -> begin
(let _158_463 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _158_463))
end
| c -> begin
(let _158_465 = (let _158_464 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _158_464))
in (FStar_All.failwith _158_465))
end))

# 354 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 355 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 356 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_76_537) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_76_540) -> begin
(let _158_474 = (FStar_Syntax_Util.unrefine t)
in (aux true _158_474))
end
| _76_543 -> begin
if norm then begin
(let _158_475 = (whnf env t)
in (aux false _158_475))
end else begin
(let _158_478 = (let _158_477 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _158_476 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _158_477 _158_476)))
in (FStar_All.failwith _158_478))
end
end)))
in (aux true t0)))

# 365 "FStar.SMTEncoding.Encode.fst"
let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (
# 366 "FStar.SMTEncoding.Encode.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _76_551 -> begin
(let _158_481 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _158_481))
end)))

# 372 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 379 "FStar.SMTEncoding.Encode.fst"
let _76_555 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_531 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _158_531))
end else begin
()
end
in (
# 381 "FStar.SMTEncoding.Encode.fst"
let _76_583 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _76_562 b -> (match (_76_562) with
| (vars, guards, env, decls, names) -> begin
(
# 382 "FStar.SMTEncoding.Encode.fst"
let _76_577 = (
# 383 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 384 "FStar.SMTEncoding.Encode.fst"
let _76_568 = (gen_term_var env x)
in (match (_76_568) with
| (xxsym, xx, env') -> begin
(
# 385 "FStar.SMTEncoding.Encode.fst"
let _76_571 = (let _158_534 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _158_534 env xx))
in (match (_76_571) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_76_577) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_76_583) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 400 "FStar.SMTEncoding.Encode.fst"
let _76_590 = (encode_term t env)
in (match (_76_590) with
| (t, decls) -> begin
(let _158_539 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_158_539, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 404 "FStar.SMTEncoding.Encode.fst"
let _76_597 = (encode_term t env)
in (match (_76_597) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _158_544 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_158_544, decls))
end
| Some (f) -> begin
(let _158_545 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_158_545, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 412 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 413 "FStar.SMTEncoding.Encode.fst"
let _76_604 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _158_550 = (FStar_Syntax_Print.tag_of_term t)
in (let _158_549 = (FStar_Syntax_Print.tag_of_term t0)
in (let _158_548 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _158_550 _158_549 _158_548))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _158_555 = (let _158_554 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _158_553 = (FStar_Syntax_Print.tag_of_term t0)
in (let _158_552 = (FStar_Syntax_Print.term_to_string t0)
in (let _158_551 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _158_554 _158_553 _158_552 _158_551)))))
in (FStar_All.failwith _158_555))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _158_557 = (let _158_556 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _158_556))
in (FStar_All.failwith _158_557))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _76_615) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _76_620) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 429 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v, _76_628) -> begin
(let _158_558 = (lookup_free_var env v)
in (_158_558, []))
end
| FStar_Syntax_Syntax.Tm_type (_76_632) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _76_636) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _158_559 = (encode_const c)
in (_158_559, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 445 "FStar.SMTEncoding.Encode.fst"
let _76_647 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_76_647) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 449 "FStar.SMTEncoding.Encode.fst"
let _76_654 = (encode_binders None binders env)
in (match (_76_654) with
| (vars, guards, env', decls, _76_653) -> begin
(
# 450 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _158_560 = (varops.fresh "f")
in (_158_560, FStar_SMTEncoding_Term.Term_sort))
in (
# 451 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 452 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 453 "FStar.SMTEncoding.Encode.fst"
let _76_660 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_76_660) with
| (pre_opt, res_t) -> begin
(
# 454 "FStar.SMTEncoding.Encode.fst"
let _76_663 = (encode_term_pred None res_t env' app)
in (match (_76_663) with
| (res_pred, decls') -> begin
(
# 455 "FStar.SMTEncoding.Encode.fst"
let _76_672 = (match (pre_opt) with
| None -> begin
(let _158_561 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_158_561, decls))
end
| Some (pre) -> begin
(
# 458 "FStar.SMTEncoding.Encode.fst"
let _76_669 = (encode_formula pre env')
in (match (_76_669) with
| (guard, decls0) -> begin
(let _158_562 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_158_562, (FStar_List.append decls decls0)))
end))
end)
in (match (_76_672) with
| (guards, guard_decls) -> begin
(
# 460 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _158_564 = (let _158_563 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _158_563))
in (FStar_SMTEncoding_Term.mkForall _158_564))
in (
# 465 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _158_566 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _158_566 (FStar_List.filter (fun _76_677 -> (match (_76_677) with
| (x, _76_676) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 466 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _76_683) -> begin
(let _158_569 = (let _158_568 = (let _158_567 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _158_567))
in (FStar_SMTEncoding_Term.mkApp _158_568))
in (_158_569, []))
end
| None -> begin
(
# 472 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Tm_arrow")
in (
# 473 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 474 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _158_570 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_158_570))
end else begin
None
end
in (
# 479 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 481 "FStar.SMTEncoding.Encode.fst"
let t = (let _158_572 = (let _158_571 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _158_571))
in (FStar_SMTEncoding_Term.mkApp _158_572))
in (
# 482 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 484 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _158_574 = (let _158_573 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_158_573, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_158_574))
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 487 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _158_581 = (let _158_580 = (let _158_579 = (let _158_578 = (let _158_577 = (let _158_576 = (let _158_575 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _158_575))
in (f_has_t, _158_576))
in (FStar_SMTEncoding_Term.mkImp _158_577))
in (((f_has_t)::[])::[], (fsym)::cvars, _158_578))
in (mkForall_fuel _158_579))
in (_158_580, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_158_581))
in (
# 489 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _158_585 = (let _158_584 = (let _158_583 = (let _158_582 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _158_582))
in (FStar_SMTEncoding_Term.mkForall _158_583))
in (_158_584, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_158_585))
in (
# 492 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 493 "FStar.SMTEncoding.Encode.fst"
let _76_699 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 497 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Non_total_Tm_arrow")
in (
# 498 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 499 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (
# 500 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (let _158_587 = (let _158_586 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_158_586, None))
in FStar_SMTEncoding_Term.Assume (_158_587))
in (
# 501 "FStar.SMTEncoding.Encode.fst"
let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (
# 502 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 503 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 504 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _158_594 = (let _158_593 = (let _158_592 = (let _158_591 = (let _158_590 = (let _158_589 = (let _158_588 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _158_588))
in (f_has_t, _158_589))
in (FStar_SMTEncoding_Term.mkImp _158_590))
in (((f_has_t)::[])::[], (fsym)::[], _158_591))
in (mkForall_fuel _158_592))
in (_158_593, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_158_594))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_76_710) -> begin
(
# 511 "FStar.SMTEncoding.Encode.fst"
let _76_730 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _76_717; FStar_Syntax_Syntax.pos = _76_715; FStar_Syntax_Syntax.vars = _76_713} -> begin
(
# 513 "FStar.SMTEncoding.Encode.fst"
let _76_725 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_76_725) with
| (b, f) -> begin
(let _158_596 = (let _158_595 = (FStar_List.hd b)
in (Prims.fst _158_595))
in (_158_596, f))
end))
end
| _76_727 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_76_730) with
| (x, f) -> begin
(
# 517 "FStar.SMTEncoding.Encode.fst"
let _76_733 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_76_733) with
| (base_t, decls) -> begin
(
# 518 "FStar.SMTEncoding.Encode.fst"
let _76_737 = (gen_term_var env x)
in (match (_76_737) with
| (x, xtm, env') -> begin
(
# 519 "FStar.SMTEncoding.Encode.fst"
let _76_740 = (encode_formula f env')
in (match (_76_740) with
| (refinement, decls') -> begin
(
# 521 "FStar.SMTEncoding.Encode.fst"
let _76_743 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_743) with
| (fsym, fterm) -> begin
(
# 523 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _158_598 = (let _158_597 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_158_597, refinement))
in (FStar_SMTEncoding_Term.mkAnd _158_598))
in (
# 525 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _158_600 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _158_600 (FStar_List.filter (fun _76_748 -> (match (_76_748) with
| (y, _76_747) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 526 "FStar.SMTEncoding.Encode.fst"
let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (
# 527 "FStar.SMTEncoding.Encode.fst"
let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (
# 528 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _76_755, _76_757) -> begin
(let _158_603 = (let _158_602 = (let _158_601 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _158_601))
in (FStar_SMTEncoding_Term.mkApp _158_602))
in (_158_603, []))
end
| None -> begin
(
# 535 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Typ_refine")
in (
# 536 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 537 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 538 "FStar.SMTEncoding.Encode.fst"
let t = (let _158_605 = (let _158_604 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _158_604))
in (FStar_SMTEncoding_Term.mkApp _158_605))
in (
# 540 "FStar.SMTEncoding.Encode.fst"
let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 541 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 543 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (
# 544 "FStar.SMTEncoding.Encode.fst"
let assumption = (let _158_607 = (let _158_606 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _158_606))
in (FStar_SMTEncoding_Term.mkForall _158_607))
in (
# 546 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _158_614 = (let _158_613 = (let _158_612 = (let _158_611 = (let _158_610 = (let _158_609 = (let _158_608 = (FStar_Syntax_Print.term_to_string t0)
in Some (_158_608))
in (assumption, _158_609))
in FStar_SMTEncoding_Term.Assume (_158_610))
in (_158_611)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, None)))::_158_612)
in (tdecl)::_158_613)
in (FStar_List.append (FStar_List.append decls decls') _158_614))
in (
# 551 "FStar.SMTEncoding.Encode.fst"
let _76_770 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
# 556 "FStar.SMTEncoding.Encode.fst"
let ttm = (let _158_615 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _158_615))
in (
# 557 "FStar.SMTEncoding.Encode.fst"
let _76_779 = (encode_term_pred None k env ttm)
in (match (_76_779) with
| (t_has_k, decls) -> begin
(
# 558 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_76_782) -> begin
(
# 562 "FStar.SMTEncoding.Encode.fst"
let _76_786 = (FStar_Syntax_Util.head_and_args t0)
in (match (_76_786) with
| (head, args_e) -> begin
(match ((let _158_617 = (let _158_616 = (FStar_Syntax_Subst.compress head)
in _158_616.FStar_Syntax_Syntax.n)
in (_158_617, args_e))) with
| (FStar_Syntax_Syntax.Tm_abs (_76_788), _76_791) -> begin
(let _158_618 = (whnf env t)
in (encode_term _158_618 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (l, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (l, _), _::(v1, _)::(v2, _)::[])) when (FStar_Ident.lid_equals l.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
(
# 569 "FStar.SMTEncoding.Encode.fst"
let _76_837 = (encode_term v1 env)
in (match (_76_837) with
| (v1, decls1) -> begin
(
# 570 "FStar.SMTEncoding.Encode.fst"
let _76_840 = (encode_term v2 env)
in (match (_76_840) with
| (v2, decls2) -> begin
(let _158_619 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_158_619, (FStar_List.append decls1 decls2)))
end))
end))
end
| _76_842 -> begin
(
# 574 "FStar.SMTEncoding.Encode.fst"
let _76_845 = (encode_args args_e env)
in (match (_76_845) with
| (args, decls) -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 577 "FStar.SMTEncoding.Encode.fst"
let _76_850 = (encode_term head env)
in (match (_76_850) with
| (head, decls') -> begin
(
# 578 "FStar.SMTEncoding.Encode.fst"
let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(
# 582 "FStar.SMTEncoding.Encode.fst"
let _76_859 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_76_859) with
| (formals, rest) -> begin
(
# 583 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _76_863 _76_867 -> (match ((_76_863, _76_867)) with
| ((bv, _76_862), (a, _76_866)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 584 "FStar.SMTEncoding.Encode.fst"
let ty = (let _158_624 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _158_624 (FStar_Syntax_Subst.subst subst)))
in (
# 585 "FStar.SMTEncoding.Encode.fst"
let _76_872 = (encode_term_pred None ty env app_tm)
in (match (_76_872) with
| (has_type, decls'') -> begin
(
# 586 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 587 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _158_626 = (let _158_625 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_158_625, None))
in FStar_SMTEncoding_Term.Assume (_158_626))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 591 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 592 "FStar.SMTEncoding.Encode.fst"
let _76_879 = (lookup_free_var_sym env fv)
in (match (_76_879) with
| (fname, fuel_args) -> begin
(
# 593 "FStar.SMTEncoding.Encode.fst"
let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (
# 596 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Subst.compress head)
in (
# 598 "FStar.SMTEncoding.Encode.fst"
let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(let _158_630 = (let _158_629 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _158_629 Prims.snd))
in Some (_158_630))
end
| FStar_Syntax_Syntax.Tm_ascribed (_76_917, t, _76_920) -> begin
Some (t)
end
| _76_924 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 609 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _158_631 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _158_631))
in (
# 610 "FStar.SMTEncoding.Encode.fst"
let _76_932 = (curried_arrow_formals_comp head_type)
in (match (_76_932) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _76_954 -> begin
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
# 624 "FStar.SMTEncoding.Encode.fst"
let _76_963 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_76_963) with
| (bs, body, opening) -> begin
(
# 625 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _76_965 -> (match (()) with
| () -> begin
(
# 626 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 627 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _158_634 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_158_634, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 632 "FStar.SMTEncoding.Encode.fst"
let _76_969 = (let _158_636 = (let _158_635 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _158_635))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _158_636))
in (fallback ()))
end
| Some (lc) -> begin
if (let _158_637 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _158_637)) then begin
(fallback ())
end else begin
(
# 638 "FStar.SMTEncoding.Encode.fst"
let c0 = (lc.FStar_Syntax_Syntax.comp ())
in (
# 639 "FStar.SMTEncoding.Encode.fst"
let c = (FStar_Syntax_Subst.subst_comp opening c0)
in (
# 642 "FStar.SMTEncoding.Encode.fst"
let _76_981 = (encode_binders None bs env)
in (match (_76_981) with
| (vars, guards, envbody, decls, _76_980) -> begin
(
# 643 "FStar.SMTEncoding.Encode.fst"
let _76_984 = (encode_term body envbody)
in (match (_76_984) with
| (body, decls') -> begin
(
# 644 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _158_641 = (let _158_640 = (let _158_639 = (let _158_638 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_158_638, body))
in (FStar_SMTEncoding_Term.mkImp _158_639))
in ([], vars, _158_640))
in (FStar_SMTEncoding_Term.mkForall _158_641))
in (
# 645 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 646 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _76_990, _76_992) -> begin
(let _158_644 = (let _158_643 = (let _158_642 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _158_642))
in (FStar_SMTEncoding_Term.mkApp _158_643))
in (_158_644, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(
# 655 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 656 "FStar.SMTEncoding.Encode.fst"
let fsym = (varops.fresh "Exp_abs")
in (
# 657 "FStar.SMTEncoding.Encode.fst"
let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 658 "FStar.SMTEncoding.Encode.fst"
let f = (let _158_646 = (let _158_645 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _158_645))
in (FStar_SMTEncoding_Term.mkApp _158_646))
in (
# 659 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 660 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 661 "FStar.SMTEncoding.Encode.fst"
let _76_1007 = (encode_term_pred None tfun env f)
in (match (_76_1007) with
| (f_has_t, decls'') -> begin
(
# 662 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _158_648 = (let _158_647 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_158_647, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_158_648))
in (
# 664 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _158_655 = (let _158_654 = (let _158_653 = (let _158_652 = (let _158_651 = (let _158_650 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _158_649 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_158_650, _158_649)))
in (FStar_SMTEncoding_Term.mkImp _158_651))
in (((app)::[])::[], (FStar_List.append vars cvars), _158_652))
in (FStar_SMTEncoding_Term.mkForall _158_653))
in (_158_654, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_158_655))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 667 "FStar.SMTEncoding.Encode.fst"
let _76_1011 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_76_1014, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_76_1026); FStar_Syntax_Syntax.lbunivs = _76_1024; FStar_Syntax_Syntax.lbtyp = _76_1022; FStar_Syntax_Syntax.lbeff = _76_1020; FStar_Syntax_Syntax.lbdef = _76_1018}::_76_1016), _76_1032) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _76_1041; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _76_1038; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_76_1051) -> begin
(
# 680 "FStar.SMTEncoding.Encode.fst"
let _76_1053 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 681 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 682 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _158_656 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_158_656, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 689 "FStar.SMTEncoding.Encode.fst"
let _76_1069 = (encode_term e1 env)
in (match (_76_1069) with
| (ee1, decls1) -> begin
(
# 690 "FStar.SMTEncoding.Encode.fst"
let _76_1072 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_76_1072) with
| (xs, e2) -> begin
(
# 691 "FStar.SMTEncoding.Encode.fst"
let _76_1076 = (FStar_List.hd xs)
in (match (_76_1076) with
| (x, _76_1075) -> begin
(
# 692 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 693 "FStar.SMTEncoding.Encode.fst"
let _76_1080 = (encode_term e2 env')
in (match (_76_1080) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 697 "FStar.SMTEncoding.Encode.fst"
let _76_1088 = (encode_term e env)
in (match (_76_1088) with
| (scr, decls) -> begin
(
# 698 "FStar.SMTEncoding.Encode.fst"
let _76_1125 = (FStar_List.fold_right (fun b _76_1092 -> (match (_76_1092) with
| (else_case, decls) -> begin
(
# 699 "FStar.SMTEncoding.Encode.fst"
let _76_1096 = (FStar_Syntax_Subst.open_branch b)
in (match (_76_1096) with
| (p, w, br) -> begin
(
# 700 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _76_1100 _76_1103 -> (match ((_76_1100, _76_1103)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 702 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 703 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 704 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _76_1109 -> (match (_76_1109) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 705 "FStar.SMTEncoding.Encode.fst"
let _76_1119 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 708 "FStar.SMTEncoding.Encode.fst"
let _76_1116 = (encode_term w env)
in (match (_76_1116) with
| (w, decls2) -> begin
(let _158_690 = (let _158_689 = (let _158_688 = (let _158_687 = (let _158_686 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _158_686))
in (FStar_SMTEncoding_Term.mkEq _158_687))
in (guard, _158_688))
in (FStar_SMTEncoding_Term.mkAnd _158_689))
in (_158_690, decls2))
end))
end)
in (match (_76_1119) with
| (guard, decls2) -> begin
(
# 710 "FStar.SMTEncoding.Encode.fst"
let _76_1122 = (encode_br br env)
in (match (_76_1122) with
| (br, decls3) -> begin
(let _158_691 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_158_691, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_76_1125) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _76_1131 -> begin
(let _158_694 = (encode_one_pat env pat)
in (_158_694)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 724 "FStar.SMTEncoding.Encode.fst"
let _76_1134 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_697 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _158_697))
end else begin
()
end
in (
# 725 "FStar.SMTEncoding.Encode.fst"
let _76_1138 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_76_1138) with
| (vars, pat_term) -> begin
(
# 727 "FStar.SMTEncoding.Encode.fst"
let _76_1150 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _76_1141 v -> (match (_76_1141) with
| (env, vars) -> begin
(
# 728 "FStar.SMTEncoding.Encode.fst"
let _76_1147 = (gen_term_var env v)
in (match (_76_1147) with
| (xx, _76_1145, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_76_1150) with
| (env, vars) -> begin
(
# 731 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_76_1155) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _158_705 = (let _158_704 = (encode_const c)
in (scrutinee, _158_704))
in (FStar_SMTEncoding_Term.mkEq _158_705))
end
| FStar_Syntax_Syntax.Pat_cons ((f, _76_1170), args) -> begin
(
# 739 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.v scrutinee)
in (
# 740 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _76_1180 -> (match (_76_1180) with
| (arg, _76_1179) -> begin
(
# 741 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _158_708 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _158_708)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 745 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_76_1187) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_76_1197) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons ((f, _76_1201), args) -> begin
(let _158_716 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _76_1210 -> (match (_76_1210) with
| (arg, _76_1209) -> begin
(
# 757 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _158_715 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _158_715)))
end))))
in (FStar_All.pipe_right _158_716 FStar_List.flatten))
end))
in (
# 761 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _76_1213 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (
# 763 "FStar.SMTEncoding.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (
# 773 "FStar.SMTEncoding.Encode.fst"
let _76_1229 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _76_1219 _76_1223 -> (match ((_76_1219, _76_1223)) with
| ((tms, decls), (t, _76_1222)) -> begin
(
# 774 "FStar.SMTEncoding.Encode.fst"
let _76_1226 = (encode_term t env)
in (match (_76_1226) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_76_1229) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 779 "FStar.SMTEncoding.Encode.fst"
let _76_1235 = (encode_formula_with_labels phi env)
in (match (_76_1235) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _76_1238 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 786 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 787 "FStar.SMTEncoding.Encode.fst"
let _76_1247 = (let _158_731 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _158_731))
in (match (_76_1247) with
| (head, args) -> begin
(match ((let _158_733 = (let _158_732 = (FStar_Syntax_Util.un_uinst head)
in _158_732.FStar_Syntax_Syntax.n)
in (_158_733, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _76_1250), _76_1254) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _76_1258), _76_1270::(hd, _76_1267)::(tl, _76_1263)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid) -> begin
(let _158_734 = (list_elements tl)
in (hd)::_158_734)
end
| _76_1274 -> begin
(
# 792 "FStar.SMTEncoding.Encode.fst"
let _76_1275 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 794 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 795 "FStar.SMTEncoding.Encode.fst"
let _76_1281 = (let _158_737 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _158_737 FStar_Syntax_Util.head_and_args))
in (match (_76_1281) with
| (head, args) -> begin
(match ((let _158_739 = (let _158_738 = (FStar_Syntax_Util.un_uinst head)
in _158_738.FStar_Syntax_Syntax.n)
in (_158_739, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _76_1284), (_76_1292, _76_1294)::(e, _76_1289)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _76_1300), (e, _76_1305)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _76_1310 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (
# 801 "FStar.SMTEncoding.Encode.fst"
let lemma_pats = (fun p -> (
# 802 "FStar.SMTEncoding.Encode.fst"
let elts = (list_elements p)
in (
# 803 "FStar.SMTEncoding.Encode.fst"
let smt_pat_or = (fun t -> (
# 804 "FStar.SMTEncoding.Encode.fst"
let _76_1318 = (let _158_744 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _158_744 FStar_Syntax_Util.head_and_args))
in (match (_76_1318) with
| (head, args) -> begin
(match ((let _158_746 = (let _158_745 = (FStar_Syntax_Util.un_uinst head)
in _158_745.FStar_Syntax_Syntax.n)
in (_158_746, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _76_1321), (e, _76_1326)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _76_1331 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _158_749 = (list_elements e)
in (FStar_All.pipe_right _158_749 (FStar_List.map (fun branch -> (let _158_748 = (list_elements branch)
in (FStar_All.pipe_right _158_748 (FStar_List.map one_pat)))))))
end
| _76_1338 -> begin
(let _158_750 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_158_750)::[])
end)
end
| _76_1340 -> begin
(let _158_751 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_158_751)::[])
end))))
in (
# 818 "FStar.SMTEncoding.Encode.fst"
let _76_1374 = (match ((let _158_752 = (FStar_Syntax_Subst.compress t)
in _158_752.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 820 "FStar.SMTEncoding.Encode.fst"
let _76_1347 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_76_1347) with
| (binders, c) -> begin
(
# 821 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _76_1359)::(post, _76_1355)::(pats, _76_1351)::[] -> begin
(
# 824 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _158_753 = (lemma_pats pats')
in (binders, pre, post, _158_753)))
end
| _76_1367 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _76_1369 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_76_1374) with
| (binders, pre, post, patterns) -> begin
(
# 832 "FStar.SMTEncoding.Encode.fst"
let _76_1381 = (encode_binders None binders env)
in (match (_76_1381) with
| (vars, guards, env, decls, _76_1380) -> begin
(
# 835 "FStar.SMTEncoding.Encode.fst"
let _76_1394 = (let _158_757 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 836 "FStar.SMTEncoding.Encode.fst"
let _76_1391 = (let _158_756 = (FStar_All.pipe_right branch (FStar_List.map (fun _76_1386 -> (match (_76_1386) with
| (t, _76_1385) -> begin
(encode_term t (
# 836 "FStar.SMTEncoding.Encode.fst"
let _76_1387 = env
in {bindings = _76_1387.bindings; depth = _76_1387.depth; tcenv = _76_1387.tcenv; warn = _76_1387.warn; cache = _76_1387.cache; nolabels = _76_1387.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _76_1387.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _158_756 FStar_List.unzip))
in (match (_76_1391) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _158_757 FStar_List.unzip))
in (match (_76_1394) with
| (pats, decls') -> begin
(
# 839 "FStar.SMTEncoding.Encode.fst"
let decls' = (FStar_List.flatten decls')
in (
# 841 "FStar.SMTEncoding.Encode.fst"
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _158_760 = (let _158_759 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _158_759 e))
in (_158_760)::p))))
end
| _76_1404 -> begin
(
# 849 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _158_766 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_158_766)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _158_768 = (let _158_767 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _158_767 tl))
in (aux _158_768 vars))
end
| _76_1416 -> begin
pats
end))
in (let _158_769 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _158_769 vars)))
end)
end)
in (
# 856 "FStar.SMTEncoding.Encode.fst"
let env = (
# 856 "FStar.SMTEncoding.Encode.fst"
let _76_1418 = env
in {bindings = _76_1418.bindings; depth = _76_1418.depth; tcenv = _76_1418.tcenv; warn = _76_1418.warn; cache = _76_1418.cache; nolabels = true; use_zfuel_name = _76_1418.use_zfuel_name; encode_non_total_function_typ = _76_1418.encode_non_total_function_typ})
in (
# 857 "FStar.SMTEncoding.Encode.fst"
let _76_1423 = (let _158_770 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _158_770 env))
in (match (_76_1423) with
| (pre, decls'') -> begin
(
# 858 "FStar.SMTEncoding.Encode.fst"
let _76_1426 = (let _158_771 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _158_771 env))
in (match (_76_1426) with
| (post, decls''') -> begin
(
# 859 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _158_776 = (let _158_775 = (let _158_774 = (let _158_773 = (let _158_772 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_158_772, post))
in (FStar_SMTEncoding_Term.mkImp _158_773))
in (pats, vars, _158_774))
in (FStar_SMTEncoding_Term.mkForall _158_775))
in (_158_776, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * labels * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 863 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 864 "FStar.SMTEncoding.Encode.fst"
let _76_1440 = (FStar_Util.fold_map (fun decls x -> (
# 864 "FStar.SMTEncoding.Encode.fst"
let _76_1437 = (encode_term (Prims.fst x) env)
in (match (_76_1437) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_76_1440) with
| (decls, args) -> begin
(let _158_794 = (f args)
in (_158_794, [], decls))
end)))
in (
# 867 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _76_1443 -> (f, [], []))
in (
# 868 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _158_808 = (FStar_List.hd l)
in (FStar_All.pipe_left f _158_808)))
in (
# 869 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _76_8 -> (match (_76_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _76_1454 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 873 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 874 "FStar.SMTEncoding.Encode.fst"
let _76_1474 = (FStar_List.fold_right (fun _76_1462 _76_1466 -> (match ((_76_1462, _76_1466)) with
| ((t, _76_1461), (phis, labs, decls)) -> begin
(
# 876 "FStar.SMTEncoding.Encode.fst"
let _76_1470 = (encode_formula_with_labels t env)
in (match (_76_1470) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end)) l ([], [], []))
in (match (_76_1474) with
| (phis, labs, decls) -> begin
(let _158_833 = (f phis)
in (_158_833, labs, decls))
end)))
in (
# 881 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _76_9 -> (match (_76_9) with
| _76_1481::_76_1479::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 885 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _76_10 -> (match (_76_10) with
| (lhs, _76_1492)::(rhs, _76_1488)::[] -> begin
(
# 887 "FStar.SMTEncoding.Encode.fst"
let _76_1498 = (encode_formula_with_labels rhs env)
in (match (_76_1498) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _76_1501) -> begin
(l1, labs1, decls1)
end
| _76_1505 -> begin
(
# 891 "FStar.SMTEncoding.Encode.fst"
let _76_1509 = (encode_formula_with_labels lhs env)
in (match (_76_1509) with
| (l2, labs2, decls2) -> begin
(let _158_838 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_158_838, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _76_1511 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 896 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _76_11 -> (match (_76_11) with
| (guard, _76_1524)::(_then, _76_1520)::(_else, _76_1516)::[] -> begin
(
# 898 "FStar.SMTEncoding.Encode.fst"
let _76_1530 = (encode_formula_with_labels guard env)
in (match (_76_1530) with
| (g, labs1, decls1) -> begin
(
# 899 "FStar.SMTEncoding.Encode.fst"
let _76_1534 = (encode_formula_with_labels _then env)
in (match (_76_1534) with
| (t, labs2, decls2) -> begin
(
# 900 "FStar.SMTEncoding.Encode.fst"
let _76_1538 = (encode_formula_with_labels _else env)
in (match (_76_1538) with
| (e, labs3, decls3) -> begin
(
# 901 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _76_1541 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 906 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _158_850 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _158_850)))
in (
# 907 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _158_903 = (let _158_859 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _158_859))
in (let _158_902 = (let _158_901 = (let _158_865 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _158_865))
in (let _158_900 = (let _158_899 = (let _158_898 = (let _158_874 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _158_874))
in (let _158_897 = (let _158_896 = (let _158_895 = (let _158_883 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _158_883))
in (_158_895)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_158_896)
in (_158_898)::_158_897))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_158_899)
in (_158_901)::_158_900))
in (_158_903)::_158_902))
in (
# 919 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 921 "FStar.SMTEncoding.Encode.fst"
let _76_1560 = (encode_formula_with_labels phi' env)
in (match (_76_1560) with
| (phi, labs, decls) -> begin
(let _158_906 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_158_906, [], decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 925 "FStar.SMTEncoding.Encode.fst"
let _76_1567 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_76_1567) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _76_1574; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _76_1571; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 929 "FStar.SMTEncoding.Encode.fst"
let _76_1585 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_76_1585) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, _76_1596::(x, _76_1593)::(t, _76_1589)::[]) -> begin
(
# 933 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _76_1603) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.has_type_lid) -> begin
(
# 936 "FStar.SMTEncoding.Encode.fst"
let _76_1608 = (encode_term x env)
in (match (_76_1608) with
| (x, decls) -> begin
(
# 937 "FStar.SMTEncoding.Encode.fst"
let _76_1611 = (encode_term t env)
in (match (_76_1611) with
| (t, decls') -> begin
(let _158_907 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_158_907, [], (FStar_List.append decls decls')))
end))
end))
end
| _76_1613 -> begin
(
# 940 "FStar.SMTEncoding.Encode.fst"
let _76_1616 = (encode_term phi env)
in (match (_76_1616) with
| (tt, decls) -> begin
(let _158_908 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_158_908, [], decls))
end))
end))
end
| _76_1618 -> begin
(
# 945 "FStar.SMTEncoding.Encode.fst"
let _76_1621 = (encode_term phi env)
in (match (_76_1621) with
| (tt, decls) -> begin
(let _158_909 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_158_909, [], decls))
end))
end))
in (
# 948 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 949 "FStar.SMTEncoding.Encode.fst"
let _76_1633 = (encode_binders None bs env)
in (match (_76_1633) with
| (vars, guards, env, decls, _76_1632) -> begin
(
# 950 "FStar.SMTEncoding.Encode.fst"
let _76_1646 = (let _158_921 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 951 "FStar.SMTEncoding.Encode.fst"
let _76_1643 = (let _158_920 = (FStar_All.pipe_right p (FStar_List.map (fun _76_1638 -> (match (_76_1638) with
| (t, _76_1637) -> begin
(encode_term t (
# 951 "FStar.SMTEncoding.Encode.fst"
let _76_1639 = env
in {bindings = _76_1639.bindings; depth = _76_1639.depth; tcenv = _76_1639.tcenv; warn = _76_1639.warn; cache = _76_1639.cache; nolabels = _76_1639.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _76_1639.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _158_920 FStar_List.unzip))
in (match (_76_1643) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _158_921 FStar_List.unzip))
in (match (_76_1646) with
| (pats, decls') -> begin
(
# 953 "FStar.SMTEncoding.Encode.fst"
let _76_1650 = (encode_formula_with_labels body env)
in (match (_76_1650) with
| (body, labs, decls'') -> begin
(let _158_922 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _158_922, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 956 "FStar.SMTEncoding.Encode.fst"
let _76_1651 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_923 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _158_923))
end else begin
()
end
in (
# 958 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _76_1663 -> (match (_76_1663) with
| (l, _76_1662) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_76_1666, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 968 "FStar.SMTEncoding.Encode.fst"
let _76_1676 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_940 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _158_940))
end else begin
()
end
in (
# 971 "FStar.SMTEncoding.Encode.fst"
let _76_1684 = (encode_q_body env vars pats body)
in (match (_76_1684) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _158_943 = (let _158_942 = (let _158_941 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _158_941))
in (FStar_SMTEncoding_Term.mkForall _158_942))
in (_158_943, labs, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 975 "FStar.SMTEncoding.Encode.fst"
let _76_1697 = (encode_q_body env vars pats body)
in (match (_76_1697) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _158_946 = (let _158_945 = (let _158_944 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _158_944))
in (FStar_SMTEncoding_Term.mkExists _158_945))
in (_158_946, labs, decls))
end))
end))))))))))))))))

# 984 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 984 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 990 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 991 "FStar.SMTEncoding.Encode.fst"
let _76_1703 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_1703) with
| (asym, a) -> begin
(
# 992 "FStar.SMTEncoding.Encode.fst"
let _76_1706 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_1706) with
| (xsym, x) -> begin
(
# 993 "FStar.SMTEncoding.Encode.fst"
let _76_1709 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_1709) with
| (ysym, y) -> begin
(
# 994 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 995 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 996 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _158_989 = (let _158_988 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _158_988))
in (FStar_SMTEncoding_Term.mkApp _158_989))
in (
# 997 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _158_991 = (let _158_990 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _158_990, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_158_991))
in (let _158_997 = (let _158_996 = (let _158_995 = (let _158_994 = (let _158_993 = (let _158_992 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _158_992))
in (FStar_SMTEncoding_Term.mkForall _158_993))
in (_158_994, None))
in FStar_SMTEncoding_Term.Assume (_158_995))
in (_158_996)::[])
in (vname_decl)::_158_997))))
in (
# 1000 "FStar.SMTEncoding.Encode.fst"
let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1001 "FStar.SMTEncoding.Encode.fst"
let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1002 "FStar.SMTEncoding.Encode.fst"
let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1003 "FStar.SMTEncoding.Encode.fst"
let prims = (let _158_1157 = (let _158_1006 = (let _158_1005 = (let _158_1004 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1004))
in (quant axy _158_1005))
in (FStar_Syntax_Const.op_Eq, _158_1006))
in (let _158_1156 = (let _158_1155 = (let _158_1013 = (let _158_1012 = (let _158_1011 = (let _158_1010 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _158_1010))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1011))
in (quant axy _158_1012))
in (FStar_Syntax_Const.op_notEq, _158_1013))
in (let _158_1154 = (let _158_1153 = (let _158_1022 = (let _158_1021 = (let _158_1020 = (let _158_1019 = (let _158_1018 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1017 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1018, _158_1017)))
in (FStar_SMTEncoding_Term.mkLT _158_1019))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1020))
in (quant xy _158_1021))
in (FStar_Syntax_Const.op_LT, _158_1022))
in (let _158_1152 = (let _158_1151 = (let _158_1031 = (let _158_1030 = (let _158_1029 = (let _158_1028 = (let _158_1027 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1026 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1027, _158_1026)))
in (FStar_SMTEncoding_Term.mkLTE _158_1028))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1029))
in (quant xy _158_1030))
in (FStar_Syntax_Const.op_LTE, _158_1031))
in (let _158_1150 = (let _158_1149 = (let _158_1040 = (let _158_1039 = (let _158_1038 = (let _158_1037 = (let _158_1036 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1035 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1036, _158_1035)))
in (FStar_SMTEncoding_Term.mkGT _158_1037))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1038))
in (quant xy _158_1039))
in (FStar_Syntax_Const.op_GT, _158_1040))
in (let _158_1148 = (let _158_1147 = (let _158_1049 = (let _158_1048 = (let _158_1047 = (let _158_1046 = (let _158_1045 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1044 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1045, _158_1044)))
in (FStar_SMTEncoding_Term.mkGTE _158_1046))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1047))
in (quant xy _158_1048))
in (FStar_Syntax_Const.op_GTE, _158_1049))
in (let _158_1146 = (let _158_1145 = (let _158_1058 = (let _158_1057 = (let _158_1056 = (let _158_1055 = (let _158_1054 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1053 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1054, _158_1053)))
in (FStar_SMTEncoding_Term.mkSub _158_1055))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1056))
in (quant xy _158_1057))
in (FStar_Syntax_Const.op_Subtraction, _158_1058))
in (let _158_1144 = (let _158_1143 = (let _158_1065 = (let _158_1064 = (let _158_1063 = (let _158_1062 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _158_1062))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1063))
in (quant qx _158_1064))
in (FStar_Syntax_Const.op_Minus, _158_1065))
in (let _158_1142 = (let _158_1141 = (let _158_1074 = (let _158_1073 = (let _158_1072 = (let _158_1071 = (let _158_1070 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1069 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1070, _158_1069)))
in (FStar_SMTEncoding_Term.mkAdd _158_1071))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1072))
in (quant xy _158_1073))
in (FStar_Syntax_Const.op_Addition, _158_1074))
in (let _158_1140 = (let _158_1139 = (let _158_1083 = (let _158_1082 = (let _158_1081 = (let _158_1080 = (let _158_1079 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1078 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1079, _158_1078)))
in (FStar_SMTEncoding_Term.mkMul _158_1080))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1081))
in (quant xy _158_1082))
in (FStar_Syntax_Const.op_Multiply, _158_1083))
in (let _158_1138 = (let _158_1137 = (let _158_1092 = (let _158_1091 = (let _158_1090 = (let _158_1089 = (let _158_1088 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1087 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1088, _158_1087)))
in (FStar_SMTEncoding_Term.mkDiv _158_1089))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1090))
in (quant xy _158_1091))
in (FStar_Syntax_Const.op_Division, _158_1092))
in (let _158_1136 = (let _158_1135 = (let _158_1101 = (let _158_1100 = (let _158_1099 = (let _158_1098 = (let _158_1097 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1096 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1097, _158_1096)))
in (FStar_SMTEncoding_Term.mkMod _158_1098))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1099))
in (quant xy _158_1100))
in (FStar_Syntax_Const.op_Modulus, _158_1101))
in (let _158_1134 = (let _158_1133 = (let _158_1110 = (let _158_1109 = (let _158_1108 = (let _158_1107 = (let _158_1106 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _158_1105 = (FStar_SMTEncoding_Term.unboxBool y)
in (_158_1106, _158_1105)))
in (FStar_SMTEncoding_Term.mkAnd _158_1107))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1108))
in (quant xy _158_1109))
in (FStar_Syntax_Const.op_And, _158_1110))
in (let _158_1132 = (let _158_1131 = (let _158_1119 = (let _158_1118 = (let _158_1117 = (let _158_1116 = (let _158_1115 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _158_1114 = (FStar_SMTEncoding_Term.unboxBool y)
in (_158_1115, _158_1114)))
in (FStar_SMTEncoding_Term.mkOr _158_1116))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1117))
in (quant xy _158_1118))
in (FStar_Syntax_Const.op_Or, _158_1119))
in (let _158_1130 = (let _158_1129 = (let _158_1126 = (let _158_1125 = (let _158_1124 = (let _158_1123 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _158_1123))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1124))
in (quant qx _158_1125))
in (FStar_Syntax_Const.op_Negation, _158_1126))
in (_158_1129)::[])
in (_158_1131)::_158_1130))
in (_158_1133)::_158_1132))
in (_158_1135)::_158_1134))
in (_158_1137)::_158_1136))
in (_158_1139)::_158_1138))
in (_158_1141)::_158_1140))
in (_158_1143)::_158_1142))
in (_158_1145)::_158_1144))
in (_158_1147)::_158_1146))
in (_158_1149)::_158_1148))
in (_158_1151)::_158_1150))
in (_158_1153)::_158_1152))
in (_158_1155)::_158_1154))
in (_158_1157)::_158_1156))
in (
# 1020 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _158_1189 = (FStar_All.pipe_right prims (FStar_List.filter (fun _76_1729 -> (match (_76_1729) with
| (l', _76_1728) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _158_1189 (FStar_List.collect (fun _76_1733 -> (match (_76_1733) with
| (_76_1731, b) -> begin
(b v)
end))))))
in (
# 1022 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _76_1739 -> (match (_76_1739) with
| (l', _76_1738) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1027 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1028 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1029 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1031 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1032 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1034 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun _76_1745 tt -> (
# 1035 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _158_1221 = (let _158_1212 = (let _158_1211 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_158_1211, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_158_1212))
in (let _158_1220 = (let _158_1219 = (let _158_1218 = (let _158_1217 = (let _158_1216 = (let _158_1215 = (let _158_1214 = (let _158_1213 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _158_1213))
in (FStar_SMTEncoding_Term.mkImp _158_1214))
in (((typing_pred)::[])::[], (xx)::[], _158_1215))
in (mkForall_fuel _158_1216))
in (_158_1217, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1218))
in (_158_1219)::[])
in (_158_1221)::_158_1220))))
in (
# 1038 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun _76_1750 tt -> (
# 1039 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1040 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1041 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _158_1242 = (let _158_1231 = (let _158_1230 = (let _158_1229 = (let _158_1228 = (let _158_1227 = (let _158_1226 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _158_1226))
in (FStar_SMTEncoding_Term.mkImp _158_1227))
in (((typing_pred)::[])::[], (xx)::[], _158_1228))
in (mkForall_fuel _158_1229))
in (_158_1230, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1231))
in (let _158_1241 = (let _158_1240 = (let _158_1239 = (let _158_1238 = (let _158_1237 = (let _158_1236 = (let _158_1233 = (let _158_1232 = (FStar_SMTEncoding_Term.boxBool b)
in (_158_1232)::[])
in (_158_1233)::[])
in (let _158_1235 = (let _158_1234 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _158_1234 tt))
in (_158_1236, (bb)::[], _158_1235)))
in (FStar_SMTEncoding_Term.mkForall _158_1237))
in (_158_1238, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_158_1239))
in (_158_1240)::[])
in (_158_1242)::_158_1241))))))
in (
# 1044 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun _76_1757 tt -> (
# 1045 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1046 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1047 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1048 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1049 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1050 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1051 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _158_1254 = (let _158_1253 = (let _158_1252 = (let _158_1251 = (let _158_1250 = (let _158_1249 = (FStar_SMTEncoding_Term.boxInt a)
in (let _158_1248 = (let _158_1247 = (FStar_SMTEncoding_Term.boxInt b)
in (_158_1247)::[])
in (_158_1249)::_158_1248))
in (tt)::_158_1250)
in (tt)::_158_1251)
in ("Prims.Precedes", _158_1252))
in (FStar_SMTEncoding_Term.mkApp _158_1253))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _158_1254))
in (
# 1052 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _158_1255 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _158_1255))
in (let _158_1297 = (let _158_1261 = (let _158_1260 = (let _158_1259 = (let _158_1258 = (let _158_1257 = (let _158_1256 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _158_1256))
in (FStar_SMTEncoding_Term.mkImp _158_1257))
in (((typing_pred)::[])::[], (xx)::[], _158_1258))
in (mkForall_fuel _158_1259))
in (_158_1260, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1261))
in (let _158_1296 = (let _158_1295 = (let _158_1269 = (let _158_1268 = (let _158_1267 = (let _158_1266 = (let _158_1263 = (let _158_1262 = (FStar_SMTEncoding_Term.boxInt b)
in (_158_1262)::[])
in (_158_1263)::[])
in (let _158_1265 = (let _158_1264 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _158_1264 tt))
in (_158_1266, (bb)::[], _158_1265)))
in (FStar_SMTEncoding_Term.mkForall _158_1267))
in (_158_1268, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_158_1269))
in (let _158_1294 = (let _158_1293 = (let _158_1292 = (let _158_1291 = (let _158_1290 = (let _158_1289 = (let _158_1288 = (let _158_1287 = (let _158_1286 = (let _158_1285 = (let _158_1284 = (let _158_1283 = (let _158_1272 = (let _158_1271 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1270 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_158_1271, _158_1270)))
in (FStar_SMTEncoding_Term.mkGT _158_1272))
in (let _158_1282 = (let _158_1281 = (let _158_1275 = (let _158_1274 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _158_1273 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_158_1274, _158_1273)))
in (FStar_SMTEncoding_Term.mkGTE _158_1275))
in (let _158_1280 = (let _158_1279 = (let _158_1278 = (let _158_1277 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _158_1276 = (FStar_SMTEncoding_Term.unboxInt x)
in (_158_1277, _158_1276)))
in (FStar_SMTEncoding_Term.mkLT _158_1278))
in (_158_1279)::[])
in (_158_1281)::_158_1280))
in (_158_1283)::_158_1282))
in (typing_pred_y)::_158_1284)
in (typing_pred)::_158_1285)
in (FStar_SMTEncoding_Term.mk_and_l _158_1286))
in (_158_1287, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _158_1288))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _158_1289))
in (mkForall_fuel _158_1290))
in (_158_1291, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_158_1292))
in (_158_1293)::[])
in (_158_1295)::_158_1294))
in (_158_1297)::_158_1296)))))))))))
in (
# 1064 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun _76_1769 tt -> (let _158_1306 = (let _158_1305 = (let _158_1304 = (let _158_1303 = (let _158_1302 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _158_1302))
in (FStar_SMTEncoding_Term.mkEq _158_1303))
in (_158_1304, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_158_1305))
in (_158_1306)::[]))
in (
# 1066 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun _76_1773 tt -> (
# 1067 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1068 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1069 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _158_1327 = (let _158_1316 = (let _158_1315 = (let _158_1314 = (let _158_1313 = (let _158_1312 = (let _158_1311 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _158_1311))
in (FStar_SMTEncoding_Term.mkImp _158_1312))
in (((typing_pred)::[])::[], (xx)::[], _158_1313))
in (mkForall_fuel _158_1314))
in (_158_1315, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1316))
in (let _158_1326 = (let _158_1325 = (let _158_1324 = (let _158_1323 = (let _158_1322 = (let _158_1321 = (let _158_1318 = (let _158_1317 = (FStar_SMTEncoding_Term.boxString b)
in (_158_1317)::[])
in (_158_1318)::[])
in (let _158_1320 = (let _158_1319 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _158_1319 tt))
in (_158_1321, (bb)::[], _158_1320)))
in (FStar_SMTEncoding_Term.mkForall _158_1322))
in (_158_1323, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_158_1324))
in (_158_1325)::[])
in (_158_1327)::_158_1326))))))
in (
# 1072 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun reft_name _76_1781 -> (
# 1073 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1074 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1075 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1076 "FStar.SMTEncoding.Encode.fst"
let refa = (let _158_1334 = (let _158_1333 = (let _158_1332 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_158_1332)::[])
in (reft_name, _158_1333))
in (FStar_SMTEncoding_Term.mkApp _158_1334))
in (
# 1077 "FStar.SMTEncoding.Encode.fst"
let refb = (let _158_1337 = (let _158_1336 = (let _158_1335 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_158_1335)::[])
in (reft_name, _158_1336))
in (FStar_SMTEncoding_Term.mkApp _158_1337))
in (
# 1078 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1079 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _158_1356 = (let _158_1343 = (let _158_1342 = (let _158_1341 = (let _158_1340 = (let _158_1339 = (let _158_1338 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _158_1338))
in (FStar_SMTEncoding_Term.mkImp _158_1339))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _158_1340))
in (mkForall_fuel _158_1341))
in (_158_1342, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1343))
in (let _158_1355 = (let _158_1354 = (let _158_1353 = (let _158_1352 = (let _158_1351 = (let _158_1350 = (let _158_1349 = (let _158_1348 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _158_1347 = (let _158_1346 = (let _158_1345 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _158_1344 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_158_1345, _158_1344)))
in (FStar_SMTEncoding_Term.mkEq _158_1346))
in (_158_1348, _158_1347)))
in (FStar_SMTEncoding_Term.mkImp _158_1349))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _158_1350))
in (mkForall_fuel' 2 _158_1351))
in (_158_1352, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_158_1353))
in (_158_1354)::[])
in (_158_1356)::_158_1355))))))))))
in (
# 1083 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun _76_1791 false_tm -> (
# 1084 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _158_1363 = (let _158_1362 = (let _158_1361 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_158_1361, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1362))
in (_158_1363)::[])))
in (
# 1086 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun conj _76_1797 -> (
# 1087 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1088 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1089 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1090 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1091 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1370 = (let _158_1369 = (let _158_1368 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_158_1368)::[])
in ("Valid", _158_1369))
in (FStar_SMTEncoding_Term.mkApp _158_1370))
in (
# 1092 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1093 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _158_1377 = (let _158_1376 = (let _158_1375 = (let _158_1374 = (let _158_1373 = (let _158_1372 = (let _158_1371 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_158_1371, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1372))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1373))
in (FStar_SMTEncoding_Term.mkForall _158_1374))
in (_158_1375, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1376))
in (_158_1377)::[])))))))))
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun disj _76_1808 -> (
# 1096 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1097 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1098 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1099 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1100 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1384 = (let _158_1383 = (let _158_1382 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_158_1382)::[])
in ("Valid", _158_1383))
in (FStar_SMTEncoding_Term.mkApp _158_1384))
in (
# 1101 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1102 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _158_1391 = (let _158_1390 = (let _158_1389 = (let _158_1388 = (let _158_1387 = (let _158_1386 = (let _158_1385 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_158_1385, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1386))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1387))
in (FStar_SMTEncoding_Term.mkForall _158_1388))
in (_158_1389, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1390))
in (_158_1391)::[])))))))))
in (
# 1104 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun eq2 tt -> (
# 1105 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1106 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1107 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1109 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1110 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1112 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1113 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1398 = (let _158_1397 = (let _158_1396 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_158_1396)::[])
in ("Valid", _158_1397))
in (FStar_SMTEncoding_Term.mkApp _158_1398))
in (let _158_1405 = (let _158_1404 = (let _158_1403 = (let _158_1402 = (let _158_1401 = (let _158_1400 = (let _158_1399 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_158_1399, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1400))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _158_1401))
in (FStar_SMTEncoding_Term.mkForall _158_1402))
in (_158_1403, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1404))
in (_158_1405)::[])))))))))))
in (
# 1115 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun imp tt -> (
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
let valid = (let _158_1412 = (let _158_1411 = (let _158_1410 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_158_1410)::[])
in ("Valid", _158_1411))
in (FStar_SMTEncoding_Term.mkApp _158_1412))
in (
# 1121 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1122 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _158_1419 = (let _158_1418 = (let _158_1417 = (let _158_1416 = (let _158_1415 = (let _158_1414 = (let _158_1413 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_158_1413, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1414))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1415))
in (FStar_SMTEncoding_Term.mkForall _158_1416))
in (_158_1417, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1418))
in (_158_1419)::[])))))))))
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun iff tt -> (
# 1125 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1128 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1129 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1426 = (let _158_1425 = (let _158_1424 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_158_1424)::[])
in ("Valid", _158_1425))
in (FStar_SMTEncoding_Term.mkApp _158_1426))
in (
# 1130 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1131 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _158_1433 = (let _158_1432 = (let _158_1431 = (let _158_1430 = (let _158_1429 = (let _158_1428 = (let _158_1427 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_158_1427, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1428))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1429))
in (FStar_SMTEncoding_Term.mkForall _158_1430))
in (_158_1431, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1432))
in (_158_1433)::[])))))))))
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun for_all tt -> (
# 1134 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1135 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1136 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1137 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1138 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1139 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1140 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1440 = (let _158_1439 = (let _158_1438 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_158_1438)::[])
in ("Valid", _158_1439))
in (FStar_SMTEncoding_Term.mkApp _158_1440))
in (
# 1141 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _158_1443 = (let _158_1442 = (let _158_1441 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_158_1441)::[])
in ("Valid", _158_1442))
in (FStar_SMTEncoding_Term.mkApp _158_1443))
in (let _158_1457 = (let _158_1456 = (let _158_1455 = (let _158_1454 = (let _158_1453 = (let _158_1452 = (let _158_1451 = (let _158_1450 = (let _158_1449 = (let _158_1445 = (let _158_1444 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_158_1444)::[])
in (_158_1445)::[])
in (let _158_1448 = (let _158_1447 = (let _158_1446 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_158_1446, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _158_1447))
in (_158_1449, (xx)::[], _158_1448)))
in (FStar_SMTEncoding_Term.mkForall _158_1450))
in (_158_1451, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1452))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1453))
in (FStar_SMTEncoding_Term.mkForall _158_1454))
in (_158_1455, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1456))
in (_158_1457)::[]))))))))))
in (
# 1143 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun for_all tt -> (
# 1144 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1145 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1148 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1149 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1150 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1464 = (let _158_1463 = (let _158_1462 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_158_1462)::[])
in ("Valid", _158_1463))
in (FStar_SMTEncoding_Term.mkApp _158_1464))
in (
# 1151 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _158_1467 = (let _158_1466 = (let _158_1465 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_158_1465)::[])
in ("Valid", _158_1466))
in (FStar_SMTEncoding_Term.mkApp _158_1467))
in (let _158_1481 = (let _158_1480 = (let _158_1479 = (let _158_1478 = (let _158_1477 = (let _158_1476 = (let _158_1475 = (let _158_1474 = (let _158_1473 = (let _158_1469 = (let _158_1468 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_158_1468)::[])
in (_158_1469)::[])
in (let _158_1472 = (let _158_1471 = (let _158_1470 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_158_1470, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _158_1471))
in (_158_1473, (xx)::[], _158_1472)))
in (FStar_SMTEncoding_Term.mkExists _158_1474))
in (_158_1475, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1476))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1477))
in (FStar_SMTEncoding_Term.mkForall _158_1478))
in (_158_1479, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1480))
in (_158_1481)::[]))))))))))
in (
# 1154 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _76_1879 -> (match (_76_1879) with
| (l, _76_1878) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_76_1882, f) -> begin
(f s tt)
end)))))))))))))))))))))

# 1175 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1176 "FStar.SMTEncoding.Encode.fst"
let _76_1888 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _158_1624 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _158_1624))
end else begin
()
end
in (
# 1179 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1182 "FStar.SMTEncoding.Encode.fst"
let _76_1896 = (encode_sigelt' env se)
in (match (_76_1896) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _158_1627 = (let _158_1626 = (let _158_1625 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_158_1625))
in (_158_1626)::[])
in (_158_1627, e))
end
| _76_1899 -> begin
(let _158_1634 = (let _158_1633 = (let _158_1629 = (let _158_1628 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_158_1628))
in (_158_1629)::g)
in (let _158_1632 = (let _158_1631 = (let _158_1630 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_158_1630))
in (_158_1631)::[])
in (FStar_List.append _158_1633 _158_1632)))
in (_158_1634, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1188 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1194 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1195 "FStar.SMTEncoding.Encode.fst"
let tt = (whnf env t)
in (
# 1200 "FStar.SMTEncoding.Encode.fst"
let _76_1912 = (encode_free_var env lid t tt quals)
in (match (_76_1912) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _158_1648 = (let _158_1647 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _158_1647))
in (_158_1648, env))
end else begin
(decls, env)
end
end))))
in (
# 1206 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _76_1919 lb -> (match (_76_1919) with
| (decls, env) -> begin
(
# 1208 "FStar.SMTEncoding.Encode.fst"
let _76_1923 = (let _158_1657 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _158_1657 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_76_1923) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _76_1941, _76_1943, _76_1945, _76_1947) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1220 "FStar.SMTEncoding.Encode.fst"
let _76_1953 = (new_term_constant_and_tok_from_lid env lid)
in (match (_76_1953) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _76_1956, t, quals, _76_1960) -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_12 -> (match (_76_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _76_1972 -> begin
false
end)))) || env.tcenv.FStar_TypeChecker_Env.is_iface) then begin
(
# 1225 "FStar.SMTEncoding.Encode.fst"
let _76_1975 = (encode_top_level_val env lid t quals)
in (match (_76_1975) with
| (decls, env) -> begin
(
# 1226 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1227 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _158_1660 = (let _158_1659 = (primitive_type_axioms lid tname tsym)
in (FStar_List.append decls _158_1659))
in (_158_1660, env))))
end))
end else begin
([], env)
end
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _76_1981, _76_1983) -> begin
(
# 1234 "FStar.SMTEncoding.Encode.fst"
let _76_1988 = (encode_formula f env)
in (match (_76_1988) with
| (f, decls) -> begin
(
# 1235 "FStar.SMTEncoding.Encode.fst"
let g = (let _158_1665 = (let _158_1664 = (let _158_1663 = (let _158_1662 = (let _158_1661 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _158_1661))
in Some (_158_1662))
in (f, _158_1663))
in FStar_SMTEncoding_Term.Assume (_158_1664))
in (_158_1665)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _76_1993, _76_1995) when (FStar_All.pipe_right (Prims.snd lbs) (FStar_Util.for_some (fun lb -> (let _158_1667 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (should_skip _158_1667))))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_76_2000, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _76_2008; FStar_Syntax_Syntax.lbtyp = _76_2006; FStar_Syntax_Syntax.lbeff = _76_2004; FStar_Syntax_Syntax.lbdef = _76_2002}::[]), _76_2015, _76_2017, _76_2019) when (FStar_Ident.lid_equals b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1242 "FStar.SMTEncoding.Encode.fst"
let _76_2025 = (new_term_constant_and_tok_from_lid env b2t)
in (match (_76_2025) with
| (tname, ttok, env) -> begin
(
# 1243 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1244 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1245 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _158_1670 = (let _158_1669 = (let _158_1668 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_158_1668)::[])
in ("Valid", _158_1669))
in (FStar_SMTEncoding_Term.mkApp _158_1670))
in (
# 1246 "FStar.SMTEncoding.Encode.fst"
let decls = (let _158_1678 = (let _158_1677 = (let _158_1676 = (let _158_1675 = (let _158_1674 = (let _158_1673 = (let _158_1672 = (let _158_1671 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _158_1671))
in (FStar_SMTEncoding_Term.mkEq _158_1672))
in (((valid_b2t_x)::[])::[], (xx)::[], _158_1673))
in (FStar_SMTEncoding_Term.mkForall _158_1674))
in (_158_1675, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_158_1676))
in (_158_1677)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_158_1678)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_76_2031, _76_2033, _76_2035, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_13 -> (match (_76_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _76_2045 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _76_2051, _76_2053, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_14 -> (match (_76_14) with
| FStar_Syntax_Syntax.Projector (_76_2059) -> begin
true
end
| _76_2062 -> begin
false
end)))) -> begin
(
# 1260 "FStar.SMTEncoding.Encode.fst"
let l = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (match ((try_lookup_free_var env l)) with
| Some (_76_2065) -> begin
([], env)
end
| None -> begin
(
# 1265 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _76_2073, _76_2075, quals) -> begin
(
# 1271 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1272 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1273 "FStar.SMTEncoding.Encode.fst"
let _76_2087 = (FStar_Util.first_N nbinders formals)
in (match (_76_2087) with
| (formals, extra_formals) -> begin
(
# 1274 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _76_2091 _76_2095 -> (match ((_76_2091, _76_2095)) with
| ((formal, _76_2090), (binder, _76_2094)) -> begin
(let _158_1692 = (let _158_1691 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _158_1691))
in FStar_Syntax_Syntax.NT (_158_1692))
end)) formals binders)
in (
# 1275 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _158_1696 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _76_2099 -> (match (_76_2099) with
| (x, i) -> begin
(let _158_1695 = (
# 1275 "FStar.SMTEncoding.Encode.fst"
let _76_2100 = x
in (let _158_1694 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _76_2100.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _76_2100.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _158_1694}))
in (_158_1695, i))
end))))
in (FStar_All.pipe_right _158_1696 FStar_Syntax_Util.name_binders))
in (
# 1276 "FStar.SMTEncoding.Encode.fst"
let body = (let _158_1703 = (FStar_Syntax_Subst.compress body)
in (let _158_1702 = (let _158_1697 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _158_1697))
in (let _158_1701 = (let _158_1700 = (let _158_1699 = (FStar_Syntax_Subst.subst subst t)
in _158_1699.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _158_1698 -> Some (_158_1698)) _158_1700))
in (FStar_Syntax_Syntax.extend_app_n _158_1703 _158_1702 _158_1701 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1279 "FStar.SMTEncoding.Encode.fst"
let rec destruct_bound_function = (fun flid t_norm e -> (match ((let _158_1710 = (FStar_Syntax_Util.unascribe e)
in _158_1710.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1282 "FStar.SMTEncoding.Encode.fst"
let _76_2116 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_76_2116) with
| (binders, body, opening) -> begin
(match ((let _158_1711 = (FStar_Syntax_Subst.compress t_norm)
in _158_1711.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1285 "FStar.SMTEncoding.Encode.fst"
let _76_2123 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_76_2123) with
| (formals, c) -> begin
(
# 1286 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1287 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1288 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1290 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1291 "FStar.SMTEncoding.Encode.fst"
let _76_2130 = (FStar_Util.first_N nformals binders)
in (match (_76_2130) with
| (bs0, rest) -> begin
(
# 1292 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1293 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _76_2134 _76_2138 -> (match ((_76_2134, _76_2138)) with
| ((b, _76_2133), (x, _76_2137)) -> begin
(let _158_1715 = (let _158_1714 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _158_1714))
in FStar_Syntax_Syntax.NT (_158_1715))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1295 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1298 "FStar.SMTEncoding.Encode.fst"
let _76_2144 = (eta_expand binders formals body tres)
in (match (_76_2144) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| _76_2146 -> begin
(let _158_1718 = (let _158_1717 = (FStar_Syntax_Print.term_to_string e)
in (let _158_1716 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _158_1717 _158_1716)))
in (FStar_All.failwith _158_1718))
end)
end))
end
| _76_2148 -> begin
(match ((let _158_1719 = (FStar_Syntax_Subst.compress t_norm)
in _158_1719.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1308 "FStar.SMTEncoding.Encode.fst"
let _76_2155 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_76_2155) with
| (formals, c) -> begin
(
# 1309 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1310 "FStar.SMTEncoding.Encode.fst"
let _76_2159 = (eta_expand [] formals e tres)
in (match (_76_2159) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _76_2161 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _76_2163 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1318 "FStar.SMTEncoding.Encode.fst"
let _76_2189 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _76_2176 lb -> (match (_76_2176) with
| (toks, typs, decls, env) -> begin
(
# 1320 "FStar.SMTEncoding.Encode.fst"
let _76_2178 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1321 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1322 "FStar.SMTEncoding.Encode.fst"
let _76_2184 = (let _158_1724 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _158_1724 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_76_2184) with
| (tok, decl, env) -> begin
(let _158_1727 = (let _158_1726 = (let _158_1725 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_158_1725, tok))
in (_158_1726)::toks)
in (_158_1727, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_76_2189) with
| (toks, typs, decls, env) -> begin
(
# 1324 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1325 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1326 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_15 -> (match (_76_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _76_2196 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _158_1730 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _158_1730)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _76_2206; FStar_Syntax_Syntax.lbunivs = _76_2204; FStar_Syntax_Syntax.lbtyp = _76_2202; FStar_Syntax_Syntax.lbeff = _76_2200; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(
# 1333 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1334 "FStar.SMTEncoding.Encode.fst"
let _76_2225 = (destruct_bound_function flid t_norm e)
in (match (_76_2225) with
| (binders, body, _76_2222, _76_2224) -> begin
(
# 1335 "FStar.SMTEncoding.Encode.fst"
let _76_2232 = (encode_binders None binders env)
in (match (_76_2232) with
| (vars, guards, env', binder_decls, _76_2231) -> begin
(
# 1336 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _76_2235 -> begin
(let _158_1732 = (let _158_1731 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _158_1731))
in (FStar_SMTEncoding_Term.mkApp _158_1732))
end)
in (
# 1337 "FStar.SMTEncoding.Encode.fst"
let _76_2241 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _158_1734 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _158_1733 = (encode_formula body env')
in (_158_1734, _158_1733)))
end else begin
(let _158_1735 = (encode_term body env')
in (app, _158_1735))
end
in (match (_76_2241) with
| (app, (body, decls2)) -> begin
(
# 1341 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _158_1744 = (let _158_1743 = (let _158_1740 = (let _158_1739 = (let _158_1738 = (let _158_1737 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _158_1736 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_158_1737, _158_1736)))
in (FStar_SMTEncoding_Term.mkImp _158_1738))
in (((app)::[])::[], vars, _158_1739))
in (FStar_SMTEncoding_Term.mkForall _158_1740))
in (let _158_1742 = (let _158_1741 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_158_1741))
in (_158_1743, _158_1742)))
in FStar_SMTEncoding_Term.Assume (_158_1744))
in (let _158_1746 = (let _158_1745 = (primitive_type_axioms flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _158_1745))
in (_158_1746, env)))
end)))
end))
end)))
end
| _76_2244 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1347 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _158_1747 = (varops.fresh "fuel")
in (_158_1747, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1348 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1349 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1350 "FStar.SMTEncoding.Encode.fst"
let _76_2261 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _76_2250 _76_2255 -> (match ((_76_2250, _76_2255)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(
# 1351 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1352 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1353 "FStar.SMTEncoding.Encode.fst"
let env = (let _158_1752 = (let _158_1751 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _158_1750 -> Some (_158_1750)) _158_1751))
in (push_free_var env flid gtok _158_1752))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_76_2261) with
| (gtoks, env) -> begin
(
# 1355 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1356 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _76_2270 t_norm _76_2281 -> (match ((_76_2270, _76_2281)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _76_2280; FStar_Syntax_Syntax.lbunivs = _76_2278; FStar_Syntax_Syntax.lbtyp = _76_2276; FStar_Syntax_Syntax.lbeff = _76_2274; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1357 "FStar.SMTEncoding.Encode.fst"
let _76_2286 = (destruct_bound_function flid t_norm e)
in (match (_76_2286) with
| (binders, body, formals, tres) -> begin
(
# 1358 "FStar.SMTEncoding.Encode.fst"
let _76_2293 = (encode_binders None binders env)
in (match (_76_2293) with
| (vars, guards, env', binder_decls, _76_2292) -> begin
(
# 1359 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _158_1763 = (let _158_1762 = (let _158_1761 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_158_1761)
in (g, _158_1762, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_158_1763))
in (
# 1360 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1361 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1362 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1363 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1364 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _158_1766 = (let _158_1765 = (let _158_1764 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_158_1764)::vars_tm)
in (g, _158_1765))
in (FStar_SMTEncoding_Term.mkApp _158_1766))
in (
# 1365 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _158_1769 = (let _158_1768 = (let _158_1767 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_158_1767)::vars_tm)
in (g, _158_1768))
in (FStar_SMTEncoding_Term.mkApp _158_1769))
in (
# 1366 "FStar.SMTEncoding.Encode.fst"
let _76_2303 = (encode_term body env')
in (match (_76_2303) with
| (body_tm, decls2) -> begin
(
# 1367 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _158_1778 = (let _158_1777 = (let _158_1774 = (let _158_1773 = (let _158_1772 = (let _158_1771 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _158_1770 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_158_1771, _158_1770)))
in (FStar_SMTEncoding_Term.mkImp _158_1772))
in (((gsapp)::[])::[], (fuel)::vars, _158_1773))
in (FStar_SMTEncoding_Term.mkForall _158_1774))
in (let _158_1776 = (let _158_1775 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_158_1775))
in (_158_1777, _158_1776)))
in FStar_SMTEncoding_Term.Assume (_158_1778))
in (
# 1369 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _158_1782 = (let _158_1781 = (let _158_1780 = (let _158_1779 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _158_1779))
in (FStar_SMTEncoding_Term.mkForall _158_1780))
in (_158_1781, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_158_1782))
in (
# 1371 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _158_1791 = (let _158_1790 = (let _158_1789 = (let _158_1788 = (let _158_1787 = (let _158_1786 = (let _158_1785 = (let _158_1784 = (let _158_1783 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_158_1783)::vars_tm)
in (g, _158_1784))
in (FStar_SMTEncoding_Term.mkApp _158_1785))
in (gsapp, _158_1786))
in (FStar_SMTEncoding_Term.mkEq _158_1787))
in (((gsapp)::[])::[], (fuel)::vars, _158_1788))
in (FStar_SMTEncoding_Term.mkForall _158_1789))
in (_158_1790, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_158_1791))
in (
# 1373 "FStar.SMTEncoding.Encode.fst"
let _76_2326 = (
# 1374 "FStar.SMTEncoding.Encode.fst"
let _76_2313 = (encode_binders None formals env0)
in (match (_76_2313) with
| (vars, v_guards, env, binder_decls, _76_2312) -> begin
(
# 1375 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1376 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1377 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1378 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _158_1792 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _158_1792 ((fuel)::vars)))
in (let _158_1796 = (let _158_1795 = (let _158_1794 = (let _158_1793 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _158_1793))
in (FStar_SMTEncoding_Term.mkForall _158_1794))
in (_158_1795, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_158_1796)))
in (
# 1381 "FStar.SMTEncoding.Encode.fst"
let _76_2323 = (
# 1382 "FStar.SMTEncoding.Encode.fst"
let _76_2320 = (encode_term_pred None tres env gapp)
in (match (_76_2320) with
| (g_typing, d3) -> begin
(let _158_1804 = (let _158_1803 = (let _158_1802 = (let _158_1801 = (let _158_1800 = (let _158_1799 = (let _158_1798 = (let _158_1797 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_158_1797, g_typing))
in (FStar_SMTEncoding_Term.mkImp _158_1798))
in (((gapp)::[])::[], (fuel)::vars, _158_1799))
in (FStar_SMTEncoding_Term.mkForall _158_1800))
in (_158_1801, None))
in FStar_SMTEncoding_Term.Assume (_158_1802))
in (_158_1803)::[])
in (d3, _158_1804))
end))
in (match (_76_2323) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_76_2326) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1386 "FStar.SMTEncoding.Encode.fst"
let _76_2342 = (let _158_1807 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _76_2330 _76_2334 -> (match ((_76_2330, _76_2334)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1387 "FStar.SMTEncoding.Encode.fst"
let _76_2338 = (encode_one_binding env0 gtok ty bs)
in (match (_76_2338) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _158_1807))
in (match (_76_2342) with
| (decls, eqns, env0) -> begin
(
# 1389 "FStar.SMTEncoding.Encode.fst"
let _76_2351 = (let _158_1809 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _158_1809 (FStar_List.partition (fun _76_16 -> (match (_76_16) with
| FStar_SMTEncoding_Term.DeclFun (_76_2345) -> begin
true
end
| _76_2348 -> begin
false
end)))))
in (match (_76_2351) with
| (prefix_decls, rest) -> begin
(
# 1392 "FStar.SMTEncoding.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _76_2162 -> (match (_76_2162) with
| Let_rec_unencodeable -> begin
(
# 1395 "FStar.SMTEncoding.Encode.fst"
let msg = (let _158_1812 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _158_1812 (FStar_String.concat " and ")))
in (
# 1396 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _76_2355, _76_2357, _76_2359) -> begin
(
# 1401 "FStar.SMTEncoding.Encode.fst"
let _76_2364 = (encode_signature env ses)
in (match (_76_2364) with
| (g, env) -> begin
(
# 1402 "FStar.SMTEncoding.Encode.fst"
let _76_2376 = (FStar_All.pipe_right g (FStar_List.partition (fun _76_17 -> (match (_76_17) with
| FStar_SMTEncoding_Term.Assume (_76_2367, Some ("inversion axiom")) -> begin
false
end
| _76_2373 -> begin
true
end))))
in (match (_76_2376) with
| (g', inversions) -> begin
(
# 1405 "FStar.SMTEncoding.Encode.fst"
let _76_2385 = (FStar_All.pipe_right g' (FStar_List.partition (fun _76_18 -> (match (_76_18) with
| FStar_SMTEncoding_Term.DeclFun (_76_2379) -> begin
true
end
| _76_2382 -> begin
false
end))))
in (match (_76_2385) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _76_2388, tps, k, _76_2392, datas, quals, _76_2396) -> begin
(
# 1411 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_19 -> (match (_76_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _76_2403 -> begin
false
end))))
in (
# 1412 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1414 "FStar.SMTEncoding.Encode.fst"
let _76_2413 = c
in (match (_76_2413) with
| (name, args, _76_2410, _76_2412) -> begin
(let _158_1820 = (let _158_1819 = (let _158_1818 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _158_1818, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_158_1819))
in (_158_1820)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1418 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _158_1826 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _158_1826 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1422 "FStar.SMTEncoding.Encode.fst"
let _76_2420 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_2420) with
| (xxsym, xx) -> begin
(
# 1423 "FStar.SMTEncoding.Encode.fst"
let _76_2456 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _76_2423 l -> (match (_76_2423) with
| (out, decls) -> begin
(
# 1424 "FStar.SMTEncoding.Encode.fst"
let _76_2428 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_76_2428) with
| (_76_2426, data_t) -> begin
(
# 1425 "FStar.SMTEncoding.Encode.fst"
let _76_2431 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_76_2431) with
| (args, res) -> begin
(
# 1426 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _158_1829 = (FStar_Syntax_Subst.compress res)
in _158_1829.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_76_2433, indices) -> begin
indices
end
| _76_2438 -> begin
[]
end)
in (
# 1429 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _76_2444 -> (match (_76_2444) with
| (x, _76_2443) -> begin
(let _158_1834 = (let _158_1833 = (let _158_1832 = (mk_term_projector_name l x)
in (_158_1832, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _158_1833))
in (push_term_var env x _158_1834))
end)) env))
in (
# 1432 "FStar.SMTEncoding.Encode.fst"
let _76_2448 = (encode_args indices env)
in (match (_76_2448) with
| (indices, decls') -> begin
(
# 1433 "FStar.SMTEncoding.Encode.fst"
let _76_2449 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1435 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _158_1839 = (FStar_List.map2 (fun v a -> (let _158_1838 = (let _158_1837 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_158_1837, a))
in (FStar_SMTEncoding_Term.mkEq _158_1838))) vars indices)
in (FStar_All.pipe_right _158_1839 FStar_SMTEncoding_Term.mk_and_l))
in (let _158_1844 = (let _158_1843 = (let _158_1842 = (let _158_1841 = (let _158_1840 = (mk_data_tester env l xx)
in (_158_1840, eqs))
in (FStar_SMTEncoding_Term.mkAnd _158_1841))
in (out, _158_1842))
in (FStar_SMTEncoding_Term.mkOr _158_1843))
in (_158_1844, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_76_2456) with
| (data_ax, decls) -> begin
(
# 1437 "FStar.SMTEncoding.Encode.fst"
let _76_2459 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_2459) with
| (ffsym, ff) -> begin
(
# 1438 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _158_1845 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _158_1845 xx tapp))
in (let _158_1852 = (let _158_1851 = (let _158_1850 = (let _158_1849 = (let _158_1848 = (let _158_1847 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _158_1846 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _158_1847, _158_1846)))
in (FStar_SMTEncoding_Term.mkForall _158_1848))
in (_158_1849, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_158_1850))
in (_158_1851)::[])
in (FStar_List.append decls _158_1852)))
end))
end))
end))
end)
in (
# 1442 "FStar.SMTEncoding.Encode.fst"
let _76_2469 = (match ((let _158_1853 = (FStar_Syntax_Subst.compress k)
in _158_1853.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _76_2466 -> begin
(tps, k)
end)
in (match (_76_2469) with
| (formals, res) -> begin
(
# 1448 "FStar.SMTEncoding.Encode.fst"
let _76_2472 = (FStar_Syntax_Subst.open_term formals res)
in (match (_76_2472) with
| (formals, res) -> begin
(
# 1449 "FStar.SMTEncoding.Encode.fst"
let _76_2479 = (encode_binders None formals env)
in (match (_76_2479) with
| (vars, guards, env', binder_decls, _76_2478) -> begin
(
# 1451 "FStar.SMTEncoding.Encode.fst"
let pretype_axioms = (fun tapp vars -> (
# 1452 "FStar.SMTEncoding.Encode.fst"
let _76_2485 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_2485) with
| (xxsym, xx) -> begin
(
# 1453 "FStar.SMTEncoding.Encode.fst"
let _76_2488 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_2488) with
| (ffsym, ff) -> begin
(
# 1454 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _158_1866 = (let _158_1865 = (let _158_1864 = (let _158_1863 = (let _158_1862 = (let _158_1861 = (let _158_1860 = (let _158_1859 = (let _158_1858 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _158_1858))
in (FStar_SMTEncoding_Term.mkEq _158_1859))
in (xx_has_type, _158_1860))
in (FStar_SMTEncoding_Term.mkImp _158_1861))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _158_1862))
in (FStar_SMTEncoding_Term.mkForall _158_1863))
in (_158_1864, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_158_1865))
in (_158_1866)::[]))
end))
end)))
in (
# 1458 "FStar.SMTEncoding.Encode.fst"
let _76_2493 = (new_term_constant_and_tok_from_lid env t)
in (match (_76_2493) with
| (tname, ttok, env) -> begin
(
# 1459 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1460 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1461 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _158_1868 = (let _158_1867 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _158_1867))
in (FStar_SMTEncoding_Term.mkApp _158_1868))
in (
# 1462 "FStar.SMTEncoding.Encode.fst"
let _76_2514 = (
# 1463 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _158_1872 = (let _158_1871 = (FStar_All.pipe_right vars (FStar_List.map (fun _76_2499 -> (match (_76_2499) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _158_1870 = (varops.next_id ())
in (tname, _158_1871, FStar_SMTEncoding_Term.Term_sort, _158_1870)))
in (constructor_or_logic_type_decl _158_1872))
in (
# 1464 "FStar.SMTEncoding.Encode.fst"
let _76_2511 = (match (vars) with
| [] -> begin
(let _158_1876 = (let _158_1875 = (let _158_1874 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _158_1873 -> Some (_158_1873)) _158_1874))
in (push_free_var env t tname _158_1875))
in ([], _158_1876))
end
| _76_2503 -> begin
(
# 1467 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1468 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _158_1877 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _158_1877))
in (
# 1469 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1470 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1473 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _158_1881 = (let _158_1880 = (let _158_1879 = (let _158_1878 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _158_1878))
in (FStar_SMTEncoding_Term.mkForall' _158_1879))
in (_158_1880, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_158_1881))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_76_2511) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_76_2514) with
| (decls, env) -> begin
(
# 1476 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1477 "FStar.SMTEncoding.Encode.fst"
let _76_2517 = (encode_term_pred None res env' tapp)
in (match (_76_2517) with
| (k, decls) -> begin
(
# 1478 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _158_1885 = (let _158_1884 = (let _158_1883 = (let _158_1882 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _158_1882))
in (_158_1883, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_158_1884))
in (_158_1885)::[])
end else begin
[]
end
in (let _158_1891 = (let _158_1890 = (let _158_1889 = (let _158_1888 = (let _158_1887 = (let _158_1886 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _158_1886))
in (FStar_SMTEncoding_Term.mkForall _158_1887))
in (_158_1888, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_158_1889))
in (_158_1890)::[])
in (FStar_List.append (FStar_List.append decls karr) _158_1891)))
end))
in (
# 1483 "FStar.SMTEncoding.Encode.fst"
let aux = (let _158_1894 = (let _158_1892 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _158_1892))
in (let _158_1893 = (pretype_axioms tapp vars)
in (FStar_List.append _158_1894 _158_1893)))
in (
# 1488 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _76_2524, _76_2526, _76_2528, _76_2530, _76_2532, _76_2534, _76_2536) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _76_2541, t, _76_2544, n_tps, quals, _76_2548, drange) -> begin
(
# 1496 "FStar.SMTEncoding.Encode.fst"
let _76_2555 = (new_term_constant_and_tok_from_lid env d)
in (match (_76_2555) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1497 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1498 "FStar.SMTEncoding.Encode.fst"
let _76_2559 = (FStar_Syntax_Util.arrow_formals t)
in (match (_76_2559) with
| (formals, t_res) -> begin
(
# 1499 "FStar.SMTEncoding.Encode.fst"
let _76_2562 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_2562) with
| (fuel_var, fuel_tm) -> begin
(
# 1500 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1501 "FStar.SMTEncoding.Encode.fst"
let _76_2569 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_76_2569) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1502 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _158_1896 = (mk_term_projector_name d x)
in (_158_1896, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1503 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _158_1898 = (let _158_1897 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _158_1897))
in (FStar_All.pipe_right _158_1898 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1504 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1505 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1506 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1507 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1509 "FStar.SMTEncoding.Encode.fst"
let _76_2579 = (encode_term_pred None t env ddtok_tm)
in (match (_76_2579) with
| (tok_typing, decls3) -> begin
(
# 1511 "FStar.SMTEncoding.Encode.fst"
let _76_2586 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_76_2586) with
| (vars', guards', env'', decls_formals, _76_2585) -> begin
(
# 1512 "FStar.SMTEncoding.Encode.fst"
let _76_2591 = (
# 1513 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1514 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_76_2591) with
| (ty_pred', decls_pred) -> begin
(
# 1516 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1517 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _76_2595 -> begin
(let _158_1900 = (let _158_1899 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _158_1899))
in (_158_1900)::[])
end)
in (
# 1521 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _76_2598 -> (match (()) with
| () -> begin
(
# 1522 "FStar.SMTEncoding.Encode.fst"
let _76_2601 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_76_2601) with
| (head, args) -> begin
(match ((let _158_1903 = (FStar_Syntax_Subst.compress head)
in _158_1903.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(
# 1526 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv)
in (
# 1527 "FStar.SMTEncoding.Encode.fst"
let _76_2625 = (encode_args args env')
in (match (_76_2625) with
| (encoded_args, arg_decls) -> begin
(
# 1528 "FStar.SMTEncoding.Encode.fst"
let _76_2640 = (FStar_List.fold_left (fun _76_2629 arg -> (match (_76_2629) with
| (env, arg_vars, eqns) -> begin
(
# 1529 "FStar.SMTEncoding.Encode.fst"
let _76_2635 = (let _158_1906 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _158_1906))
in (match (_76_2635) with
| (_76_2632, xv, env) -> begin
(let _158_1908 = (let _158_1907 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_158_1907)::eqns)
in (env, (xv)::arg_vars, _158_1908))
end))
end)) (env', [], []) encoded_args)
in (match (_76_2640) with
| (_76_2637, arg_vars, eqns) -> begin
(
# 1531 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1532 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1533 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1534 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1535 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1536 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1537 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _158_1915 = (let _158_1914 = (let _158_1913 = (let _158_1912 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _158_1911 = (let _158_1910 = (let _158_1909 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _158_1909))
in (FStar_SMTEncoding_Term.mkImp _158_1910))
in (((ty_pred)::[])::[], _158_1912, _158_1911)))
in (FStar_SMTEncoding_Term.mkForall _158_1913))
in (_158_1914, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_158_1915))
in (
# 1542 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1544 "FStar.SMTEncoding.Encode.fst"
let x = (let _158_1916 = (varops.fresh "x")
in (_158_1916, FStar_SMTEncoding_Term.Term_sort))
in (
# 1545 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _158_1926 = (let _158_1925 = (let _158_1924 = (let _158_1923 = (let _158_1918 = (let _158_1917 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_158_1917)::[])
in (_158_1918)::[])
in (let _158_1922 = (let _158_1921 = (let _158_1920 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _158_1919 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_158_1920, _158_1919)))
in (FStar_SMTEncoding_Term.mkImp _158_1921))
in (_158_1923, (x)::[], _158_1922)))
in (FStar_SMTEncoding_Term.mkForall _158_1924))
in (_158_1925, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_158_1926))))
end else begin
(
# 1548 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _158_1929 = (let _158_1928 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _158_1928 dapp))
in (_158_1929)::[])
end
| _76_2654 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _158_1936 = (let _158_1935 = (let _158_1934 = (let _158_1933 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _158_1932 = (let _158_1931 = (let _158_1930 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _158_1930))
in (FStar_SMTEncoding_Term.mkImp _158_1931))
in (((ty_pred)::[])::[], _158_1933, _158_1932)))
in (FStar_SMTEncoding_Term.mkForall _158_1934))
in (_158_1935, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_158_1936)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _76_2658 -> begin
(
# 1556 "FStar.SMTEncoding.Encode.fst"
let _76_2659 = (let _158_1939 = (let _158_1938 = (FStar_Syntax_Print.lid_to_string d)
in (let _158_1937 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _158_1938 _158_1937)))
in (FStar_TypeChecker_Errors.warn drange _158_1939))
in ([], []))
end)
end))
end))
in (
# 1559 "FStar.SMTEncoding.Encode.fst"
let _76_2663 = (encode_elim ())
in (match (_76_2663) with
| (decls2, elim) -> begin
(
# 1560 "FStar.SMTEncoding.Encode.fst"
let g = (let _158_1964 = (let _158_1963 = (let _158_1948 = (let _158_1947 = (let _158_1946 = (let _158_1945 = (let _158_1944 = (let _158_1943 = (let _158_1942 = (let _158_1941 = (let _158_1940 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _158_1940))
in Some (_158_1941))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _158_1942))
in FStar_SMTEncoding_Term.DeclFun (_158_1943))
in (_158_1944)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _158_1945))
in (FStar_List.append _158_1946 proxy_fresh))
in (FStar_List.append _158_1947 decls_formals))
in (FStar_List.append _158_1948 decls_pred))
in (let _158_1962 = (let _158_1961 = (let _158_1960 = (let _158_1952 = (let _158_1951 = (let _158_1950 = (let _158_1949 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _158_1949))
in (FStar_SMTEncoding_Term.mkForall _158_1950))
in (_158_1951, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_158_1952))
in (let _158_1959 = (let _158_1958 = (let _158_1957 = (let _158_1956 = (let _158_1955 = (let _158_1954 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _158_1953 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _158_1954, _158_1953)))
in (FStar_SMTEncoding_Term.mkForall _158_1955))
in (_158_1956, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_158_1957))
in (_158_1958)::[])
in (_158_1960)::_158_1959))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_158_1961)
in (FStar_List.append _158_1963 _158_1962)))
in (FStar_List.append _158_1964 elim))
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
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(
# 1578 "FStar.SMTEncoding.Encode.fst"
let _76_2672 = (encode_free_var env x t t_norm [])
in (match (_76_2672) with
| (decls, env) -> begin
(
# 1579 "FStar.SMTEncoding.Encode.fst"
let _76_2677 = (lookup_lid env x)
in (match (_76_2677) with
| (n, x', _76_2676) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _76_2681) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env lid t -> (
# 1585 "FStar.SMTEncoding.Encode.fst"
let _76_2689 = (encode_function_type_as_formula None None t env)
in (match (_76_2689) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _158_1977 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _158_1977)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1591 "FStar.SMTEncoding.Encode.fst"
let _76_2698 = (new_term_constant_and_tok_from_lid env lid)
in (match (_76_2698) with
| (vname, vtok, env) -> begin
(
# 1592 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _158_1978 = (FStar_Syntax_Subst.compress t_norm)
in _158_1978.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _76_2701) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _76_2704 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _76_2707 -> begin
[]
end)
in (
# 1595 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1596 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1599 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1600 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1601 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1603 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1604 "FStar.SMTEncoding.Encode.fst"
let _76_2722 = (
# 1605 "FStar.SMTEncoding.Encode.fst"
let _76_2717 = (curried_arrow_formals_comp t_norm)
in (match (_76_2717) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _158_1980 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _158_1980))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_76_2722) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1609 "FStar.SMTEncoding.Encode.fst"
let _76_2726 = (new_term_constant_and_tok_from_lid env lid)
in (match (_76_2726) with
| (vname, vtok, env) -> begin
(
# 1610 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _76_2729 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1613 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _76_20 -> (match (_76_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1615 "FStar.SMTEncoding.Encode.fst"
let _76_2745 = (FStar_Util.prefix vars)
in (match (_76_2745) with
| (_76_2740, (xxsym, _76_2743)) -> begin
(
# 1616 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _158_1997 = (let _158_1996 = (let _158_1995 = (let _158_1994 = (let _158_1993 = (let _158_1992 = (let _158_1991 = (let _158_1990 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1990))
in (vapp, _158_1991))
in (FStar_SMTEncoding_Term.mkEq _158_1992))
in (((vapp)::[])::[], vars, _158_1993))
in (FStar_SMTEncoding_Term.mkForall _158_1994))
in (_158_1995, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_158_1996))
in (_158_1997)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1621 "FStar.SMTEncoding.Encode.fst"
let _76_2757 = (FStar_Util.prefix vars)
in (match (_76_2757) with
| (_76_2752, (xxsym, _76_2755)) -> begin
(
# 1622 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1623 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1624 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _158_1999 = (let _158_1998 = (mk_term_projector_name d f)
in (_158_1998, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _158_1999))
in (let _158_2004 = (let _158_2003 = (let _158_2002 = (let _158_2001 = (let _158_2000 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _158_2000))
in (FStar_SMTEncoding_Term.mkForall _158_2001))
in (_158_2002, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_158_2003))
in (_158_2004)::[]))))
end))
end
| _76_2762 -> begin
[]
end)))))
in (
# 1628 "FStar.SMTEncoding.Encode.fst"
let _76_2769 = (encode_binders None formals env)
in (match (_76_2769) with
| (vars, guards, env', decls1, _76_2768) -> begin
(
# 1629 "FStar.SMTEncoding.Encode.fst"
let _76_2778 = (match (pre_opt) with
| None -> begin
(let _158_2005 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_158_2005, decls1))
end
| Some (p) -> begin
(
# 1631 "FStar.SMTEncoding.Encode.fst"
let _76_2775 = (encode_formula p env')
in (match (_76_2775) with
| (g, ds) -> begin
(let _158_2006 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_158_2006, (FStar_List.append decls1 ds)))
end))
end)
in (match (_76_2778) with
| (guard, decls1) -> begin
(
# 1632 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1634 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _158_2008 = (let _158_2007 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _158_2007))
in (FStar_SMTEncoding_Term.mkApp _158_2008))
in (
# 1635 "FStar.SMTEncoding.Encode.fst"
let _76_2802 = (
# 1636 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _158_2011 = (let _158_2010 = (FStar_All.pipe_right formals (FStar_List.map (fun _76_2781 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _158_2010, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_158_2011))
in (
# 1637 "FStar.SMTEncoding.Encode.fst"
let _76_2789 = (
# 1638 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1638 "FStar.SMTEncoding.Encode.fst"
let _76_2784 = env
in {bindings = _76_2784.bindings; depth = _76_2784.depth; tcenv = _76_2784.tcenv; warn = _76_2784.warn; cache = _76_2784.cache; nolabels = _76_2784.nolabels; use_zfuel_name = _76_2784.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_76_2789) with
| (tok_typing, decls2) -> begin
(
# 1642 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1643 "FStar.SMTEncoding.Encode.fst"
let _76_2799 = (match (formals) with
| [] -> begin
(let _158_2015 = (let _158_2014 = (let _158_2013 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _158_2012 -> Some (_158_2012)) _158_2013))
in (push_free_var env lid vname _158_2014))
in ((FStar_List.append decls2 ((tok_typing)::[])), _158_2015))
end
| _76_2793 -> begin
(
# 1646 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1647 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _158_2016 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _158_2016))
in (
# 1648 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _158_2020 = (let _158_2019 = (let _158_2018 = (let _158_2017 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _158_2017))
in (FStar_SMTEncoding_Term.mkForall _158_2018))
in (_158_2019, None))
in FStar_SMTEncoding_Term.Assume (_158_2020))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_76_2799) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_76_2802) with
| (decls2, env) -> begin
(
# 1651 "FStar.SMTEncoding.Encode.fst"
let _76_2810 = (
# 1652 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1653 "FStar.SMTEncoding.Encode.fst"
let _76_2806 = (encode_term res_t env')
in (match (_76_2806) with
| (encoded_res_t, decls) -> begin
(let _158_2021 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _158_2021, decls))
end)))
in (match (_76_2810) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1655 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _158_2025 = (let _158_2024 = (let _158_2023 = (let _158_2022 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _158_2022))
in (FStar_SMTEncoding_Term.mkForall _158_2023))
in (_158_2024, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_158_2025))
in (
# 1656 "FStar.SMTEncoding.Encode.fst"
let g = (let _158_2027 = (let _158_2026 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_158_2026)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _158_2027))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _76_2817 se -> (match (_76_2817) with
| (g, env) -> begin
(
# 1662 "FStar.SMTEncoding.Encode.fst"
let _76_2821 = (encode_sigelt env se)
in (match (_76_2821) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1665 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1690 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _76_2828 -> (match (_76_2828) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_76_2830) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1695 "FStar.SMTEncoding.Encode.fst"
let _76_2837 = (new_term_constant env x)
in (match (_76_2837) with
| (xxsym, xx, env') -> begin
(
# 1696 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1697 "FStar.SMTEncoding.Encode.fst"
let _76_2839 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _158_2042 = (FStar_Syntax_Print.bv_to_string x)
in (let _158_2041 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _158_2040 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _158_2042 _158_2041 _158_2040))))
end else begin
()
end
in (
# 1699 "FStar.SMTEncoding.Encode.fst"
let _76_2843 = (encode_term_pred None t1 env xx)
in (match (_76_2843) with
| (t, decls') -> begin
(
# 1700 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _158_2046 = (let _158_2045 = (FStar_Syntax_Print.bv_to_string x)
in (let _158_2044 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _158_2043 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _158_2045 _158_2044 _158_2043))))
in Some (_158_2046))
end else begin
None
end
in (
# 1704 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((FStar_SMTEncoding_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_76_2848, t)) -> begin
(
# 1710 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1712 "FStar.SMTEncoding.Encode.fst"
let _76_2856 = (encode_free_var env x t t_norm [])
in (match (_76_2856) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1717 "FStar.SMTEncoding.Encode.fst"
let _76_2870 = (encode_sigelt env se)
in (match (_76_2870) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1722 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1723 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _76_2877 -> (match (_76_2877) with
| (l, _76_2874, _76_2876) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1724 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _76_2884 -> (match (_76_2884) with
| (l, _76_2881, _76_2883) -> begin
(let _158_2054 = (FStar_All.pipe_left (fun _158_2050 -> FStar_SMTEncoding_Term.Echo (_158_2050)) (Prims.fst l))
in (let _158_2053 = (let _158_2052 = (let _158_2051 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_158_2051))
in (_158_2052)::[])
in (_158_2054)::_158_2053))
end))))
in (prefix, suffix))))

# 1728 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1729 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _158_2059 = (let _158_2058 = (let _158_2057 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _158_2057; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_158_2058)::[])
in (FStar_ST.op_Colon_Equals last_env _158_2059)))

# 1732 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_76_2890 -> begin
(
# 1734 "FStar.SMTEncoding.Encode.fst"
let _76_2893 = e
in {bindings = _76_2893.bindings; depth = _76_2893.depth; tcenv = tcenv; warn = _76_2893.warn; cache = _76_2893.cache; nolabels = _76_2893.nolabels; use_zfuel_name = _76_2893.use_zfuel_name; encode_non_total_function_typ = _76_2893.encode_non_total_function_typ})
end))

# 1735 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _76_2899::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1738 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _76_2901 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1741 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1742 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1742 "FStar.SMTEncoding.Encode.fst"
let _76_2907 = hd
in {bindings = _76_2907.bindings; depth = _76_2907.depth; tcenv = _76_2907.tcenv; warn = _76_2907.warn; cache = refs; nolabels = _76_2907.nolabels; use_zfuel_name = _76_2907.use_zfuel_name; encode_non_total_function_typ = _76_2907.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1744 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _76_2910 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _76_2914::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1747 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _76_2916 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1748 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _76_2917 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1749 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _76_2918 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_76_2921::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _76_2926 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1755 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1756 "FStar.SMTEncoding.Encode.fst"
let _76_2928 = (init_env tcenv)
in (
# 1757 "FStar.SMTEncoding.Encode.fst"
let _76_2930 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1759 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1760 "FStar.SMTEncoding.Encode.fst"
let _76_2933 = (push_env ())
in (
# 1761 "FStar.SMTEncoding.Encode.fst"
let _76_2935 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1763 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1764 "FStar.SMTEncoding.Encode.fst"
let _76_2938 = (let _158_2080 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _158_2080))
in (
# 1765 "FStar.SMTEncoding.Encode.fst"
let _76_2940 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1767 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1768 "FStar.SMTEncoding.Encode.fst"
let _76_2943 = (mark_env ())
in (
# 1769 "FStar.SMTEncoding.Encode.fst"
let _76_2945 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1771 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1772 "FStar.SMTEncoding.Encode.fst"
let _76_2948 = (reset_mark_env ())
in (
# 1773 "FStar.SMTEncoding.Encode.fst"
let _76_2950 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1775 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1776 "FStar.SMTEncoding.Encode.fst"
let _76_2953 = (commit_mark_env ())
in (
# 1777 "FStar.SMTEncoding.Encode.fst"
let _76_2955 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1779 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1780 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _158_2096 = (let _158_2095 = (let _158_2094 = (let _158_2093 = (let _158_2092 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _158_2092 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _158_2093 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _158_2094))
in FStar_SMTEncoding_Term.Caption (_158_2095))
in (_158_2096)::decls)
end else begin
decls
end)
in (
# 1784 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1785 "FStar.SMTEncoding.Encode.fst"
let _76_2964 = (encode_sigelt env se)
in (match (_76_2964) with
| (decls, env) -> begin
(
# 1786 "FStar.SMTEncoding.Encode.fst"
let _76_2965 = (set_env env)
in (let _158_2097 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _158_2097)))
end)))))

# 1789 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1790 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1791 "FStar.SMTEncoding.Encode.fst"
let _76_2970 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _158_2102 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _158_2102))
end else begin
()
end
in (
# 1793 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1794 "FStar.SMTEncoding.Encode.fst"
let _76_2977 = (encode_signature (
# 1794 "FStar.SMTEncoding.Encode.fst"
let _76_2973 = env
in {bindings = _76_2973.bindings; depth = _76_2973.depth; tcenv = _76_2973.tcenv; warn = false; cache = _76_2973.cache; nolabels = _76_2973.nolabels; use_zfuel_name = _76_2973.use_zfuel_name; encode_non_total_function_typ = _76_2973.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_76_2977) with
| (decls, env) -> begin
(
# 1795 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1797 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1800 "FStar.SMTEncoding.Encode.fst"
let _76_2983 = (set_env (
# 1800 "FStar.SMTEncoding.Encode.fst"
let _76_2981 = env
in {bindings = _76_2981.bindings; depth = _76_2981.depth; tcenv = _76_2981.tcenv; warn = true; cache = _76_2981.cache; nolabels = _76_2981.nolabels; use_zfuel_name = _76_2981.use_zfuel_name; encode_non_total_function_typ = _76_2981.encode_non_total_function_typ}))
in (
# 1801 "FStar.SMTEncoding.Encode.fst"
let _76_2985 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1802 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1805 "FStar.SMTEncoding.Encode.fst"
let solve : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (
# 1806 "FStar.SMTEncoding.Encode.fst"
let _76_2990 = (let _158_2111 = (let _158_2110 = (let _158_2109 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _158_2109))
in (FStar_Util.format1 "Starting query at %s" _158_2110))
in (push _158_2111))
in (
# 1807 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _76_2993 -> (match (()) with
| () -> begin
(let _158_2116 = (let _158_2115 = (let _158_2114 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _158_2114))
in (FStar_Util.format1 "Ending query at %s" _158_2115))
in (pop _158_2116))
end))
in (
# 1808 "FStar.SMTEncoding.Encode.fst"
let _76_3047 = (
# 1809 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1810 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1811 "FStar.SMTEncoding.Encode.fst"
let _76_3017 = (
# 1812 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1814 "FStar.SMTEncoding.Encode.fst"
let _76_3006 = (aux rest)
in (match (_76_3006) with
| (out, rest) -> begin
(
# 1815 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _158_2122 = (let _158_2121 = (FStar_Syntax_Syntax.mk_binder (
# 1816 "FStar.SMTEncoding.Encode.fst"
let _76_3008 = x
in {FStar_Syntax_Syntax.ppname = _76_3008.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _76_3008.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_158_2121)::out)
in (_158_2122, rest)))
end))
end
| _76_3011 -> begin
([], bindings)
end))
in (
# 1818 "FStar.SMTEncoding.Encode.fst"
let _76_3014 = (aux bindings)
in (match (_76_3014) with
| (closing, bindings) -> begin
(let _158_2123 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_158_2123, bindings))
end)))
in (match (_76_3017) with
| (q, bindings) -> begin
(
# 1820 "FStar.SMTEncoding.Encode.fst"
let _76_3026 = (let _158_2125 = (FStar_List.filter (fun _76_21 -> (match (_76_21) with
| FStar_TypeChecker_Env.Binding_sig (_76_3020) -> begin
false
end
| _76_3023 -> begin
true
end)) bindings)
in (encode_env_bindings env _158_2125))
in (match (_76_3026) with
| (env_decls, env) -> begin
(
# 1821 "FStar.SMTEncoding.Encode.fst"
let _76_3027 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _158_2126 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _158_2126))
end else begin
()
end
in (
# 1824 "FStar.SMTEncoding.Encode.fst"
let _76_3031 = (encode_formula q env)
in (match (_76_3031) with
| (phi, qdecls) -> begin
(
# 1827 "FStar.SMTEncoding.Encode.fst"
let _76_3036 = (FStar_SMTEncoding_ErrorReporting.label_goals [] phi [])
in (match (_76_3036) with
| (phi, labels, _76_3035) -> begin
(
# 1828 "FStar.SMTEncoding.Encode.fst"
let _76_3039 = (encode_labels labels)
in (match (_76_3039) with
| (label_prefix, label_suffix) -> begin
(
# 1829 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1833 "FStar.SMTEncoding.Encode.fst"
let qry = (let _158_2128 = (let _158_2127 = (FStar_SMTEncoding_Term.mkNot phi)
in (_158_2127, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_158_2128))
in (
# 1834 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_76_3047) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _76_3054); FStar_SMTEncoding_Term.hash = _76_3051; FStar_SMTEncoding_Term.freevars = _76_3049}, _76_3059) -> begin
(
# 1837 "FStar.SMTEncoding.Encode.fst"
let _76_3062 = (pop ())
in ())
end
| _76_3065 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1838 "FStar.SMTEncoding.Encode.fst"
let _76_3066 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _76_3070) -> begin
(
# 1840 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1841 "FStar.SMTEncoding.Encode.fst"
let _76_3074 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 1843 "FStar.SMTEncoding.Encode.fst"
let with_fuel = (fun p _76_3080 -> (match (_76_3080) with
| (n, i) -> begin
(let _158_2151 = (let _158_2150 = (let _158_2135 = (let _158_2134 = (FStar_Util.string_of_int n)
in (let _158_2133 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _158_2134 _158_2133)))
in FStar_SMTEncoding_Term.Caption (_158_2135))
in (let _158_2149 = (let _158_2148 = (let _158_2140 = (let _158_2139 = (let _158_2138 = (let _158_2137 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _158_2136 = (FStar_SMTEncoding_Term.n_fuel n)
in (_158_2137, _158_2136)))
in (FStar_SMTEncoding_Term.mkEq _158_2138))
in (_158_2139, None))
in FStar_SMTEncoding_Term.Assume (_158_2140))
in (let _158_2147 = (let _158_2146 = (let _158_2145 = (let _158_2144 = (let _158_2143 = (let _158_2142 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _158_2141 = (FStar_SMTEncoding_Term.n_fuel i)
in (_158_2142, _158_2141)))
in (FStar_SMTEncoding_Term.mkEq _158_2143))
in (_158_2144, None))
in FStar_SMTEncoding_Term.Assume (_158_2145))
in (_158_2146)::(p)::(FStar_SMTEncoding_Term.CheckSat)::[])
in (_158_2148)::_158_2147))
in (_158_2150)::_158_2149))
in (FStar_List.append _158_2151 suffix))
end))
in (
# 1850 "FStar.SMTEncoding.Encode.fst"
let check = (fun p -> (
# 1851 "FStar.SMTEncoding.Encode.fst"
let initial_config = (let _158_2155 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _158_2154 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_158_2155, _158_2154)))
in (
# 1852 "FStar.SMTEncoding.Encode.fst"
let alt_configs = (let _158_2174 = (let _158_2173 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _158_2158 = (let _158_2157 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _158_2156 = (FStar_ST.read FStar_Options.max_ifuel)
in (_158_2157, _158_2156)))
in (_158_2158)::[])
end else begin
[]
end
in (let _158_2172 = (let _158_2171 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _158_2161 = (let _158_2160 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _158_2159 = (FStar_ST.read FStar_Options.max_ifuel)
in (_158_2160, _158_2159)))
in (_158_2161)::[])
end else begin
[]
end
in (let _158_2170 = (let _158_2169 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _158_2164 = (let _158_2163 = (FStar_ST.read FStar_Options.max_fuel)
in (let _158_2162 = (FStar_ST.read FStar_Options.max_ifuel)
in (_158_2163, _158_2162)))
in (_158_2164)::[])
end else begin
[]
end
in (let _158_2168 = (let _158_2167 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _158_2166 = (let _158_2165 = (FStar_ST.read FStar_Options.min_fuel)
in (_158_2165, 1))
in (_158_2166)::[])
end else begin
[]
end
in (_158_2167)::[])
in (_158_2169)::_158_2168))
in (_158_2171)::_158_2170))
in (_158_2173)::_158_2172))
in (FStar_List.flatten _158_2174))
in (
# 1857 "FStar.SMTEncoding.Encode.fst"
let report = (fun errs -> (
# 1858 "FStar.SMTEncoding.Encode.fst"
let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _76_3089 -> begin
errs
end)
in (
# 1861 "FStar.SMTEncoding.Encode.fst"
let _76_3091 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _158_2182 = (let _158_2177 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _158_2177))
in (let _158_2181 = (let _158_2178 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _158_2178 FStar_Util.string_of_int))
in (let _158_2180 = (let _158_2179 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _158_2179 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _158_2182 _158_2181 _158_2180))))
end else begin
()
end
in (FStar_TypeChecker_Errors.add_errors tcenv errs))))
in (
# 1868 "FStar.SMTEncoding.Encode.fst"
let rec try_alt_configs = (fun p errs _76_22 -> (match (_76_22) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _158_2193 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _158_2193 (cb mi p [])))
end
| _76_3103 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _158_2195 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _158_2195 (fun _76_3109 -> (match (_76_3109) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _76_3112 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _76_3115 p alt _76_3120 -> (match ((_76_3115, _76_3120)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _158_2203 = (let _158_2200 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _158_2200))
in (let _158_2202 = (FStar_Util.string_of_int prev_fuel)
in (let _158_2201 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _158_2203 _158_2202 _158_2201))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _158_2204 = (with_fuel p initial_config)
in (FStar_SMTEncoding_Z3.ask fresh labels _158_2204 (cb initial_config p alt_configs))))))))
in (
# 1893 "FStar.SMTEncoding.Encode.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 1895 "FStar.SMTEncoding.Encode.fst"
let _76_3125 = (let _158_2210 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _158_2210 q))
in (match (_76_3125) with
| (b, cb) -> begin
if b then begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in (
# 1900 "FStar.SMTEncoding.Encode.fst"
let _76_3126 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _76_3129 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1906 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1907 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1908 "FStar.SMTEncoding.Encode.fst"
let _76_3133 = (push "query")
in (
# 1909 "FStar.SMTEncoding.Encode.fst"
let _76_3140 = (encode_formula_with_labels q env)
in (match (_76_3140) with
| (f, _76_3137, _76_3139) -> begin
(
# 1910 "FStar.SMTEncoding.Encode.fst"
let _76_3141 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _76_3145) -> begin
true
end
| _76_3149 -> begin
false
end))
end)))))

# 1915 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1929 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _76_3150 -> ()); FStar_TypeChecker_Env.push = (fun _76_3152 -> ()); FStar_TypeChecker_Env.pop = (fun _76_3154 -> ()); FStar_TypeChecker_Env.mark = (fun _76_3156 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _76_3158 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _76_3160 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _76_3162 _76_3164 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _76_3166 _76_3168 -> ()); FStar_TypeChecker_Env.solve = (fun _76_3170 _76_3172 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _76_3174 _76_3176 -> false); FStar_TypeChecker_Env.finish = (fun _76_3178 -> ()); FStar_TypeChecker_Env.refresh = (fun _76_3179 -> ())}





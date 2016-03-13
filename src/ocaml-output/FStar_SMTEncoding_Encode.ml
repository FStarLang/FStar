
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
let initial_ctr = 100
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
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _158_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _158_381 FStar_Option.isNone))
end
| _76_432 -> begin
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
in (let _158_393 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
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
let _76_444 = ()
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
| _76_454 -> begin
false
end))

# 290 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 291 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _76_465; FStar_SMTEncoding_Term.freevars = _76_463}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _76_483) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _76_490 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_76_492, []) -> begin
(
# 302 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _76_498 -> begin
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
| FStar_Const.Const_string (bytes, _76_520) -> begin
(let _158_463 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _158_463))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _158_465 = (let _158_464 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _158_464))
in (FStar_All.failwith _158_465))
end))

# 356 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 357 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 358 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_76_534) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_76_537) -> begin
(let _158_474 = (FStar_Syntax_Util.unrefine t)
in (aux true _158_474))
end
| _76_540 -> begin
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

# 367 "FStar.SMTEncoding.Encode.fst"
let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (
# 368 "FStar.SMTEncoding.Encode.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _76_548 -> begin
(let _158_481 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _158_481))
end)))

# 374 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 381 "FStar.SMTEncoding.Encode.fst"
let _76_552 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_531 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _158_531))
end else begin
()
end
in (
# 383 "FStar.SMTEncoding.Encode.fst"
let _76_580 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _76_559 b -> (match (_76_559) with
| (vars, guards, env, decls, names) -> begin
(
# 384 "FStar.SMTEncoding.Encode.fst"
let _76_574 = (
# 385 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 386 "FStar.SMTEncoding.Encode.fst"
let _76_565 = (gen_term_var env x)
in (match (_76_565) with
| (xxsym, xx, env') -> begin
(
# 387 "FStar.SMTEncoding.Encode.fst"
let _76_568 = (let _158_534 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _158_534 env xx))
in (match (_76_568) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_76_574) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_76_580) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 402 "FStar.SMTEncoding.Encode.fst"
let _76_587 = (encode_term t env)
in (match (_76_587) with
| (t, decls) -> begin
(let _158_539 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_158_539, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 406 "FStar.SMTEncoding.Encode.fst"
let _76_594 = (encode_term t env)
in (match (_76_594) with
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
# 414 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 415 "FStar.SMTEncoding.Encode.fst"
let _76_601 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
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
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _76_612) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _76_617) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 431 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _158_558 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_158_558, []))
end
| FStar_Syntax_Syntax.Tm_type (_76_626) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _76_630) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _158_559 = (encode_const c)
in (_158_559, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 447 "FStar.SMTEncoding.Encode.fst"
let _76_641 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_76_641) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 451 "FStar.SMTEncoding.Encode.fst"
let _76_648 = (encode_binders None binders env)
in (match (_76_648) with
| (vars, guards, env', decls, _76_647) -> begin
(
# 452 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _158_560 = (varops.fresh "f")
in (_158_560, FStar_SMTEncoding_Term.Term_sort))
in (
# 453 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 454 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 455 "FStar.SMTEncoding.Encode.fst"
let _76_654 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_76_654) with
| (pre_opt, res_t) -> begin
(
# 456 "FStar.SMTEncoding.Encode.fst"
let _76_657 = (encode_term_pred None res_t env' app)
in (match (_76_657) with
| (res_pred, decls') -> begin
(
# 457 "FStar.SMTEncoding.Encode.fst"
let _76_666 = (match (pre_opt) with
| None -> begin
(let _158_561 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_158_561, decls))
end
| Some (pre) -> begin
(
# 460 "FStar.SMTEncoding.Encode.fst"
let _76_663 = (encode_formula pre env')
in (match (_76_663) with
| (guard, decls0) -> begin
(let _158_562 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_158_562, (FStar_List.append decls decls0)))
end))
end)
in (match (_76_666) with
| (guards, guard_decls) -> begin
(
# 462 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _158_564 = (let _158_563 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _158_563))
in (FStar_SMTEncoding_Term.mkForall _158_564))
in (
# 467 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _158_566 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _158_566 (FStar_List.filter (fun _76_671 -> (match (_76_671) with
| (x, _76_670) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 468 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _76_677) -> begin
(let _158_569 = (let _158_568 = (let _158_567 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _158_567))
in (FStar_SMTEncoding_Term.mkApp _158_568))
in (_158_569, []))
end
| None -> begin
(
# 474 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Tm_arrow")
in (
# 475 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 476 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _158_570 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_158_570))
end else begin
None
end
in (
# 481 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 483 "FStar.SMTEncoding.Encode.fst"
let t = (let _158_572 = (let _158_571 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _158_571))
in (FStar_SMTEncoding_Term.mkApp _158_572))
in (
# 484 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _158_574 = (let _158_573 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_158_573, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_158_574))
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 489 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 490 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _158_581 = (let _158_580 = (let _158_579 = (let _158_578 = (let _158_577 = (let _158_576 = (let _158_575 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _158_575))
in (f_has_t, _158_576))
in (FStar_SMTEncoding_Term.mkImp _158_577))
in (((f_has_t)::[])::[], (fsym)::cvars, _158_578))
in (mkForall_fuel _158_579))
in (_158_580, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_158_581))
in (
# 491 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _158_585 = (let _158_584 = (let _158_583 = (let _158_582 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _158_582))
in (FStar_SMTEncoding_Term.mkForall _158_583))
in (_158_584, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_158_585))
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 495 "FStar.SMTEncoding.Encode.fst"
let _76_693 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 499 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Non_total_Tm_arrow")
in (
# 500 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 501 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (
# 502 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (let _158_587 = (let _158_586 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_158_586, None))
in FStar_SMTEncoding_Term.Assume (_158_587))
in (
# 503 "FStar.SMTEncoding.Encode.fst"
let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (
# 504 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 505 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 506 "FStar.SMTEncoding.Encode.fst"
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
| FStar_Syntax_Syntax.Tm_refine (_76_704) -> begin
(
# 513 "FStar.SMTEncoding.Encode.fst"
let _76_724 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _76_711; FStar_Syntax_Syntax.pos = _76_709; FStar_Syntax_Syntax.vars = _76_707} -> begin
(
# 515 "FStar.SMTEncoding.Encode.fst"
let _76_719 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_76_719) with
| (b, f) -> begin
(let _158_596 = (let _158_595 = (FStar_List.hd b)
in (Prims.fst _158_595))
in (_158_596, f))
end))
end
| _76_721 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_76_724) with
| (x, f) -> begin
(
# 519 "FStar.SMTEncoding.Encode.fst"
let _76_727 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_76_727) with
| (base_t, decls) -> begin
(
# 520 "FStar.SMTEncoding.Encode.fst"
let _76_731 = (gen_term_var env x)
in (match (_76_731) with
| (x, xtm, env') -> begin
(
# 521 "FStar.SMTEncoding.Encode.fst"
let _76_734 = (encode_formula f env')
in (match (_76_734) with
| (refinement, decls') -> begin
(
# 523 "FStar.SMTEncoding.Encode.fst"
let _76_737 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_737) with
| (fsym, fterm) -> begin
(
# 525 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _158_598 = (let _158_597 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_158_597, refinement))
in (FStar_SMTEncoding_Term.mkAnd _158_598))
in (
# 527 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _158_600 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _158_600 (FStar_List.filter (fun _76_742 -> (match (_76_742) with
| (y, _76_741) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 528 "FStar.SMTEncoding.Encode.fst"
let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (
# 529 "FStar.SMTEncoding.Encode.fst"
let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (
# 530 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _76_749, _76_751) -> begin
(let _158_603 = (let _158_602 = (let _158_601 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _158_601))
in (FStar_SMTEncoding_Term.mkApp _158_602))
in (_158_603, []))
end
| None -> begin
(
# 537 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Typ_refine")
in (
# 538 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 539 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 540 "FStar.SMTEncoding.Encode.fst"
let t = (let _158_605 = (let _158_604 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _158_604))
in (FStar_SMTEncoding_Term.mkApp _158_605))
in (
# 542 "FStar.SMTEncoding.Encode.fst"
let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 543 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 545 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (
# 546 "FStar.SMTEncoding.Encode.fst"
let assumption = (let _158_607 = (let _158_606 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _158_606))
in (FStar_SMTEncoding_Term.mkForall _158_607))
in (
# 548 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _158_614 = (let _158_613 = (let _158_612 = (let _158_611 = (let _158_610 = (let _158_609 = (let _158_608 = (FStar_Syntax_Print.term_to_string t0)
in Some (_158_608))
in (assumption, _158_609))
in FStar_SMTEncoding_Term.Assume (_158_610))
in (_158_611)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, None)))::_158_612)
in (tdecl)::_158_613)
in (FStar_List.append (FStar_List.append decls decls') _158_614))
in (
# 553 "FStar.SMTEncoding.Encode.fst"
let _76_764 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
# 558 "FStar.SMTEncoding.Encode.fst"
let ttm = (let _158_615 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _158_615))
in (
# 559 "FStar.SMTEncoding.Encode.fst"
let _76_773 = (encode_term_pred None k env ttm)
in (match (_76_773) with
| (t_has_k, decls) -> begin
(
# 560 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_76_776) -> begin
(
# 564 "FStar.SMTEncoding.Encode.fst"
let _76_780 = (FStar_Syntax_Util.head_and_args t0)
in (match (_76_780) with
| (head, args_e) -> begin
(match ((let _158_617 = (let _158_616 = (FStar_Syntax_Subst.compress head)
in _158_616.FStar_Syntax_Syntax.n)
in (_158_617, args_e))) with
| (FStar_Syntax_Syntax.Tm_abs (_76_782), _76_785) -> begin
(let _158_618 = (whnf env t)
in (encode_term _158_618 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), _::(v1, _)::(v2, _)::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(
# 571 "FStar.SMTEncoding.Encode.fst"
let _76_825 = (encode_term v1 env)
in (match (_76_825) with
| (v1, decls1) -> begin
(
# 572 "FStar.SMTEncoding.Encode.fst"
let _76_828 = (encode_term v2 env)
in (match (_76_828) with
| (v2, decls2) -> begin
(let _158_619 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_158_619, (FStar_List.append decls1 decls2)))
end))
end))
end
| _76_830 -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let _76_833 = (encode_args args_e env)
in (match (_76_833) with
| (args, decls) -> begin
(
# 578 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 579 "FStar.SMTEncoding.Encode.fst"
let _76_838 = (encode_term head env)
in (match (_76_838) with
| (head, decls') -> begin
(
# 580 "FStar.SMTEncoding.Encode.fst"
let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(
# 584 "FStar.SMTEncoding.Encode.fst"
let _76_847 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_76_847) with
| (formals, rest) -> begin
(
# 585 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _76_851 _76_855 -> (match ((_76_851, _76_855)) with
| ((bv, _76_850), (a, _76_854)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 586 "FStar.SMTEncoding.Encode.fst"
let ty = (let _158_624 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _158_624 (FStar_Syntax_Subst.subst subst)))
in (
# 587 "FStar.SMTEncoding.Encode.fst"
let _76_860 = (encode_term_pred None ty env app_tm)
in (match (_76_860) with
| (has_type, decls'') -> begin
(
# 588 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 589 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _158_626 = (let _158_625 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_158_625, None))
in FStar_SMTEncoding_Term.Assume (_158_626))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 593 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 594 "FStar.SMTEncoding.Encode.fst"
let _76_867 = (lookup_free_var_sym env fv)
in (match (_76_867) with
| (fname, fuel_args) -> begin
(
# 595 "FStar.SMTEncoding.Encode.fst"
let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (
# 598 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Subst.compress head)
in (
# 600 "FStar.SMTEncoding.Encode.fst"
let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _158_630 = (let _158_629 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _158_629 Prims.snd))
in Some (_158_630))
end
| FStar_Syntax_Syntax.Tm_ascribed (_76_899, t, _76_902) -> begin
Some (t)
end
| _76_906 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 611 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _158_631 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _158_631))
in (
# 612 "FStar.SMTEncoding.Encode.fst"
let _76_914 = (curried_arrow_formals_comp head_type)
in (match (_76_914) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _76_930 -> begin
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
# 626 "FStar.SMTEncoding.Encode.fst"
let _76_939 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_76_939) with
| (bs, body, opening) -> begin
(
# 627 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _76_941 -> (match (()) with
| () -> begin
(
# 628 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 629 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _158_634 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_158_634, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 634 "FStar.SMTEncoding.Encode.fst"
let _76_945 = (let _158_636 = (let _158_635 = (FStar_Syntax_Print.term_to_string t0)
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
# 640 "FStar.SMTEncoding.Encode.fst"
let c0 = (lc.FStar_Syntax_Syntax.comp ())
in (
# 641 "FStar.SMTEncoding.Encode.fst"
let c = (FStar_Syntax_Subst.subst_comp opening c0)
in (
# 644 "FStar.SMTEncoding.Encode.fst"
let _76_957 = (encode_binders None bs env)
in (match (_76_957) with
| (vars, guards, envbody, decls, _76_956) -> begin
(
# 645 "FStar.SMTEncoding.Encode.fst"
let _76_960 = (encode_term body envbody)
in (match (_76_960) with
| (body, decls') -> begin
(
# 646 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _158_641 = (let _158_640 = (let _158_639 = (let _158_638 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_158_638, body))
in (FStar_SMTEncoding_Term.mkImp _158_639))
in ([], vars, _158_640))
in (FStar_SMTEncoding_Term.mkForall _158_641))
in (
# 647 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 648 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _76_966, _76_968) -> begin
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
# 657 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 658 "FStar.SMTEncoding.Encode.fst"
let fsym = (varops.fresh "Exp_abs")
in (
# 659 "FStar.SMTEncoding.Encode.fst"
let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 660 "FStar.SMTEncoding.Encode.fst"
let f = (let _158_646 = (let _158_645 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _158_645))
in (FStar_SMTEncoding_Term.mkApp _158_646))
in (
# 661 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 662 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 663 "FStar.SMTEncoding.Encode.fst"
let _76_983 = (encode_term_pred None tfun env f)
in (match (_76_983) with
| (f_has_t, decls'') -> begin
(
# 664 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _158_648 = (let _158_647 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_158_647, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_158_648))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _158_655 = (let _158_654 = (let _158_653 = (let _158_652 = (let _158_651 = (let _158_650 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _158_649 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_158_650, _158_649)))
in (FStar_SMTEncoding_Term.mkImp _158_651))
in (((app)::[])::[], (FStar_List.append vars cvars), _158_652))
in (FStar_SMTEncoding_Term.mkForall _158_653))
in (_158_654, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_158_655))
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 669 "FStar.SMTEncoding.Encode.fst"
let _76_987 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_76_990, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_76_1002); FStar_Syntax_Syntax.lbunivs = _76_1000; FStar_Syntax_Syntax.lbtyp = _76_998; FStar_Syntax_Syntax.lbeff = _76_996; FStar_Syntax_Syntax.lbdef = _76_994}::_76_992), _76_1008) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _76_1017; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _76_1014; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_76_1027) -> begin
(
# 682 "FStar.SMTEncoding.Encode.fst"
let _76_1029 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 683 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 684 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _158_656 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_158_656, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 691 "FStar.SMTEncoding.Encode.fst"
let _76_1045 = (encode_term e1 env)
in (match (_76_1045) with
| (ee1, decls1) -> begin
(
# 692 "FStar.SMTEncoding.Encode.fst"
let _76_1048 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_76_1048) with
| (xs, e2) -> begin
(
# 693 "FStar.SMTEncoding.Encode.fst"
let _76_1052 = (FStar_List.hd xs)
in (match (_76_1052) with
| (x, _76_1051) -> begin
(
# 694 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 695 "FStar.SMTEncoding.Encode.fst"
let _76_1056 = (encode_body e2 env')
in (match (_76_1056) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 699 "FStar.SMTEncoding.Encode.fst"
let _76_1064 = (encode_term e env)
in (match (_76_1064) with
| (scr, decls) -> begin
(
# 700 "FStar.SMTEncoding.Encode.fst"
let _76_1101 = (FStar_List.fold_right (fun b _76_1068 -> (match (_76_1068) with
| (else_case, decls) -> begin
(
# 701 "FStar.SMTEncoding.Encode.fst"
let _76_1072 = (FStar_Syntax_Subst.open_branch b)
in (match (_76_1072) with
| (p, w, br) -> begin
(
# 702 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _76_1076 _76_1079 -> (match ((_76_1076, _76_1079)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 704 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 705 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 706 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _76_1085 -> (match (_76_1085) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 707 "FStar.SMTEncoding.Encode.fst"
let _76_1095 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 710 "FStar.SMTEncoding.Encode.fst"
let _76_1092 = (encode_term w env)
in (match (_76_1092) with
| (w, decls2) -> begin
(let _158_690 = (let _158_689 = (let _158_688 = (let _158_687 = (let _158_686 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _158_686))
in (FStar_SMTEncoding_Term.mkEq _158_687))
in (guard, _158_688))
in (FStar_SMTEncoding_Term.mkAnd _158_689))
in (_158_690, decls2))
end))
end)
in (match (_76_1095) with
| (guard, decls2) -> begin
(
# 712 "FStar.SMTEncoding.Encode.fst"
let _76_1098 = (encode_br br env)
in (match (_76_1098) with
| (br, decls3) -> begin
(let _158_691 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_158_691, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_76_1101) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _76_1107 -> begin
(let _158_694 = (encode_one_pat env pat)
in (_158_694)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 726 "FStar.SMTEncoding.Encode.fst"
let _76_1110 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_697 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _158_697))
end else begin
()
end
in (
# 727 "FStar.SMTEncoding.Encode.fst"
let _76_1114 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_76_1114) with
| (vars, pat_term) -> begin
(
# 729 "FStar.SMTEncoding.Encode.fst"
let _76_1126 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _76_1117 v -> (match (_76_1117) with
| (env, vars) -> begin
(
# 730 "FStar.SMTEncoding.Encode.fst"
let _76_1123 = (gen_term_var env v)
in (match (_76_1123) with
| (xx, _76_1121, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_76_1126) with
| (env, vars) -> begin
(
# 733 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_76_1131) -> begin
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
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(
# 741 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (
# 742 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _76_1153 -> (match (_76_1153) with
| (arg, _76_1152) -> begin
(
# 743 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _158_708 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _158_708)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 747 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_76_1160) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_76_1170) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _158_716 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _76_1180 -> (match (_76_1180) with
| (arg, _76_1179) -> begin
(
# 759 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _158_715 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _158_715)))
end))))
in (FStar_All.pipe_right _158_716 FStar_List.flatten))
end))
in (
# 763 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _76_1183 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (
# 765 "FStar.SMTEncoding.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (
# 775 "FStar.SMTEncoding.Encode.fst"
let _76_1199 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _76_1189 _76_1193 -> (match ((_76_1189, _76_1193)) with
| ((tms, decls), (t, _76_1192)) -> begin
(
# 776 "FStar.SMTEncoding.Encode.fst"
let _76_1196 = (encode_term t env)
in (match (_76_1196) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_76_1199) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 781 "FStar.SMTEncoding.Encode.fst"
let _76_1205 = (encode_formula_with_labels phi env)
in (match (_76_1205) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _76_1208 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 789 "FStar.SMTEncoding.Encode.fst"
let _76_1217 = (let _158_731 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _158_731))
in (match (_76_1217) with
| (head, args) -> begin
(match ((let _158_733 = (let _158_732 = (FStar_Syntax_Util.un_uinst head)
in _158_732.FStar_Syntax_Syntax.n)
in (_158_733, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _76_1221) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _76_1234::(hd, _76_1231)::(tl, _76_1227)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _158_734 = (list_elements tl)
in (hd)::_158_734)
end
| _76_1238 -> begin
(
# 794 "FStar.SMTEncoding.Encode.fst"
let _76_1239 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 796 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 797 "FStar.SMTEncoding.Encode.fst"
let _76_1245 = (let _158_737 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _158_737 FStar_Syntax_Util.head_and_args))
in (match (_76_1245) with
| (head, args) -> begin
(match ((let _158_739 = (let _158_738 = (FStar_Syntax_Util.un_uinst head)
in _158_738.FStar_Syntax_Syntax.n)
in (_158_739, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_76_1253, _76_1255)::(e, _76_1250)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _76_1263)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _76_1268 -> begin
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
let _76_1276 = (let _158_744 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _158_744 FStar_Syntax_Util.head_and_args))
in (match (_76_1276) with
| (head, args) -> begin
(match ((let _158_746 = (let _158_745 = (FStar_Syntax_Util.un_uinst head)
in _158_745.FStar_Syntax_Syntax.n)
in (_158_746, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _76_1281)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _76_1286 -> begin
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
| _76_1293 -> begin
(let _158_750 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_158_750)::[])
end)
end
| _76_1295 -> begin
(let _158_751 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_158_751)::[])
end))))
in (
# 820 "FStar.SMTEncoding.Encode.fst"
let _76_1329 = (match ((let _158_752 = (FStar_Syntax_Subst.compress t)
in _158_752.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 822 "FStar.SMTEncoding.Encode.fst"
let _76_1302 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_76_1302) with
| (binders, c) -> begin
(
# 823 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _76_1314)::(post, _76_1310)::(pats, _76_1306)::[] -> begin
(
# 826 "FStar.SMTEncoding.Encode.fst"
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
| _76_1322 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _76_1324 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_76_1329) with
| (binders, pre, post, patterns) -> begin
(
# 834 "FStar.SMTEncoding.Encode.fst"
let _76_1336 = (encode_binders None binders env)
in (match (_76_1336) with
| (vars, guards, env, decls, _76_1335) -> begin
(
# 837 "FStar.SMTEncoding.Encode.fst"
let _76_1349 = (let _158_757 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 838 "FStar.SMTEncoding.Encode.fst"
let _76_1346 = (let _158_756 = (FStar_All.pipe_right branch (FStar_List.map (fun _76_1341 -> (match (_76_1341) with
| (t, _76_1340) -> begin
(encode_term t (
# 838 "FStar.SMTEncoding.Encode.fst"
let _76_1342 = env
in {bindings = _76_1342.bindings; depth = _76_1342.depth; tcenv = _76_1342.tcenv; warn = _76_1342.warn; cache = _76_1342.cache; nolabels = _76_1342.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _76_1342.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _158_756 FStar_List.unzip))
in (match (_76_1346) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _158_757 FStar_List.unzip))
in (match (_76_1349) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _158_760 = (let _158_759 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _158_759 e))
in (_158_760)::p))))
end
| _76_1359 -> begin
(
# 851 "FStar.SMTEncoding.Encode.fst"
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
| _76_1371 -> begin
pats
end))
in (let _158_769 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _158_769 vars)))
end)
end)
in (
# 858 "FStar.SMTEncoding.Encode.fst"
let env = (
# 858 "FStar.SMTEncoding.Encode.fst"
let _76_1373 = env
in {bindings = _76_1373.bindings; depth = _76_1373.depth; tcenv = _76_1373.tcenv; warn = _76_1373.warn; cache = _76_1373.cache; nolabels = true; use_zfuel_name = _76_1373.use_zfuel_name; encode_non_total_function_typ = _76_1373.encode_non_total_function_typ})
in (
# 859 "FStar.SMTEncoding.Encode.fst"
let _76_1378 = (let _158_770 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _158_770 env))
in (match (_76_1378) with
| (pre, decls'') -> begin
(
# 860 "FStar.SMTEncoding.Encode.fst"
let _76_1381 = (let _158_771 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _158_771 env))
in (match (_76_1381) with
| (post, decls''') -> begin
(
# 861 "FStar.SMTEncoding.Encode.fst"
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
# 865 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 866 "FStar.SMTEncoding.Encode.fst"
let _76_1395 = (FStar_Util.fold_map (fun decls x -> (
# 866 "FStar.SMTEncoding.Encode.fst"
let _76_1392 = (encode_term (Prims.fst x) env)
in (match (_76_1392) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_76_1395) with
| (decls, args) -> begin
(let _158_794 = (f args)
in (_158_794, [], decls))
end)))
in (
# 869 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _76_1398 -> (f, [], []))
in (
# 870 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _158_808 = (FStar_List.hd l)
in (FStar_All.pipe_left f _158_808)))
in (
# 871 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _76_8 -> (match (_76_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _76_1409 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 875 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 876 "FStar.SMTEncoding.Encode.fst"
let _76_1429 = (FStar_List.fold_right (fun _76_1417 _76_1421 -> (match ((_76_1417, _76_1421)) with
| ((t, _76_1416), (phis, labs, decls)) -> begin
(
# 878 "FStar.SMTEncoding.Encode.fst"
let _76_1425 = (encode_formula_with_labels t env)
in (match (_76_1425) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end)) l ([], [], []))
in (match (_76_1429) with
| (phis, labs, decls) -> begin
(let _158_833 = (f phis)
in (_158_833, labs, decls))
end)))
in (
# 883 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _76_9 -> (match (_76_9) with
| _76_1436::_76_1434::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 887 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _76_10 -> (match (_76_10) with
| (lhs, _76_1447)::(rhs, _76_1443)::[] -> begin
(
# 889 "FStar.SMTEncoding.Encode.fst"
let _76_1453 = (encode_formula_with_labels rhs env)
in (match (_76_1453) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _76_1456) -> begin
(l1, labs1, decls1)
end
| _76_1460 -> begin
(
# 893 "FStar.SMTEncoding.Encode.fst"
let _76_1464 = (encode_formula_with_labels lhs env)
in (match (_76_1464) with
| (l2, labs2, decls2) -> begin
(let _158_838 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_158_838, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _76_1466 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 898 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _76_11 -> (match (_76_11) with
| (guard, _76_1479)::(_then, _76_1475)::(_else, _76_1471)::[] -> begin
(
# 900 "FStar.SMTEncoding.Encode.fst"
let _76_1485 = (encode_formula_with_labels guard env)
in (match (_76_1485) with
| (g, labs1, decls1) -> begin
(
# 901 "FStar.SMTEncoding.Encode.fst"
let _76_1489 = (encode_formula_with_labels _then env)
in (match (_76_1489) with
| (t, labs2, decls2) -> begin
(
# 902 "FStar.SMTEncoding.Encode.fst"
let _76_1493 = (encode_formula_with_labels _else env)
in (match (_76_1493) with
| (e, labs3, decls3) -> begin
(
# 903 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _76_1496 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 908 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _158_850 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _158_850)))
in (
# 909 "FStar.SMTEncoding.Encode.fst"
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
# 921 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 923 "FStar.SMTEncoding.Encode.fst"
let _76_1515 = (encode_formula_with_labels phi' env)
in (match (_76_1515) with
| (phi, labs, decls) -> begin
(let _158_906 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_158_906, [], decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 927 "FStar.SMTEncoding.Encode.fst"
let _76_1522 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_76_1522) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _76_1529; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _76_1526; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 931 "FStar.SMTEncoding.Encode.fst"
let _76_1540 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_76_1540) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 935 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _76_1557::(x, _76_1554)::(t, _76_1550)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(
# 938 "FStar.SMTEncoding.Encode.fst"
let _76_1562 = (encode_term x env)
in (match (_76_1562) with
| (x, decls) -> begin
(
# 939 "FStar.SMTEncoding.Encode.fst"
let _76_1565 = (encode_term t env)
in (match (_76_1565) with
| (t, decls') -> begin
(let _158_907 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_158_907, [], (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _76_1583::_76_1581::(r, _76_1578)::(msg, _76_1574)::(phi, _76_1570)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _158_911 = (let _158_908 = (FStar_Syntax_Subst.compress r)
in _158_908.FStar_Syntax_Syntax.n)
in (let _158_910 = (let _158_909 = (FStar_Syntax_Subst.compress msg)
in _158_909.FStar_Syntax_Syntax.n)
in (_158_911, _158_910)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _76_1591))) -> begin
(
# 945 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _76_1598 -> begin
(fallback phi)
end)
end
| _76_1600 -> begin
(
# 952 "FStar.SMTEncoding.Encode.fst"
let _76_1603 = (encode_term phi env)
in (match (_76_1603) with
| (tt, decls) -> begin
(let _158_912 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_158_912, [], decls))
end))
end))
end
| _76_1605 -> begin
(
# 957 "FStar.SMTEncoding.Encode.fst"
let _76_1608 = (encode_term phi env)
in (match (_76_1608) with
| (tt, decls) -> begin
(let _158_913 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_158_913, [], decls))
end))
end))
in (
# 960 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 961 "FStar.SMTEncoding.Encode.fst"
let _76_1620 = (encode_binders None bs env)
in (match (_76_1620) with
| (vars, guards, env, decls, _76_1619) -> begin
(
# 962 "FStar.SMTEncoding.Encode.fst"
let _76_1633 = (let _158_925 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 963 "FStar.SMTEncoding.Encode.fst"
let _76_1630 = (let _158_924 = (FStar_All.pipe_right p (FStar_List.map (fun _76_1625 -> (match (_76_1625) with
| (t, _76_1624) -> begin
(encode_term t (
# 963 "FStar.SMTEncoding.Encode.fst"
let _76_1626 = env
in {bindings = _76_1626.bindings; depth = _76_1626.depth; tcenv = _76_1626.tcenv; warn = _76_1626.warn; cache = _76_1626.cache; nolabels = _76_1626.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _76_1626.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _158_924 FStar_List.unzip))
in (match (_76_1630) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _158_925 FStar_List.unzip))
in (match (_76_1633) with
| (pats, decls') -> begin
(
# 965 "FStar.SMTEncoding.Encode.fst"
let _76_1637 = (encode_formula_with_labels body env)
in (match (_76_1637) with
| (body, labs, decls'') -> begin
(let _158_926 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _158_926, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 968 "FStar.SMTEncoding.Encode.fst"
let _76_1638 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_927 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _158_927))
end else begin
()
end
in (
# 970 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _76_1650 -> (match (_76_1650) with
| (l, _76_1649) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_76_1653, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 980 "FStar.SMTEncoding.Encode.fst"
let _76_1663 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _158_944 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _158_944))
end else begin
()
end
in (
# 983 "FStar.SMTEncoding.Encode.fst"
let _76_1671 = (encode_q_body env vars pats body)
in (match (_76_1671) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _158_947 = (let _158_946 = (let _158_945 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _158_945))
in (FStar_SMTEncoding_Term.mkForall _158_946))
in (_158_947, labs, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 987 "FStar.SMTEncoding.Encode.fst"
let _76_1684 = (encode_q_body env vars pats body)
in (match (_76_1684) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _158_950 = (let _158_949 = (let _158_948 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _158_948))
in (FStar_SMTEncoding_Term.mkExists _158_949))
in (_158_950, labs, decls))
end))
end))))))))))))))))

# 996 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 996 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1002 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 1003 "FStar.SMTEncoding.Encode.fst"
let _76_1690 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_1690) with
| (asym, a) -> begin
(
# 1004 "FStar.SMTEncoding.Encode.fst"
let _76_1693 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_1693) with
| (xsym, x) -> begin
(
# 1005 "FStar.SMTEncoding.Encode.fst"
let _76_1696 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_1696) with
| (ysym, y) -> begin
(
# 1006 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 1007 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1008 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _158_993 = (let _158_992 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _158_992))
in (FStar_SMTEncoding_Term.mkApp _158_993))
in (
# 1009 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _158_995 = (let _158_994 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _158_994, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_158_995))
in (let _158_1001 = (let _158_1000 = (let _158_999 = (let _158_998 = (let _158_997 = (let _158_996 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _158_996))
in (FStar_SMTEncoding_Term.mkForall _158_997))
in (_158_998, None))
in FStar_SMTEncoding_Term.Assume (_158_999))
in (_158_1000)::[])
in (vname_decl)::_158_1001))))
in (
# 1012 "FStar.SMTEncoding.Encode.fst"
let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1013 "FStar.SMTEncoding.Encode.fst"
let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1014 "FStar.SMTEncoding.Encode.fst"
let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1015 "FStar.SMTEncoding.Encode.fst"
let prims = (let _158_1161 = (let _158_1010 = (let _158_1009 = (let _158_1008 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1008))
in (quant axy _158_1009))
in (FStar_Syntax_Const.op_Eq, _158_1010))
in (let _158_1160 = (let _158_1159 = (let _158_1017 = (let _158_1016 = (let _158_1015 = (let _158_1014 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _158_1014))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1015))
in (quant axy _158_1016))
in (FStar_Syntax_Const.op_notEq, _158_1017))
in (let _158_1158 = (let _158_1157 = (let _158_1026 = (let _158_1025 = (let _158_1024 = (let _158_1023 = (let _158_1022 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1021 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1022, _158_1021)))
in (FStar_SMTEncoding_Term.mkLT _158_1023))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1024))
in (quant xy _158_1025))
in (FStar_Syntax_Const.op_LT, _158_1026))
in (let _158_1156 = (let _158_1155 = (let _158_1035 = (let _158_1034 = (let _158_1033 = (let _158_1032 = (let _158_1031 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1030 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1031, _158_1030)))
in (FStar_SMTEncoding_Term.mkLTE _158_1032))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1033))
in (quant xy _158_1034))
in (FStar_Syntax_Const.op_LTE, _158_1035))
in (let _158_1154 = (let _158_1153 = (let _158_1044 = (let _158_1043 = (let _158_1042 = (let _158_1041 = (let _158_1040 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1039 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1040, _158_1039)))
in (FStar_SMTEncoding_Term.mkGT _158_1041))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1042))
in (quant xy _158_1043))
in (FStar_Syntax_Const.op_GT, _158_1044))
in (let _158_1152 = (let _158_1151 = (let _158_1053 = (let _158_1052 = (let _158_1051 = (let _158_1050 = (let _158_1049 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1048 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1049, _158_1048)))
in (FStar_SMTEncoding_Term.mkGTE _158_1050))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1051))
in (quant xy _158_1052))
in (FStar_Syntax_Const.op_GTE, _158_1053))
in (let _158_1150 = (let _158_1149 = (let _158_1062 = (let _158_1061 = (let _158_1060 = (let _158_1059 = (let _158_1058 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1057 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1058, _158_1057)))
in (FStar_SMTEncoding_Term.mkSub _158_1059))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1060))
in (quant xy _158_1061))
in (FStar_Syntax_Const.op_Subtraction, _158_1062))
in (let _158_1148 = (let _158_1147 = (let _158_1069 = (let _158_1068 = (let _158_1067 = (let _158_1066 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _158_1066))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1067))
in (quant qx _158_1068))
in (FStar_Syntax_Const.op_Minus, _158_1069))
in (let _158_1146 = (let _158_1145 = (let _158_1078 = (let _158_1077 = (let _158_1076 = (let _158_1075 = (let _158_1074 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1073 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1074, _158_1073)))
in (FStar_SMTEncoding_Term.mkAdd _158_1075))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1076))
in (quant xy _158_1077))
in (FStar_Syntax_Const.op_Addition, _158_1078))
in (let _158_1144 = (let _158_1143 = (let _158_1087 = (let _158_1086 = (let _158_1085 = (let _158_1084 = (let _158_1083 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1082 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1083, _158_1082)))
in (FStar_SMTEncoding_Term.mkMul _158_1084))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1085))
in (quant xy _158_1086))
in (FStar_Syntax_Const.op_Multiply, _158_1087))
in (let _158_1142 = (let _158_1141 = (let _158_1096 = (let _158_1095 = (let _158_1094 = (let _158_1093 = (let _158_1092 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1091 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1092, _158_1091)))
in (FStar_SMTEncoding_Term.mkDiv _158_1093))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1094))
in (quant xy _158_1095))
in (FStar_Syntax_Const.op_Division, _158_1096))
in (let _158_1140 = (let _158_1139 = (let _158_1105 = (let _158_1104 = (let _158_1103 = (let _158_1102 = (let _158_1101 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1100 = (FStar_SMTEncoding_Term.unboxInt y)
in (_158_1101, _158_1100)))
in (FStar_SMTEncoding_Term.mkMod _158_1102))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _158_1103))
in (quant xy _158_1104))
in (FStar_Syntax_Const.op_Modulus, _158_1105))
in (let _158_1138 = (let _158_1137 = (let _158_1114 = (let _158_1113 = (let _158_1112 = (let _158_1111 = (let _158_1110 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _158_1109 = (FStar_SMTEncoding_Term.unboxBool y)
in (_158_1110, _158_1109)))
in (FStar_SMTEncoding_Term.mkAnd _158_1111))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1112))
in (quant xy _158_1113))
in (FStar_Syntax_Const.op_And, _158_1114))
in (let _158_1136 = (let _158_1135 = (let _158_1123 = (let _158_1122 = (let _158_1121 = (let _158_1120 = (let _158_1119 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _158_1118 = (FStar_SMTEncoding_Term.unboxBool y)
in (_158_1119, _158_1118)))
in (FStar_SMTEncoding_Term.mkOr _158_1120))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1121))
in (quant xy _158_1122))
in (FStar_Syntax_Const.op_Or, _158_1123))
in (let _158_1134 = (let _158_1133 = (let _158_1130 = (let _158_1129 = (let _158_1128 = (let _158_1127 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _158_1127))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_1128))
in (quant qx _158_1129))
in (FStar_Syntax_Const.op_Negation, _158_1130))
in (_158_1133)::[])
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
in (_158_1159)::_158_1158))
in (_158_1161)::_158_1160))
in (
# 1032 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _158_1193 = (FStar_All.pipe_right prims (FStar_List.filter (fun _76_1716 -> (match (_76_1716) with
| (l', _76_1715) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _158_1193 (FStar_List.collect (fun _76_1720 -> (match (_76_1720) with
| (_76_1718, b) -> begin
(b v)
end))))))
in (
# 1034 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _76_1726 -> (match (_76_1726) with
| (l', _76_1725) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1039 "FStar.SMTEncoding.Encode.fst"
let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (
# 1040 "FStar.SMTEncoding.Encode.fst"
let _76_1732 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_1732) with
| (xxsym, xx) -> begin
(
# 1041 "FStar.SMTEncoding.Encode.fst"
let _76_1735 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_1735) with
| (ffsym, ff) -> begin
(
# 1042 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _158_1219 = (let _158_1218 = (let _158_1217 = (let _158_1216 = (let _158_1215 = (let _158_1214 = (let _158_1213 = (let _158_1212 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _158_1212))
in (FStar_SMTEncoding_Term.mkEq _158_1213))
in (xx_has_type, _158_1214))
in (FStar_SMTEncoding_Term.mkImp _158_1215))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _158_1216))
in (FStar_SMTEncoding_Term.mkForall _158_1217))
in (_158_1218, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_158_1219)))
end))
end)))

# 1046 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1047 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1048 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1050 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1051 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1053 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun env nm tt -> (
# 1054 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _158_1240 = (let _158_1231 = (let _158_1230 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_158_1230, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_158_1231))
in (let _158_1239 = (let _158_1238 = (let _158_1237 = (let _158_1236 = (let _158_1235 = (let _158_1234 = (let _158_1233 = (let _158_1232 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _158_1232))
in (FStar_SMTEncoding_Term.mkImp _158_1233))
in (((typing_pred)::[])::[], (xx)::[], _158_1234))
in (mkForall_fuel _158_1235))
in (_158_1236, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1237))
in (_158_1238)::[])
in (_158_1240)::_158_1239))))
in (
# 1057 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun env nm tt -> (
# 1058 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1059 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1060 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _158_1263 = (let _158_1252 = (let _158_1251 = (let _158_1250 = (let _158_1249 = (let _158_1248 = (let _158_1247 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _158_1247))
in (FStar_SMTEncoding_Term.mkImp _158_1248))
in (((typing_pred)::[])::[], (xx)::[], _158_1249))
in (mkForall_fuel _158_1250))
in (_158_1251, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1252))
in (let _158_1262 = (let _158_1261 = (let _158_1260 = (let _158_1259 = (let _158_1258 = (let _158_1257 = (let _158_1254 = (let _158_1253 = (FStar_SMTEncoding_Term.boxBool b)
in (_158_1253)::[])
in (_158_1254)::[])
in (let _158_1256 = (let _158_1255 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _158_1255 tt))
in (_158_1257, (bb)::[], _158_1256)))
in (FStar_SMTEncoding_Term.mkForall _158_1258))
in (_158_1259, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_158_1260))
in (_158_1261)::[])
in (_158_1263)::_158_1262))))))
in (
# 1063 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun env nm tt -> (
# 1064 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1065 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1066 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1067 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1068 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1069 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1070 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _158_1277 = (let _158_1276 = (let _158_1275 = (let _158_1274 = (let _158_1273 = (let _158_1272 = (FStar_SMTEncoding_Term.boxInt a)
in (let _158_1271 = (let _158_1270 = (FStar_SMTEncoding_Term.boxInt b)
in (_158_1270)::[])
in (_158_1272)::_158_1271))
in (tt)::_158_1273)
in (tt)::_158_1274)
in ("Prims.Precedes", _158_1275))
in (FStar_SMTEncoding_Term.mkApp _158_1276))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _158_1277))
in (
# 1071 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _158_1278 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _158_1278))
in (let _158_1320 = (let _158_1284 = (let _158_1283 = (let _158_1282 = (let _158_1281 = (let _158_1280 = (let _158_1279 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _158_1279))
in (FStar_SMTEncoding_Term.mkImp _158_1280))
in (((typing_pred)::[])::[], (xx)::[], _158_1281))
in (mkForall_fuel _158_1282))
in (_158_1283, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1284))
in (let _158_1319 = (let _158_1318 = (let _158_1292 = (let _158_1291 = (let _158_1290 = (let _158_1289 = (let _158_1286 = (let _158_1285 = (FStar_SMTEncoding_Term.boxInt b)
in (_158_1285)::[])
in (_158_1286)::[])
in (let _158_1288 = (let _158_1287 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _158_1287 tt))
in (_158_1289, (bb)::[], _158_1288)))
in (FStar_SMTEncoding_Term.mkForall _158_1290))
in (_158_1291, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_158_1292))
in (let _158_1317 = (let _158_1316 = (let _158_1315 = (let _158_1314 = (let _158_1313 = (let _158_1312 = (let _158_1311 = (let _158_1310 = (let _158_1309 = (let _158_1308 = (let _158_1307 = (let _158_1306 = (let _158_1295 = (let _158_1294 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _158_1293 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_158_1294, _158_1293)))
in (FStar_SMTEncoding_Term.mkGT _158_1295))
in (let _158_1305 = (let _158_1304 = (let _158_1298 = (let _158_1297 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _158_1296 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_158_1297, _158_1296)))
in (FStar_SMTEncoding_Term.mkGTE _158_1298))
in (let _158_1303 = (let _158_1302 = (let _158_1301 = (let _158_1300 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _158_1299 = (FStar_SMTEncoding_Term.unboxInt x)
in (_158_1300, _158_1299)))
in (FStar_SMTEncoding_Term.mkLT _158_1301))
in (_158_1302)::[])
in (_158_1304)::_158_1303))
in (_158_1306)::_158_1305))
in (typing_pred_y)::_158_1307)
in (typing_pred)::_158_1308)
in (FStar_SMTEncoding_Term.mk_and_l _158_1309))
in (_158_1310, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _158_1311))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _158_1312))
in (mkForall_fuel _158_1313))
in (_158_1314, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_158_1315))
in (_158_1316)::[])
in (_158_1318)::_158_1317))
in (_158_1320)::_158_1319)))))))))))
in (
# 1083 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun env nm tt -> (let _158_1331 = (let _158_1330 = (let _158_1329 = (let _158_1328 = (let _158_1327 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _158_1327))
in (FStar_SMTEncoding_Term.mkEq _158_1328))
in (_158_1329, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_158_1330))
in (_158_1331)::[]))
in (
# 1085 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun env nm tt -> (
# 1086 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1087 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1088 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _158_1354 = (let _158_1343 = (let _158_1342 = (let _158_1341 = (let _158_1340 = (let _158_1339 = (let _158_1338 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _158_1338))
in (FStar_SMTEncoding_Term.mkImp _158_1339))
in (((typing_pred)::[])::[], (xx)::[], _158_1340))
in (mkForall_fuel _158_1341))
in (_158_1342, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1343))
in (let _158_1353 = (let _158_1352 = (let _158_1351 = (let _158_1350 = (let _158_1349 = (let _158_1348 = (let _158_1345 = (let _158_1344 = (FStar_SMTEncoding_Term.boxString b)
in (_158_1344)::[])
in (_158_1345)::[])
in (let _158_1347 = (let _158_1346 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _158_1346 tt))
in (_158_1348, (bb)::[], _158_1347)))
in (FStar_SMTEncoding_Term.mkForall _158_1349))
in (_158_1350, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_158_1351))
in (_158_1352)::[])
in (_158_1354)::_158_1353))))))
in (
# 1091 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun env reft_name _76_1778 -> (
# 1092 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1093 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1094 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let refa = (let _158_1363 = (let _158_1362 = (let _158_1361 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_158_1361)::[])
in (reft_name, _158_1362))
in (FStar_SMTEncoding_Term.mkApp _158_1363))
in (
# 1096 "FStar.SMTEncoding.Encode.fst"
let refb = (let _158_1366 = (let _158_1365 = (let _158_1364 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_158_1364)::[])
in (reft_name, _158_1365))
in (FStar_SMTEncoding_Term.mkApp _158_1366))
in (
# 1097 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1098 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _158_1385 = (let _158_1372 = (let _158_1371 = (let _158_1370 = (let _158_1369 = (let _158_1368 = (let _158_1367 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _158_1367))
in (FStar_SMTEncoding_Term.mkImp _158_1368))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _158_1369))
in (mkForall_fuel _158_1370))
in (_158_1371, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_158_1372))
in (let _158_1384 = (let _158_1383 = (let _158_1382 = (let _158_1381 = (let _158_1380 = (let _158_1379 = (let _158_1378 = (let _158_1377 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _158_1376 = (let _158_1375 = (let _158_1374 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _158_1373 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_158_1374, _158_1373)))
in (FStar_SMTEncoding_Term.mkEq _158_1375))
in (_158_1377, _158_1376)))
in (FStar_SMTEncoding_Term.mkImp _158_1378))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _158_1379))
in (mkForall_fuel' 2 _158_1380))
in (_158_1381, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_158_1382))
in (_158_1383)::[])
in (_158_1385)::_158_1384))))))))))
in (
# 1101 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun env nm false_tm -> (
# 1102 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _158_1394 = (let _158_1393 = (let _158_1392 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_158_1392, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1393))
in (_158_1394)::[])))
in (
# 1104 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun env conj _76_1795 -> (
# 1105 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1106 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1107 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1109 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1403 = (let _158_1402 = (let _158_1401 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_158_1401)::[])
in ("Valid", _158_1402))
in (FStar_SMTEncoding_Term.mkApp _158_1403))
in (
# 1110 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _158_1410 = (let _158_1409 = (let _158_1408 = (let _158_1407 = (let _158_1406 = (let _158_1405 = (let _158_1404 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_158_1404, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1405))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1406))
in (FStar_SMTEncoding_Term.mkForall _158_1407))
in (_158_1408, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1409))
in (_158_1410)::[])))))))))
in (
# 1113 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun env disj _76_1807 -> (
# 1114 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1115 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1116 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1117 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1118 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1419 = (let _158_1418 = (let _158_1417 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_158_1417)::[])
in ("Valid", _158_1418))
in (FStar_SMTEncoding_Term.mkApp _158_1419))
in (
# 1119 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1120 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _158_1426 = (let _158_1425 = (let _158_1424 = (let _158_1423 = (let _158_1422 = (let _158_1421 = (let _158_1420 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_158_1420, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1421))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1422))
in (FStar_SMTEncoding_Term.mkForall _158_1423))
in (_158_1424, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1425))
in (_158_1426)::[])))))))))
in (
# 1122 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun env eq2 tt -> (
# 1123 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1125 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1128 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1129 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1130 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1131 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1435 = (let _158_1434 = (let _158_1433 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_158_1433)::[])
in ("Valid", _158_1434))
in (FStar_SMTEncoding_Term.mkApp _158_1435))
in (let _158_1442 = (let _158_1441 = (let _158_1440 = (let _158_1439 = (let _158_1438 = (let _158_1437 = (let _158_1436 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_158_1436, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1437))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _158_1438))
in (FStar_SMTEncoding_Term.mkForall _158_1439))
in (_158_1440, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1441))
in (_158_1442)::[])))))))))))
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun env imp tt -> (
# 1134 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1135 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1136 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1137 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1138 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1451 = (let _158_1450 = (let _158_1449 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_158_1449)::[])
in ("Valid", _158_1450))
in (FStar_SMTEncoding_Term.mkApp _158_1451))
in (
# 1139 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1140 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _158_1458 = (let _158_1457 = (let _158_1456 = (let _158_1455 = (let _158_1454 = (let _158_1453 = (let _158_1452 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_158_1452, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1453))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1454))
in (FStar_SMTEncoding_Term.mkForall _158_1455))
in (_158_1456, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1457))
in (_158_1458)::[])))))))))
in (
# 1142 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun env iff tt -> (
# 1143 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1144 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1145 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1467 = (let _158_1466 = (let _158_1465 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_158_1465)::[])
in ("Valid", _158_1466))
in (FStar_SMTEncoding_Term.mkApp _158_1467))
in (
# 1148 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1149 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _158_1474 = (let _158_1473 = (let _158_1472 = (let _158_1471 = (let _158_1470 = (let _158_1469 = (let _158_1468 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_158_1468, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1469))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1470))
in (FStar_SMTEncoding_Term.mkForall _158_1471))
in (_158_1472, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1473))
in (_158_1474)::[])))))))))
in (
# 1151 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun env for_all tt -> (
# 1152 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1154 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1155 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1156 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1157 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1158 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1483 = (let _158_1482 = (let _158_1481 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_158_1481)::[])
in ("Valid", _158_1482))
in (FStar_SMTEncoding_Term.mkApp _158_1483))
in (
# 1159 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _158_1486 = (let _158_1485 = (let _158_1484 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_158_1484)::[])
in ("Valid", _158_1485))
in (FStar_SMTEncoding_Term.mkApp _158_1486))
in (let _158_1500 = (let _158_1499 = (let _158_1498 = (let _158_1497 = (let _158_1496 = (let _158_1495 = (let _158_1494 = (let _158_1493 = (let _158_1492 = (let _158_1488 = (let _158_1487 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_158_1487)::[])
in (_158_1488)::[])
in (let _158_1491 = (let _158_1490 = (let _158_1489 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_158_1489, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _158_1490))
in (_158_1492, (xx)::[], _158_1491)))
in (FStar_SMTEncoding_Term.mkForall _158_1493))
in (_158_1494, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1495))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1496))
in (FStar_SMTEncoding_Term.mkForall _158_1497))
in (_158_1498, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1499))
in (_158_1500)::[]))))))))))
in (
# 1161 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun env for_some tt -> (
# 1162 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1163 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1164 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1165 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1166 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1167 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1168 "FStar.SMTEncoding.Encode.fst"
let valid = (let _158_1509 = (let _158_1508 = (let _158_1507 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_158_1507)::[])
in ("Valid", _158_1508))
in (FStar_SMTEncoding_Term.mkApp _158_1509))
in (
# 1169 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _158_1512 = (let _158_1511 = (let _158_1510 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_158_1510)::[])
in ("Valid", _158_1511))
in (FStar_SMTEncoding_Term.mkApp _158_1512))
in (let _158_1526 = (let _158_1525 = (let _158_1524 = (let _158_1523 = (let _158_1522 = (let _158_1521 = (let _158_1520 = (let _158_1519 = (let _158_1518 = (let _158_1514 = (let _158_1513 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_158_1513)::[])
in (_158_1514)::[])
in (let _158_1517 = (let _158_1516 = (let _158_1515 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_158_1515, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _158_1516))
in (_158_1518, (xx)::[], _158_1517)))
in (FStar_SMTEncoding_Term.mkExists _158_1519))
in (_158_1520, valid))
in (FStar_SMTEncoding_Term.mkIff _158_1521))
in (((valid)::[])::[], (aa)::(bb)::[], _158_1522))
in (FStar_SMTEncoding_Term.mkForall _158_1523))
in (_158_1524, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_158_1525))
in (_158_1526)::[]))))))))))
in (
# 1171 "FStar.SMTEncoding.Encode.fst"
let mk_range_of_interp = (fun env range_of tt -> (
# 1172 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1173 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1174 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1175 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1176 "FStar.SMTEncoding.Encode.fst"
let range_of_ty = (FStar_SMTEncoding_Term.mkApp (range_of, (a)::(b)::[]))
in (let _158_1537 = (let _158_1536 = (let _158_1535 = (let _158_1534 = (let _158_1533 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_of_ty)
in (((range_of_ty)::[])::[], (aa)::(bb)::[], _158_1533))
in (FStar_SMTEncoding_Term.mkForall _158_1534))
in (_158_1535, Some ("Range_const typing")))
in FStar_SMTEncoding_Term.Assume (_158_1536))
in (_158_1537)::[])))))))
in (
# 1183 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_of_lid, mk_range_of_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _76_1893 -> (match (_76_1893) with
| (l, _76_1892) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_76_1896, f) -> begin
(f env s tt)
end))))))))))))))))))))))

# 1206 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1207 "FStar.SMTEncoding.Encode.fst"
let _76_1902 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _158_1749 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _158_1749))
end else begin
()
end
in (
# 1210 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1213 "FStar.SMTEncoding.Encode.fst"
let _76_1910 = (encode_sigelt' env se)
in (match (_76_1910) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _158_1752 = (let _158_1751 = (let _158_1750 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_158_1750))
in (_158_1751)::[])
in (_158_1752, e))
end
| _76_1913 -> begin
(let _158_1759 = (let _158_1758 = (let _158_1754 = (let _158_1753 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_158_1753))
in (_158_1754)::g)
in (let _158_1757 = (let _158_1756 = (let _158_1755 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_158_1755))
in (_158_1756)::[])
in (FStar_List.append _158_1758 _158_1757)))
in (_158_1759, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1219 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1225 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1226 "FStar.SMTEncoding.Encode.fst"
let tt = (norm env t)
in (
# 1232 "FStar.SMTEncoding.Encode.fst"
let _76_1926 = (encode_free_var env lid t tt quals)
in (match (_76_1926) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _158_1773 = (let _158_1772 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _158_1772))
in (_158_1773, env))
end else begin
(decls, env)
end
end))))
in (
# 1238 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _76_1933 lb -> (match (_76_1933) with
| (decls, env) -> begin
(
# 1240 "FStar.SMTEncoding.Encode.fst"
let _76_1937 = (let _158_1782 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _158_1782 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_76_1937) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _76_1955, _76_1957, _76_1959, _76_1961) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1252 "FStar.SMTEncoding.Encode.fst"
let _76_1967 = (new_term_constant_and_tok_from_lid env lid)
in (match (_76_1967) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _76_1970, t, quals, _76_1974) -> begin
(
# 1256 "FStar.SMTEncoding.Encode.fst"
let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_12 -> (match (_76_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _76_1987 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(
# 1261 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (
# 1262 "FStar.SMTEncoding.Encode.fst"
let _76_1992 = (encode_top_level_val env fv t quals)
in (match (_76_1992) with
| (decls, env) -> begin
(
# 1263 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1264 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _158_1785 = (let _158_1784 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _158_1784))
in (_158_1785, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _76_1998, _76_2000) -> begin
(
# 1270 "FStar.SMTEncoding.Encode.fst"
let _76_2005 = (encode_formula f env)
in (match (_76_2005) with
| (f, decls) -> begin
(
# 1271 "FStar.SMTEncoding.Encode.fst"
let g = (let _158_1790 = (let _158_1789 = (let _158_1788 = (let _158_1787 = (let _158_1786 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _158_1786))
in Some (_158_1787))
in (f, _158_1788))
in FStar_SMTEncoding_Term.Assume (_158_1789))
in (_158_1790)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _76_2010, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_76_2015, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _76_2023; FStar_Syntax_Syntax.lbtyp = _76_2021; FStar_Syntax_Syntax.lbeff = _76_2019; FStar_Syntax_Syntax.lbdef = _76_2017}::[]), _76_2030, _76_2032, _76_2034) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1278 "FStar.SMTEncoding.Encode.fst"
let _76_2040 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_76_2040) with
| (tname, ttok, env) -> begin
(
# 1279 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1280 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1281 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _158_1793 = (let _158_1792 = (let _158_1791 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_158_1791)::[])
in ("Valid", _158_1792))
in (FStar_SMTEncoding_Term.mkApp _158_1793))
in (
# 1282 "FStar.SMTEncoding.Encode.fst"
let decls = (let _158_1801 = (let _158_1800 = (let _158_1799 = (let _158_1798 = (let _158_1797 = (let _158_1796 = (let _158_1795 = (let _158_1794 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _158_1794))
in (FStar_SMTEncoding_Term.mkEq _158_1795))
in (((valid_b2t_x)::[])::[], (xx)::[], _158_1796))
in (FStar_SMTEncoding_Term.mkForall _158_1797))
in (_158_1798, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_158_1799))
in (_158_1800)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_158_1801)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_76_2046, _76_2048, _76_2050, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_13 -> (match (_76_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _76_2060 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _76_2066, _76_2068, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_14 -> (match (_76_14) with
| FStar_Syntax_Syntax.Projector (_76_2074) -> begin
true
end
| _76_2077 -> begin
false
end)))) -> begin
(
# 1296 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1297 "FStar.SMTEncoding.Encode.fst"
let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_76_2081) -> begin
([], env)
end
| None -> begin
(
# 1302 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _76_2089, _76_2091, quals) -> begin
(
# 1308 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1309 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1310 "FStar.SMTEncoding.Encode.fst"
let _76_2103 = (FStar_Util.first_N nbinders formals)
in (match (_76_2103) with
| (formals, extra_formals) -> begin
(
# 1311 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _76_2107 _76_2111 -> (match ((_76_2107, _76_2111)) with
| ((formal, _76_2106), (binder, _76_2110)) -> begin
(let _158_1815 = (let _158_1814 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _158_1814))
in FStar_Syntax_Syntax.NT (_158_1815))
end)) formals binders)
in (
# 1312 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _158_1819 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _76_2115 -> (match (_76_2115) with
| (x, i) -> begin
(let _158_1818 = (
# 1312 "FStar.SMTEncoding.Encode.fst"
let _76_2116 = x
in (let _158_1817 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _76_2116.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _76_2116.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _158_1817}))
in (_158_1818, i))
end))))
in (FStar_All.pipe_right _158_1819 FStar_Syntax_Util.name_binders))
in (
# 1313 "FStar.SMTEncoding.Encode.fst"
let body = (let _158_1826 = (FStar_Syntax_Subst.compress body)
in (let _158_1825 = (let _158_1820 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _158_1820))
in (let _158_1824 = (let _158_1823 = (let _158_1822 = (FStar_Syntax_Subst.subst subst t)
in _158_1822.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _158_1821 -> Some (_158_1821)) _158_1823))
in (FStar_Syntax_Syntax.extend_app_n _158_1826 _158_1825 _158_1824 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1316 "FStar.SMTEncoding.Encode.fst"
let rec destruct_bound_function = (fun flid t_norm e -> (match ((let _158_1833 = (FStar_Syntax_Util.unascribe e)
in _158_1833.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1319 "FStar.SMTEncoding.Encode.fst"
let _76_2132 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_76_2132) with
| (binders, body, opening) -> begin
(match ((let _158_1834 = (FStar_Syntax_Subst.compress t_norm)
in _158_1834.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1322 "FStar.SMTEncoding.Encode.fst"
let _76_2139 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_76_2139) with
| (formals, c) -> begin
(
# 1323 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1324 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1325 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1327 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1328 "FStar.SMTEncoding.Encode.fst"
let _76_2146 = (FStar_Util.first_N nformals binders)
in (match (_76_2146) with
| (bs0, rest) -> begin
(
# 1329 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1330 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _76_2150 _76_2154 -> (match ((_76_2150, _76_2154)) with
| ((b, _76_2149), (x, _76_2153)) -> begin
(let _158_1838 = (let _158_1837 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _158_1837))
in FStar_Syntax_Syntax.NT (_158_1838))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1332 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1335 "FStar.SMTEncoding.Encode.fst"
let _76_2160 = (eta_expand binders formals body tres)
in (match (_76_2160) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| _76_2162 -> begin
(let _158_1841 = (let _158_1840 = (FStar_Syntax_Print.term_to_string e)
in (let _158_1839 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _158_1840 _158_1839)))
in (FStar_All.failwith _158_1841))
end)
end))
end
| _76_2164 -> begin
(match ((let _158_1842 = (FStar_Syntax_Subst.compress t_norm)
in _158_1842.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1345 "FStar.SMTEncoding.Encode.fst"
let _76_2171 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_76_2171) with
| (formals, c) -> begin
(
# 1346 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1347 "FStar.SMTEncoding.Encode.fst"
let _76_2175 = (eta_expand [] formals e tres)
in (match (_76_2175) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _76_2177 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _76_2179 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1355 "FStar.SMTEncoding.Encode.fst"
let _76_2205 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _76_2192 lb -> (match (_76_2192) with
| (toks, typs, decls, env) -> begin
(
# 1357 "FStar.SMTEncoding.Encode.fst"
let _76_2194 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1358 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1359 "FStar.SMTEncoding.Encode.fst"
let _76_2200 = (let _158_1847 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _158_1847 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_76_2200) with
| (tok, decl, env) -> begin
(let _158_1850 = (let _158_1849 = (let _158_1848 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_158_1848, tok))
in (_158_1849)::toks)
in (_158_1850, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_76_2205) with
| (toks, typs, decls, env) -> begin
(
# 1361 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1362 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1363 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_15 -> (match (_76_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _76_2212 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _158_1853 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _158_1853)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _76_2222; FStar_Syntax_Syntax.lbunivs = _76_2220; FStar_Syntax_Syntax.lbtyp = _76_2218; FStar_Syntax_Syntax.lbeff = _76_2216; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid_fv, (f, ftok))::[]) -> begin
(
# 1370 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1371 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1372 "FStar.SMTEncoding.Encode.fst"
let _76_2242 = (destruct_bound_function flid t_norm e)
in (match (_76_2242) with
| (binders, body, _76_2239, _76_2241) -> begin
(
# 1373 "FStar.SMTEncoding.Encode.fst"
let _76_2249 = (encode_binders None binders env)
in (match (_76_2249) with
| (vars, guards, env', binder_decls, _76_2248) -> begin
(
# 1374 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _76_2252 -> begin
(let _158_1855 = (let _158_1854 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _158_1854))
in (FStar_SMTEncoding_Term.mkApp _158_1855))
end)
in (
# 1375 "FStar.SMTEncoding.Encode.fst"
let _76_2258 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _158_1857 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _158_1856 = (encode_formula body env')
in (_158_1857, _158_1856)))
end else begin
(let _158_1858 = (encode_term body env')
in (app, _158_1858))
end
in (match (_76_2258) with
| (app, (body, decls2)) -> begin
(
# 1379 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _158_1867 = (let _158_1866 = (let _158_1863 = (let _158_1862 = (let _158_1861 = (let _158_1860 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _158_1859 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_158_1860, _158_1859)))
in (FStar_SMTEncoding_Term.mkImp _158_1861))
in (((app)::[])::[], vars, _158_1862))
in (FStar_SMTEncoding_Term.mkForall _158_1863))
in (let _158_1865 = (let _158_1864 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_158_1864))
in (_158_1866, _158_1865)))
in FStar_SMTEncoding_Term.Assume (_158_1867))
in (let _158_1869 = (let _158_1868 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _158_1868))
in (_158_1869, env)))
end)))
end))
end))))
end
| _76_2261 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1385 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _158_1870 = (varops.fresh "fuel")
in (_158_1870, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1386 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1387 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1388 "FStar.SMTEncoding.Encode.fst"
let _76_2279 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _76_2267 _76_2272 -> (match ((_76_2267, _76_2272)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(
# 1389 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1390 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1391 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1392 "FStar.SMTEncoding.Encode.fst"
let env = (let _158_1875 = (let _158_1874 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _158_1873 -> Some (_158_1873)) _158_1874))
in (push_free_var env flid gtok _158_1875))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_76_2279) with
| (gtoks, env) -> begin
(
# 1394 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1395 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _76_2288 t_norm _76_2299 -> (match ((_76_2288, _76_2299)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _76_2298; FStar_Syntax_Syntax.lbunivs = _76_2296; FStar_Syntax_Syntax.lbtyp = _76_2294; FStar_Syntax_Syntax.lbeff = _76_2292; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1396 "FStar.SMTEncoding.Encode.fst"
let _76_2304 = (destruct_bound_function flid t_norm e)
in (match (_76_2304) with
| (binders, body, formals, tres) -> begin
(
# 1397 "FStar.SMTEncoding.Encode.fst"
let _76_2311 = (encode_binders None binders env)
in (match (_76_2311) with
| (vars, guards, env', binder_decls, _76_2310) -> begin
(
# 1398 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _158_1886 = (let _158_1885 = (let _158_1884 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_158_1884)
in (g, _158_1885, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_158_1886))
in (
# 1399 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1400 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1401 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1402 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1403 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _158_1889 = (let _158_1888 = (let _158_1887 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_158_1887)::vars_tm)
in (g, _158_1888))
in (FStar_SMTEncoding_Term.mkApp _158_1889))
in (
# 1404 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _158_1892 = (let _158_1891 = (let _158_1890 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_158_1890)::vars_tm)
in (g, _158_1891))
in (FStar_SMTEncoding_Term.mkApp _158_1892))
in (
# 1405 "FStar.SMTEncoding.Encode.fst"
let _76_2321 = (encode_term body env')
in (match (_76_2321) with
| (body_tm, decls2) -> begin
(
# 1406 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _158_1901 = (let _158_1900 = (let _158_1897 = (let _158_1896 = (let _158_1895 = (let _158_1894 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _158_1893 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_158_1894, _158_1893)))
in (FStar_SMTEncoding_Term.mkImp _158_1895))
in (((gsapp)::[])::[], (fuel)::vars, _158_1896))
in (FStar_SMTEncoding_Term.mkForall _158_1897))
in (let _158_1899 = (let _158_1898 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_158_1898))
in (_158_1900, _158_1899)))
in FStar_SMTEncoding_Term.Assume (_158_1901))
in (
# 1408 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _158_1905 = (let _158_1904 = (let _158_1903 = (let _158_1902 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _158_1902))
in (FStar_SMTEncoding_Term.mkForall _158_1903))
in (_158_1904, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_158_1905))
in (
# 1410 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _158_1914 = (let _158_1913 = (let _158_1912 = (let _158_1911 = (let _158_1910 = (let _158_1909 = (let _158_1908 = (let _158_1907 = (let _158_1906 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_158_1906)::vars_tm)
in (g, _158_1907))
in (FStar_SMTEncoding_Term.mkApp _158_1908))
in (gsapp, _158_1909))
in (FStar_SMTEncoding_Term.mkEq _158_1910))
in (((gsapp)::[])::[], (fuel)::vars, _158_1911))
in (FStar_SMTEncoding_Term.mkForall _158_1912))
in (_158_1913, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_158_1914))
in (
# 1412 "FStar.SMTEncoding.Encode.fst"
let _76_2344 = (
# 1413 "FStar.SMTEncoding.Encode.fst"
let _76_2331 = (encode_binders None formals env0)
in (match (_76_2331) with
| (vars, v_guards, env, binder_decls, _76_2330) -> begin
(
# 1414 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1415 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1416 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1417 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _158_1915 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _158_1915 ((fuel)::vars)))
in (let _158_1919 = (let _158_1918 = (let _158_1917 = (let _158_1916 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _158_1916))
in (FStar_SMTEncoding_Term.mkForall _158_1917))
in (_158_1918, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_158_1919)))
in (
# 1420 "FStar.SMTEncoding.Encode.fst"
let _76_2341 = (
# 1421 "FStar.SMTEncoding.Encode.fst"
let _76_2338 = (encode_term_pred None tres env gapp)
in (match (_76_2338) with
| (g_typing, d3) -> begin
(let _158_1927 = (let _158_1926 = (let _158_1925 = (let _158_1924 = (let _158_1923 = (let _158_1922 = (let _158_1921 = (let _158_1920 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_158_1920, g_typing))
in (FStar_SMTEncoding_Term.mkImp _158_1921))
in (((gapp)::[])::[], (fuel)::vars, _158_1922))
in (FStar_SMTEncoding_Term.mkForall _158_1923))
in (_158_1924, None))
in FStar_SMTEncoding_Term.Assume (_158_1925))
in (_158_1926)::[])
in (d3, _158_1927))
end))
in (match (_76_2341) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_76_2344) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1425 "FStar.SMTEncoding.Encode.fst"
let _76_2360 = (let _158_1930 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _76_2348 _76_2352 -> (match ((_76_2348, _76_2352)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1426 "FStar.SMTEncoding.Encode.fst"
let _76_2356 = (encode_one_binding env0 gtok ty bs)
in (match (_76_2356) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _158_1930))
in (match (_76_2360) with
| (decls, eqns, env0) -> begin
(
# 1428 "FStar.SMTEncoding.Encode.fst"
let _76_2369 = (let _158_1932 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _158_1932 (FStar_List.partition (fun _76_16 -> (match (_76_16) with
| FStar_SMTEncoding_Term.DeclFun (_76_2363) -> begin
true
end
| _76_2366 -> begin
false
end)))))
in (match (_76_2369) with
| (prefix_decls, rest) -> begin
(
# 1431 "FStar.SMTEncoding.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _76_2178 -> (match (_76_2178) with
| Let_rec_unencodeable -> begin
(
# 1434 "FStar.SMTEncoding.Encode.fst"
let msg = (let _158_1935 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _158_1935 (FStar_String.concat " and ")))
in (
# 1435 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _76_2373, _76_2375, _76_2377) -> begin
(
# 1440 "FStar.SMTEncoding.Encode.fst"
let _76_2382 = (encode_signature env ses)
in (match (_76_2382) with
| (g, env) -> begin
(
# 1441 "FStar.SMTEncoding.Encode.fst"
let _76_2394 = (FStar_All.pipe_right g (FStar_List.partition (fun _76_17 -> (match (_76_17) with
| FStar_SMTEncoding_Term.Assume (_76_2385, Some ("inversion axiom")) -> begin
false
end
| _76_2391 -> begin
true
end))))
in (match (_76_2394) with
| (g', inversions) -> begin
(
# 1444 "FStar.SMTEncoding.Encode.fst"
let _76_2403 = (FStar_All.pipe_right g' (FStar_List.partition (fun _76_18 -> (match (_76_18) with
| FStar_SMTEncoding_Term.DeclFun (_76_2397) -> begin
true
end
| _76_2400 -> begin
false
end))))
in (match (_76_2403) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _76_2406, tps, k, _76_2410, datas, quals, _76_2414) -> begin
(
# 1450 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _76_19 -> (match (_76_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _76_2421 -> begin
false
end))))
in (
# 1451 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1453 "FStar.SMTEncoding.Encode.fst"
let _76_2433 = c
in (match (_76_2433) with
| (name, args, _76_2428, _76_2430, _76_2432) -> begin
(let _158_1943 = (let _158_1942 = (let _158_1941 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _158_1941, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_158_1942))
in (_158_1943)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1457 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _158_1949 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _158_1949 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1461 "FStar.SMTEncoding.Encode.fst"
let _76_2440 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_76_2440) with
| (xxsym, xx) -> begin
(
# 1462 "FStar.SMTEncoding.Encode.fst"
let _76_2476 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _76_2443 l -> (match (_76_2443) with
| (out, decls) -> begin
(
# 1463 "FStar.SMTEncoding.Encode.fst"
let _76_2448 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_76_2448) with
| (_76_2446, data_t) -> begin
(
# 1464 "FStar.SMTEncoding.Encode.fst"
let _76_2451 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_76_2451) with
| (args, res) -> begin
(
# 1465 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _158_1952 = (FStar_Syntax_Subst.compress res)
in _158_1952.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_76_2453, indices) -> begin
indices
end
| _76_2458 -> begin
[]
end)
in (
# 1468 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _76_2464 -> (match (_76_2464) with
| (x, _76_2463) -> begin
(let _158_1957 = (let _158_1956 = (let _158_1955 = (mk_term_projector_name l x)
in (_158_1955, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _158_1956))
in (push_term_var env x _158_1957))
end)) env))
in (
# 1471 "FStar.SMTEncoding.Encode.fst"
let _76_2468 = (encode_args indices env)
in (match (_76_2468) with
| (indices, decls') -> begin
(
# 1472 "FStar.SMTEncoding.Encode.fst"
let _76_2469 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1474 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _158_1962 = (FStar_List.map2 (fun v a -> (let _158_1961 = (let _158_1960 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_158_1960, a))
in (FStar_SMTEncoding_Term.mkEq _158_1961))) vars indices)
in (FStar_All.pipe_right _158_1962 FStar_SMTEncoding_Term.mk_and_l))
in (let _158_1967 = (let _158_1966 = (let _158_1965 = (let _158_1964 = (let _158_1963 = (mk_data_tester env l xx)
in (_158_1963, eqs))
in (FStar_SMTEncoding_Term.mkAnd _158_1964))
in (out, _158_1965))
in (FStar_SMTEncoding_Term.mkOr _158_1966))
in (_158_1967, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_76_2476) with
| (data_ax, decls) -> begin
(
# 1476 "FStar.SMTEncoding.Encode.fst"
let _76_2479 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_2479) with
| (ffsym, ff) -> begin
(
# 1477 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _158_1968 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _158_1968 xx tapp))
in (let _158_1975 = (let _158_1974 = (let _158_1973 = (let _158_1972 = (let _158_1971 = (let _158_1970 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _158_1969 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _158_1970, _158_1969)))
in (FStar_SMTEncoding_Term.mkForall _158_1971))
in (_158_1972, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_158_1973))
in (_158_1974)::[])
in (FStar_List.append decls _158_1975)))
end))
end))
end))
end)
in (
# 1481 "FStar.SMTEncoding.Encode.fst"
let _76_2489 = (match ((let _158_1976 = (FStar_Syntax_Subst.compress k)
in _158_1976.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _76_2486 -> begin
(tps, k)
end)
in (match (_76_2489) with
| (formals, res) -> begin
(
# 1487 "FStar.SMTEncoding.Encode.fst"
let _76_2492 = (FStar_Syntax_Subst.open_term formals res)
in (match (_76_2492) with
| (formals, res) -> begin
(
# 1488 "FStar.SMTEncoding.Encode.fst"
let _76_2499 = (encode_binders None formals env)
in (match (_76_2499) with
| (vars, guards, env', binder_decls, _76_2498) -> begin
(
# 1490 "FStar.SMTEncoding.Encode.fst"
let _76_2503 = (new_term_constant_and_tok_from_lid env t)
in (match (_76_2503) with
| (tname, ttok, env) -> begin
(
# 1491 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1492 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1493 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _158_1978 = (let _158_1977 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _158_1977))
in (FStar_SMTEncoding_Term.mkApp _158_1978))
in (
# 1494 "FStar.SMTEncoding.Encode.fst"
let _76_2524 = (
# 1495 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _158_1982 = (let _158_1981 = (FStar_All.pipe_right vars (FStar_List.map (fun _76_2509 -> (match (_76_2509) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _158_1980 = (varops.next_id ())
in (tname, _158_1981, FStar_SMTEncoding_Term.Term_sort, _158_1980, false)))
in (constructor_or_logic_type_decl _158_1982))
in (
# 1496 "FStar.SMTEncoding.Encode.fst"
let _76_2521 = (match (vars) with
| [] -> begin
(let _158_1986 = (let _158_1985 = (let _158_1984 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _158_1983 -> Some (_158_1983)) _158_1984))
in (push_free_var env t tname _158_1985))
in ([], _158_1986))
end
| _76_2513 -> begin
(
# 1499 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1500 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _158_1987 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _158_1987))
in (
# 1501 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1502 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1505 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _158_1991 = (let _158_1990 = (let _158_1989 = (let _158_1988 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _158_1988))
in (FStar_SMTEncoding_Term.mkForall' _158_1989))
in (_158_1990, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_158_1991))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_76_2521) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_76_2524) with
| (decls, env) -> begin
(
# 1508 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1509 "FStar.SMTEncoding.Encode.fst"
let _76_2527 = (encode_term_pred None res env' tapp)
in (match (_76_2527) with
| (k, decls) -> begin
(
# 1510 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _158_1995 = (let _158_1994 = (let _158_1993 = (let _158_1992 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _158_1992))
in (_158_1993, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_158_1994))
in (_158_1995)::[])
end else begin
[]
end
in (let _158_2001 = (let _158_2000 = (let _158_1999 = (let _158_1998 = (let _158_1997 = (let _158_1996 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _158_1996))
in (FStar_SMTEncoding_Term.mkForall _158_1997))
in (_158_1998, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_158_1999))
in (_158_2000)::[])
in (FStar_List.append (FStar_List.append decls karr) _158_2001)))
end))
in (
# 1515 "FStar.SMTEncoding.Encode.fst"
let aux = (let _158_2005 = (let _158_2002 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _158_2002))
in (let _158_2004 = (let _158_2003 = (pretype_axiom tapp vars)
in (_158_2003)::[])
in (FStar_List.append _158_2005 _158_2004)))
in (
# 1520 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _76_2534, _76_2536, _76_2538, _76_2540, _76_2542, _76_2544, _76_2546) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _76_2551, t, _76_2554, n_tps, quals, _76_2558, drange) -> begin
(
# 1528 "FStar.SMTEncoding.Encode.fst"
let _76_2565 = (new_term_constant_and_tok_from_lid env d)
in (match (_76_2565) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1529 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1530 "FStar.SMTEncoding.Encode.fst"
let _76_2569 = (FStar_Syntax_Util.arrow_formals t)
in (match (_76_2569) with
| (formals, t_res) -> begin
(
# 1531 "FStar.SMTEncoding.Encode.fst"
let _76_2572 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_76_2572) with
| (fuel_var, fuel_tm) -> begin
(
# 1532 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1533 "FStar.SMTEncoding.Encode.fst"
let _76_2579 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_76_2579) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1534 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _158_2007 = (mk_term_projector_name d x)
in (_158_2007, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1535 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _158_2009 = (let _158_2008 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _158_2008, true))
in (FStar_All.pipe_right _158_2009 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1536 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1537 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1538 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1539 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1541 "FStar.SMTEncoding.Encode.fst"
let _76_2589 = (encode_term_pred None t env ddtok_tm)
in (match (_76_2589) with
| (tok_typing, decls3) -> begin
(
# 1543 "FStar.SMTEncoding.Encode.fst"
let _76_2596 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_76_2596) with
| (vars', guards', env'', decls_formals, _76_2595) -> begin
(
# 1544 "FStar.SMTEncoding.Encode.fst"
let _76_2601 = (
# 1545 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1546 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_76_2601) with
| (ty_pred', decls_pred) -> begin
(
# 1548 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1549 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _76_2605 -> begin
(let _158_2011 = (let _158_2010 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _158_2010))
in (_158_2011)::[])
end)
in (
# 1553 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _76_2608 -> (match (()) with
| () -> begin
(
# 1554 "FStar.SMTEncoding.Encode.fst"
let _76_2611 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_76_2611) with
| (head, args) -> begin
(match ((let _158_2014 = (FStar_Syntax_Subst.compress head)
in _158_2014.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(
# 1558 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (
# 1559 "FStar.SMTEncoding.Encode.fst"
let _76_2629 = (encode_args args env')
in (match (_76_2629) with
| (encoded_args, arg_decls) -> begin
(
# 1560 "FStar.SMTEncoding.Encode.fst"
let _76_2644 = (FStar_List.fold_left (fun _76_2633 arg -> (match (_76_2633) with
| (env, arg_vars, eqns) -> begin
(
# 1561 "FStar.SMTEncoding.Encode.fst"
let _76_2639 = (let _158_2017 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _158_2017))
in (match (_76_2639) with
| (_76_2636, xv, env) -> begin
(let _158_2019 = (let _158_2018 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_158_2018)::eqns)
in (env, (xv)::arg_vars, _158_2019))
end))
end)) (env', [], []) encoded_args)
in (match (_76_2644) with
| (_76_2641, arg_vars, eqns) -> begin
(
# 1563 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1564 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1565 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1566 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1567 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1568 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1569 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _158_2026 = (let _158_2025 = (let _158_2024 = (let _158_2023 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _158_2022 = (let _158_2021 = (let _158_2020 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _158_2020))
in (FStar_SMTEncoding_Term.mkImp _158_2021))
in (((ty_pred)::[])::[], _158_2023, _158_2022)))
in (FStar_SMTEncoding_Term.mkForall _158_2024))
in (_158_2025, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_158_2026))
in (
# 1574 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1576 "FStar.SMTEncoding.Encode.fst"
let x = (let _158_2027 = (varops.fresh "x")
in (_158_2027, FStar_SMTEncoding_Term.Term_sort))
in (
# 1577 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _158_2037 = (let _158_2036 = (let _158_2035 = (let _158_2034 = (let _158_2029 = (let _158_2028 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_158_2028)::[])
in (_158_2029)::[])
in (let _158_2033 = (let _158_2032 = (let _158_2031 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _158_2030 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_158_2031, _158_2030)))
in (FStar_SMTEncoding_Term.mkImp _158_2032))
in (_158_2034, (x)::[], _158_2033)))
in (FStar_SMTEncoding_Term.mkForall _158_2035))
in (_158_2036, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_158_2037))))
end else begin
(
# 1580 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _158_2040 = (let _158_2039 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _158_2039 dapp))
in (_158_2040)::[])
end
| _76_2658 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _158_2047 = (let _158_2046 = (let _158_2045 = (let _158_2044 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _158_2043 = (let _158_2042 = (let _158_2041 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _158_2041))
in (FStar_SMTEncoding_Term.mkImp _158_2042))
in (((ty_pred)::[])::[], _158_2044, _158_2043)))
in (FStar_SMTEncoding_Term.mkForall _158_2045))
in (_158_2046, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_158_2047)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _76_2662 -> begin
(
# 1588 "FStar.SMTEncoding.Encode.fst"
let _76_2663 = (let _158_2050 = (let _158_2049 = (FStar_Syntax_Print.lid_to_string d)
in (let _158_2048 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _158_2049 _158_2048)))
in (FStar_TypeChecker_Errors.warn drange _158_2050))
in ([], []))
end)
end))
end))
in (
# 1591 "FStar.SMTEncoding.Encode.fst"
let _76_2667 = (encode_elim ())
in (match (_76_2667) with
| (decls2, elim) -> begin
(
# 1592 "FStar.SMTEncoding.Encode.fst"
let g = (let _158_2075 = (let _158_2074 = (let _158_2059 = (let _158_2058 = (let _158_2057 = (let _158_2056 = (let _158_2055 = (let _158_2054 = (let _158_2053 = (let _158_2052 = (let _158_2051 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _158_2051))
in Some (_158_2052))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _158_2053))
in FStar_SMTEncoding_Term.DeclFun (_158_2054))
in (_158_2055)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _158_2056))
in (FStar_List.append _158_2057 proxy_fresh))
in (FStar_List.append _158_2058 decls_formals))
in (FStar_List.append _158_2059 decls_pred))
in (let _158_2073 = (let _158_2072 = (let _158_2071 = (let _158_2063 = (let _158_2062 = (let _158_2061 = (let _158_2060 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _158_2060))
in (FStar_SMTEncoding_Term.mkForall _158_2061))
in (_158_2062, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_158_2063))
in (let _158_2070 = (let _158_2069 = (let _158_2068 = (let _158_2067 = (let _158_2066 = (let _158_2065 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _158_2064 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _158_2065, _158_2064)))
in (FStar_SMTEncoding_Term.mkForall _158_2066))
in (_158_2067, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_158_2068))
in (_158_2069)::[])
in (_158_2071)::_158_2070))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_158_2072)
in (FStar_List.append _158_2074 _158_2073)))
in (FStar_List.append _158_2075 elim))
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
# 1610 "FStar.SMTEncoding.Encode.fst"
let _76_2676 = (encode_free_var env x t t_norm [])
in (match (_76_2676) with
| (decls, env) -> begin
(
# 1611 "FStar.SMTEncoding.Encode.fst"
let _76_2681 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_76_2681) with
| (n, x', _76_2680) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _76_2685) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (
# 1617 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1618 "FStar.SMTEncoding.Encode.fst"
let _76_2694 = (encode_function_type_as_formula None None t env)
in (match (_76_2694) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (
# 1622 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _158_2088 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _158_2088)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1625 "FStar.SMTEncoding.Encode.fst"
let _76_2704 = (new_term_constant_and_tok_from_lid env lid)
in (match (_76_2704) with
| (vname, vtok, env) -> begin
(
# 1626 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _158_2089 = (FStar_Syntax_Subst.compress t_norm)
in _158_2089.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _76_2707) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _76_2710 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _76_2713 -> begin
[]
end)
in (
# 1629 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1630 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1633 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1634 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1635 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1637 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1638 "FStar.SMTEncoding.Encode.fst"
let _76_2728 = (
# 1639 "FStar.SMTEncoding.Encode.fst"
let _76_2723 = (curried_arrow_formals_comp t_norm)
in (match (_76_2723) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _158_2091 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _158_2091))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_76_2728) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1643 "FStar.SMTEncoding.Encode.fst"
let _76_2732 = (new_term_constant_and_tok_from_lid env lid)
in (match (_76_2732) with
| (vname, vtok, env) -> begin
(
# 1644 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _76_2735 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1647 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _76_20 -> (match (_76_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1649 "FStar.SMTEncoding.Encode.fst"
let _76_2751 = (FStar_Util.prefix vars)
in (match (_76_2751) with
| (_76_2746, (xxsym, _76_2749)) -> begin
(
# 1650 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _158_2108 = (let _158_2107 = (let _158_2106 = (let _158_2105 = (let _158_2104 = (let _158_2103 = (let _158_2102 = (let _158_2101 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _158_2101))
in (vapp, _158_2102))
in (FStar_SMTEncoding_Term.mkEq _158_2103))
in (((vapp)::[])::[], vars, _158_2104))
in (FStar_SMTEncoding_Term.mkForall _158_2105))
in (_158_2106, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_158_2107))
in (_158_2108)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1655 "FStar.SMTEncoding.Encode.fst"
let _76_2763 = (FStar_Util.prefix vars)
in (match (_76_2763) with
| (_76_2758, (xxsym, _76_2761)) -> begin
(
# 1656 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1657 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1658 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _158_2110 = (let _158_2109 = (mk_term_projector_name d f)
in (_158_2109, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _158_2110))
in (let _158_2115 = (let _158_2114 = (let _158_2113 = (let _158_2112 = (let _158_2111 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _158_2111))
in (FStar_SMTEncoding_Term.mkForall _158_2112))
in (_158_2113, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_158_2114))
in (_158_2115)::[]))))
end))
end
| _76_2768 -> begin
[]
end)))))
in (
# 1662 "FStar.SMTEncoding.Encode.fst"
let _76_2775 = (encode_binders None formals env)
in (match (_76_2775) with
| (vars, guards, env', decls1, _76_2774) -> begin
(
# 1663 "FStar.SMTEncoding.Encode.fst"
let _76_2784 = (match (pre_opt) with
| None -> begin
(let _158_2116 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_158_2116, decls1))
end
| Some (p) -> begin
(
# 1665 "FStar.SMTEncoding.Encode.fst"
let _76_2781 = (encode_formula p env')
in (match (_76_2781) with
| (g, ds) -> begin
(let _158_2117 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_158_2117, (FStar_List.append decls1 ds)))
end))
end)
in (match (_76_2784) with
| (guard, decls1) -> begin
(
# 1666 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1668 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _158_2119 = (let _158_2118 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _158_2118))
in (FStar_SMTEncoding_Term.mkApp _158_2119))
in (
# 1669 "FStar.SMTEncoding.Encode.fst"
let _76_2808 = (
# 1670 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _158_2122 = (let _158_2121 = (FStar_All.pipe_right formals (FStar_List.map (fun _76_2787 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _158_2121, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_158_2122))
in (
# 1671 "FStar.SMTEncoding.Encode.fst"
let _76_2795 = (
# 1672 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1672 "FStar.SMTEncoding.Encode.fst"
let _76_2790 = env
in {bindings = _76_2790.bindings; depth = _76_2790.depth; tcenv = _76_2790.tcenv; warn = _76_2790.warn; cache = _76_2790.cache; nolabels = _76_2790.nolabels; use_zfuel_name = _76_2790.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_76_2795) with
| (tok_typing, decls2) -> begin
(
# 1676 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1677 "FStar.SMTEncoding.Encode.fst"
let _76_2805 = (match (formals) with
| [] -> begin
(let _158_2126 = (let _158_2125 = (let _158_2124 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _158_2123 -> Some (_158_2123)) _158_2124))
in (push_free_var env lid vname _158_2125))
in ((FStar_List.append decls2 ((tok_typing)::[])), _158_2126))
end
| _76_2799 -> begin
(
# 1680 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1681 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _158_2127 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _158_2127))
in (
# 1682 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _158_2131 = (let _158_2130 = (let _158_2129 = (let _158_2128 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _158_2128))
in (FStar_SMTEncoding_Term.mkForall _158_2129))
in (_158_2130, None))
in FStar_SMTEncoding_Term.Assume (_158_2131))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_76_2805) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_76_2808) with
| (decls2, env) -> begin
(
# 1685 "FStar.SMTEncoding.Encode.fst"
let _76_2816 = (
# 1686 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1687 "FStar.SMTEncoding.Encode.fst"
let _76_2812 = (encode_term res_t env')
in (match (_76_2812) with
| (encoded_res_t, decls) -> begin
(let _158_2132 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _158_2132, decls))
end)))
in (match (_76_2816) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1689 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _158_2136 = (let _158_2135 = (let _158_2134 = (let _158_2133 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _158_2133))
in (FStar_SMTEncoding_Term.mkForall _158_2134))
in (_158_2135, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_158_2136))
in (
# 1690 "FStar.SMTEncoding.Encode.fst"
let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _158_2142 = (let _158_2139 = (let _158_2138 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _158_2137 = (varops.next_id ())
in (vname, _158_2138, FStar_SMTEncoding_Term.Term_sort, _158_2137)))
in (FStar_SMTEncoding_Term.fresh_constructor _158_2139))
in (let _158_2141 = (let _158_2140 = (pretype_axiom vapp vars)
in (_158_2140)::[])
in (_158_2142)::_158_2141))
end else begin
[]
end
in (
# 1695 "FStar.SMTEncoding.Encode.fst"
let g = (let _158_2144 = (let _158_2143 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_158_2143)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _158_2144))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _76_2824 se -> (match (_76_2824) with
| (g, env) -> begin
(
# 1701 "FStar.SMTEncoding.Encode.fst"
let _76_2828 = (encode_sigelt env se)
in (match (_76_2828) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1704 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1729 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _76_2835 -> (match (_76_2835) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_76_2837) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1734 "FStar.SMTEncoding.Encode.fst"
let _76_2844 = (new_term_constant env x)
in (match (_76_2844) with
| (xxsym, xx, env') -> begin
(
# 1735 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1736 "FStar.SMTEncoding.Encode.fst"
let _76_2846 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _158_2159 = (FStar_Syntax_Print.bv_to_string x)
in (let _158_2158 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _158_2157 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _158_2159 _158_2158 _158_2157))))
end else begin
()
end
in (
# 1738 "FStar.SMTEncoding.Encode.fst"
let _76_2850 = (encode_term_pred None t1 env xx)
in (match (_76_2850) with
| (t, decls') -> begin
(
# 1739 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _158_2163 = (let _158_2162 = (FStar_Syntax_Print.bv_to_string x)
in (let _158_2161 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _158_2160 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _158_2162 _158_2161 _158_2160))))
in Some (_158_2163))
end else begin
None
end
in (
# 1743 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((FStar_SMTEncoding_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_76_2855, t)) -> begin
(
# 1749 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1750 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (
# 1752 "FStar.SMTEncoding.Encode.fst"
let _76_2864 = (encode_free_var env fv t t_norm [])
in (match (_76_2864) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1757 "FStar.SMTEncoding.Encode.fst"
let _76_2878 = (encode_sigelt env se)
in (match (_76_2878) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1762 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1763 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _76_2885 -> (match (_76_2885) with
| (l, _76_2882, _76_2884) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1764 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _76_2892 -> (match (_76_2892) with
| (l, _76_2889, _76_2891) -> begin
(let _158_2171 = (FStar_All.pipe_left (fun _158_2167 -> FStar_SMTEncoding_Term.Echo (_158_2167)) (Prims.fst l))
in (let _158_2170 = (let _158_2169 = (let _158_2168 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_158_2168))
in (_158_2169)::[])
in (_158_2171)::_158_2170))
end))))
in (prefix, suffix))))

# 1768 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1769 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _158_2176 = (let _158_2175 = (let _158_2174 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _158_2174; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_158_2175)::[])
in (FStar_ST.op_Colon_Equals last_env _158_2176)))

# 1772 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_76_2898 -> begin
(
# 1774 "FStar.SMTEncoding.Encode.fst"
let _76_2901 = e
in {bindings = _76_2901.bindings; depth = _76_2901.depth; tcenv = tcenv; warn = _76_2901.warn; cache = _76_2901.cache; nolabels = _76_2901.nolabels; use_zfuel_name = _76_2901.use_zfuel_name; encode_non_total_function_typ = _76_2901.encode_non_total_function_typ})
end))

# 1775 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _76_2907::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1778 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _76_2909 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1781 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1782 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1782 "FStar.SMTEncoding.Encode.fst"
let _76_2915 = hd
in {bindings = _76_2915.bindings; depth = _76_2915.depth; tcenv = _76_2915.tcenv; warn = _76_2915.warn; cache = refs; nolabels = _76_2915.nolabels; use_zfuel_name = _76_2915.use_zfuel_name; encode_non_total_function_typ = _76_2915.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1784 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _76_2918 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _76_2922::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1787 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _76_2924 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1788 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _76_2925 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1789 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _76_2926 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_76_2929::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _76_2934 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1795 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1796 "FStar.SMTEncoding.Encode.fst"
let _76_2936 = (init_env tcenv)
in (
# 1797 "FStar.SMTEncoding.Encode.fst"
let _76_2938 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1799 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1800 "FStar.SMTEncoding.Encode.fst"
let _76_2941 = (push_env ())
in (
# 1801 "FStar.SMTEncoding.Encode.fst"
let _76_2943 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1803 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1804 "FStar.SMTEncoding.Encode.fst"
let _76_2946 = (let _158_2197 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _158_2197))
in (
# 1805 "FStar.SMTEncoding.Encode.fst"
let _76_2948 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1807 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1808 "FStar.SMTEncoding.Encode.fst"
let _76_2951 = (mark_env ())
in (
# 1809 "FStar.SMTEncoding.Encode.fst"
let _76_2953 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1811 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1812 "FStar.SMTEncoding.Encode.fst"
let _76_2956 = (reset_mark_env ())
in (
# 1813 "FStar.SMTEncoding.Encode.fst"
let _76_2958 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1815 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1816 "FStar.SMTEncoding.Encode.fst"
let _76_2961 = (commit_mark_env ())
in (
# 1817 "FStar.SMTEncoding.Encode.fst"
let _76_2963 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1819 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1820 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _158_2213 = (let _158_2212 = (let _158_2211 = (let _158_2210 = (let _158_2209 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _158_2209 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _158_2210 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _158_2211))
in FStar_SMTEncoding_Term.Caption (_158_2212))
in (_158_2213)::decls)
end else begin
decls
end)
in (
# 1824 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1825 "FStar.SMTEncoding.Encode.fst"
let _76_2972 = (encode_sigelt env se)
in (match (_76_2972) with
| (decls, env) -> begin
(
# 1826 "FStar.SMTEncoding.Encode.fst"
let _76_2973 = (set_env env)
in (let _158_2214 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _158_2214)))
end)))))

# 1829 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1830 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1831 "FStar.SMTEncoding.Encode.fst"
let _76_2978 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _158_2219 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _158_2219))
end else begin
()
end
in (
# 1833 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1834 "FStar.SMTEncoding.Encode.fst"
let _76_2985 = (encode_signature (
# 1834 "FStar.SMTEncoding.Encode.fst"
let _76_2981 = env
in {bindings = _76_2981.bindings; depth = _76_2981.depth; tcenv = _76_2981.tcenv; warn = false; cache = _76_2981.cache; nolabels = _76_2981.nolabels; use_zfuel_name = _76_2981.use_zfuel_name; encode_non_total_function_typ = _76_2981.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_76_2985) with
| (decls, env) -> begin
(
# 1835 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1837 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1840 "FStar.SMTEncoding.Encode.fst"
let _76_2991 = (set_env (
# 1840 "FStar.SMTEncoding.Encode.fst"
let _76_2989 = env
in {bindings = _76_2989.bindings; depth = _76_2989.depth; tcenv = _76_2989.tcenv; warn = true; cache = _76_2989.cache; nolabels = _76_2989.nolabels; use_zfuel_name = _76_2989.use_zfuel_name; encode_non_total_function_typ = _76_2989.encode_non_total_function_typ}))
in (
# 1841 "FStar.SMTEncoding.Encode.fst"
let _76_2993 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1842 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1845 "FStar.SMTEncoding.Encode.fst"
let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (
# 1846 "FStar.SMTEncoding.Encode.fst"
let _76_2999 = (let _158_2238 = (let _158_2237 = (let _158_2236 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _158_2236))
in (FStar_Util.format1 "Starting query at %s" _158_2237))
in (push _158_2238))
in (
# 1847 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _76_3002 -> (match (()) with
| () -> begin
(let _158_2243 = (let _158_2242 = (let _158_2241 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _158_2241))
in (FStar_Util.format1 "Ending query at %s" _158_2242))
in (pop _158_2243))
end))
in (
# 1848 "FStar.SMTEncoding.Encode.fst"
let _76_3056 = (
# 1849 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1850 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1851 "FStar.SMTEncoding.Encode.fst"
let _76_3026 = (
# 1852 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1854 "FStar.SMTEncoding.Encode.fst"
let _76_3015 = (aux rest)
in (match (_76_3015) with
| (out, rest) -> begin
(
# 1855 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _158_2249 = (let _158_2248 = (FStar_Syntax_Syntax.mk_binder (
# 1856 "FStar.SMTEncoding.Encode.fst"
let _76_3017 = x
in {FStar_Syntax_Syntax.ppname = _76_3017.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _76_3017.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_158_2248)::out)
in (_158_2249, rest)))
end))
end
| _76_3020 -> begin
([], bindings)
end))
in (
# 1858 "FStar.SMTEncoding.Encode.fst"
let _76_3023 = (aux bindings)
in (match (_76_3023) with
| (closing, bindings) -> begin
(let _158_2250 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_158_2250, bindings))
end)))
in (match (_76_3026) with
| (q, bindings) -> begin
(
# 1860 "FStar.SMTEncoding.Encode.fst"
let _76_3035 = (let _158_2252 = (FStar_List.filter (fun _76_21 -> (match (_76_21) with
| FStar_TypeChecker_Env.Binding_sig (_76_3029) -> begin
false
end
| _76_3032 -> begin
true
end)) bindings)
in (encode_env_bindings env _158_2252))
in (match (_76_3035) with
| (env_decls, env) -> begin
(
# 1861 "FStar.SMTEncoding.Encode.fst"
let _76_3036 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _158_2253 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _158_2253))
end else begin
()
end
in (
# 1864 "FStar.SMTEncoding.Encode.fst"
let _76_3040 = (encode_formula q env)
in (match (_76_3040) with
| (phi, qdecls) -> begin
(
# 1867 "FStar.SMTEncoding.Encode.fst"
let _76_3045 = (let _158_2254 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _158_2254 phi))
in (match (_76_3045) with
| (phi, labels, _76_3044) -> begin
(
# 1868 "FStar.SMTEncoding.Encode.fst"
let _76_3048 = (encode_labels labels)
in (match (_76_3048) with
| (label_prefix, label_suffix) -> begin
(
# 1869 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1873 "FStar.SMTEncoding.Encode.fst"
let qry = (let _158_2256 = (let _158_2255 = (FStar_SMTEncoding_Term.mkNot phi)
in (_158_2255, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_158_2256))
in (
# 1874 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_76_3056) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _76_3063); FStar_SMTEncoding_Term.hash = _76_3060; FStar_SMTEncoding_Term.freevars = _76_3058}, _76_3068) -> begin
(
# 1877 "FStar.SMTEncoding.Encode.fst"
let _76_3071 = (pop ())
in ())
end
| _76_3074 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1878 "FStar.SMTEncoding.Encode.fst"
let _76_3075 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _76_3079) -> begin
(
# 1880 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1881 "FStar.SMTEncoding.Encode.fst"
let _76_3083 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 1883 "FStar.SMTEncoding.Encode.fst"
let with_fuel = (fun p _76_3089 -> (match (_76_3089) with
| (n, i) -> begin
(let _158_2279 = (let _158_2278 = (let _158_2263 = (let _158_2262 = (FStar_Util.string_of_int n)
in (let _158_2261 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _158_2262 _158_2261)))
in FStar_SMTEncoding_Term.Caption (_158_2263))
in (let _158_2277 = (let _158_2276 = (let _158_2268 = (let _158_2267 = (let _158_2266 = (let _158_2265 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _158_2264 = (FStar_SMTEncoding_Term.n_fuel n)
in (_158_2265, _158_2264)))
in (FStar_SMTEncoding_Term.mkEq _158_2266))
in (_158_2267, None))
in FStar_SMTEncoding_Term.Assume (_158_2268))
in (let _158_2275 = (let _158_2274 = (let _158_2273 = (let _158_2272 = (let _158_2271 = (let _158_2270 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _158_2269 = (FStar_SMTEncoding_Term.n_fuel i)
in (_158_2270, _158_2269)))
in (FStar_SMTEncoding_Term.mkEq _158_2271))
in (_158_2272, None))
in FStar_SMTEncoding_Term.Assume (_158_2273))
in (_158_2274)::(p)::(FStar_SMTEncoding_Term.CheckSat)::[])
in (_158_2276)::_158_2275))
in (_158_2278)::_158_2277))
in (FStar_List.append _158_2279 suffix))
end))
in (
# 1890 "FStar.SMTEncoding.Encode.fst"
let check = (fun p -> (
# 1891 "FStar.SMTEncoding.Encode.fst"
let initial_config = (let _158_2283 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _158_2282 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_158_2283, _158_2282)))
in (
# 1892 "FStar.SMTEncoding.Encode.fst"
let alt_configs = (let _158_2302 = (let _158_2301 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _158_2286 = (let _158_2285 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _158_2284 = (FStar_ST.read FStar_Options.max_ifuel)
in (_158_2285, _158_2284)))
in (_158_2286)::[])
end else begin
[]
end
in (let _158_2300 = (let _158_2299 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _158_2289 = (let _158_2288 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _158_2287 = (FStar_ST.read FStar_Options.max_ifuel)
in (_158_2288, _158_2287)))
in (_158_2289)::[])
end else begin
[]
end
in (let _158_2298 = (let _158_2297 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _158_2292 = (let _158_2291 = (FStar_ST.read FStar_Options.max_fuel)
in (let _158_2290 = (FStar_ST.read FStar_Options.max_ifuel)
in (_158_2291, _158_2290)))
in (_158_2292)::[])
end else begin
[]
end
in (let _158_2296 = (let _158_2295 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _158_2294 = (let _158_2293 = (FStar_ST.read FStar_Options.min_fuel)
in (_158_2293, 1))
in (_158_2294)::[])
end else begin
[]
end
in (_158_2295)::[])
in (_158_2297)::_158_2296))
in (_158_2299)::_158_2298))
in (_158_2301)::_158_2300))
in (FStar_List.flatten _158_2302))
in (
# 1897 "FStar.SMTEncoding.Encode.fst"
let report = (fun errs -> (
# 1898 "FStar.SMTEncoding.Encode.fst"
let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _76_3098 -> begin
errs
end)
in (
# 1901 "FStar.SMTEncoding.Encode.fst"
let _76_3100 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _158_2310 = (let _158_2305 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _158_2305))
in (let _158_2309 = (let _158_2306 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _158_2306 FStar_Util.string_of_int))
in (let _158_2308 = (let _158_2307 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _158_2307 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _158_2310 _158_2309 _158_2308))))
end else begin
()
end
in (FStar_TypeChecker_Errors.add_errors tcenv errs))))
in (
# 1908 "FStar.SMTEncoding.Encode.fst"
let rec try_alt_configs = (fun p errs _76_22 -> (match (_76_22) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _158_2321 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _158_2321 (cb mi p [])))
end
| _76_3112 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _158_2323 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _158_2323 (fun _76_3118 -> (match (_76_3118) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _76_3121 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _76_3124 p alt _76_3129 -> (match ((_76_3124, _76_3129)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _158_2331 = (let _158_2328 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _158_2328))
in (let _158_2330 = (FStar_Util.string_of_int prev_fuel)
in (let _158_2329 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _158_2331 _158_2330 _158_2329))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _158_2332 = (with_fuel p initial_config)
in (FStar_SMTEncoding_Z3.ask fresh labels _158_2332 (cb initial_config p alt_configs))))))))
in (
# 1933 "FStar.SMTEncoding.Encode.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 1935 "FStar.SMTEncoding.Encode.fst"
let _76_3134 = (let _158_2338 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _158_2338 q))
in (match (_76_3134) with
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
# 1940 "FStar.SMTEncoding.Encode.fst"
let _76_3135 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _76_3138 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1946 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1947 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1948 "FStar.SMTEncoding.Encode.fst"
let _76_3142 = (push "query")
in (
# 1949 "FStar.SMTEncoding.Encode.fst"
let _76_3149 = (encode_formula_with_labels q env)
in (match (_76_3149) with
| (f, _76_3146, _76_3148) -> begin
(
# 1950 "FStar.SMTEncoding.Encode.fst"
let _76_3150 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _76_3154) -> begin
true
end
| _76_3158 -> begin
false
end))
end)))))

# 1955 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1969 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _76_3159 -> ()); FStar_TypeChecker_Env.push = (fun _76_3161 -> ()); FStar_TypeChecker_Env.pop = (fun _76_3163 -> ()); FStar_TypeChecker_Env.mark = (fun _76_3165 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _76_3167 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _76_3169 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _76_3171 _76_3173 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _76_3175 _76_3177 -> ()); FStar_TypeChecker_Env.solve = (fun _76_3179 _76_3181 _76_3183 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _76_3185 _76_3187 -> false); FStar_TypeChecker_Env.finish = (fun _76_3189 -> ()); FStar_TypeChecker_Env.refresh = (fun _76_3190 -> ())}





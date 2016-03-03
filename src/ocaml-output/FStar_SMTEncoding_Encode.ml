
open Prims
# 34 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 35 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _75_28 -> (match (_75_28) with
| (a, b) -> begin
(a, b, c)
end))

# 36 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _75_1 -> (match (_75_1) with
| (FStar_Util.Inl (_75_32), _75_35) -> begin
false
end
| _75_38 -> begin
true
end)) args))

# 37 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _156_13 = (let _156_12 = (let _156_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _156_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_12))
in Some (_156_13))
end))

# 42 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 43 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _75_47 = a
in (let _156_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _156_20; FStar_Syntax_Syntax.index = _75_47.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _75_47.FStar_Syntax_Syntax.sort}))
in (let _156_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _156_21))))

# 46 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _75_54 -> (match (()) with
| () -> begin
(let _156_31 = (let _156_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _156_30 lid.FStar_Ident.str))
in (FStar_All.failwith _156_31))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _75_58 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_75_58) with
| (_75_56, t) -> begin
(match ((let _156_32 = (FStar_Syntax_Subst.compress t)
in _156_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _75_66 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_75_66) with
| (binders, _75_65) -> begin
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
| _75_69 -> begin
(fail ())
end)
end))))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _156_38 = (let _156_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _156_37))
in (FStar_All.pipe_left escape _156_38)))

# 58 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _156_44 = (let _156_43 = (mk_term_projector_name lid a)
in (_156_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _156_44)))

# 60 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _156_50 = (let _156_49 = (mk_term_projector_name_by_pos lid i)
in (_156_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _156_50)))

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
let new_scope = (fun _75_93 -> (match (()) with
| () -> begin
(let _156_154 = (FStar_Util.smap_create 100)
in (let _156_153 = (FStar_Util.smap_create 100)
in (_156_154, _156_153)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _156_156 = (let _156_155 = (new_scope ())
in (_156_155)::[])
in (FStar_Util.mk_ref _156_156))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _156_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _156_160 (fun _75_101 -> (match (_75_101) with
| (names, _75_100) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_75_104) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _75_106 = (FStar_Util.incr ctr)
in (let _156_162 = (let _156_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _156_161))
in (Prims.strcat (Prims.strcat y "__") _156_162)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _156_164 = (let _156_163 = (FStar_ST.read scopes)
in (FStar_List.hd _156_163))
in (FStar_All.pipe_left Prims.fst _156_164))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _75_110 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _156_171 = (let _156_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _156_169 "__"))
in (let _156_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _156_171 _156_170))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _75_118 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _75_119 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _156_179 = (let _156_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _156_178))
in (FStar_Util.format2 "%s_%s" pfx _156_179)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _156_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _156_183 (fun _75_128 -> (match (_75_128) with
| (_75_126, strings) -> begin
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
let f = (let _156_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _156_184))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _156_186 = (let _156_185 = (FStar_ST.read scopes)
in (FStar_List.hd _156_185))
in (FStar_All.pipe_left Prims.snd _156_186))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _75_135 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _75_138 -> (match (()) with
| () -> begin
(let _156_191 = (let _156_190 = (new_scope ())
in (let _156_189 = (FStar_ST.read scopes)
in (_156_190)::_156_189))
in (FStar_ST.op_Colon_Equals scopes _156_191))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _75_140 -> (match (()) with
| () -> begin
(let _156_195 = (let _156_194 = (FStar_ST.read scopes)
in (FStar_List.tl _156_194))
in (FStar_ST.op_Colon_Equals scopes _156_195))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _75_142 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _75_144 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _75_146 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _75_159 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _75_164 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _75_167 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 122 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _75_169 = x
in (let _156_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _156_210; FStar_Syntax_Syntax.index = _75_169.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _75_169.FStar_Syntax_Syntax.sort})))

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
| Binding_var (_75_173) -> begin
_75_173
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_75_176) -> begin
_75_176
end))

# 131 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 132 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 142 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _156_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _75_2 -> (match (_75_2) with
| Binding_var (x, _75_191) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _75_196, _75_198, _75_200) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _156_268 (FStar_String.concat ", "))))

# 147 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_156_278))
end else begin
None
end)

# 154 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _156_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _156_283))))

# 158 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _156_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _156_288))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _75_214 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _75_214.tcenv; warn = _75_214.warn; cache = _75_214.cache; nolabels = _75_214.nolabels; use_zfuel_name = _75_214.use_zfuel_name; encode_non_total_function_typ = _75_214.encode_non_total_function_typ})))))

# 162 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _75_220 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _75_220.depth; tcenv = _75_220.tcenv; warn = _75_220.warn; cache = _75_220.cache; nolabels = _75_220.nolabels; use_zfuel_name = _75_220.use_zfuel_name; encode_non_total_function_typ = _75_220.encode_non_total_function_typ})))))

# 166 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _75_225 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _75_225.depth; tcenv = _75_225.tcenv; warn = _75_225.warn; cache = _75_225.cache; nolabels = _75_225.nolabels; use_zfuel_name = _75_225.use_zfuel_name; encode_non_total_function_typ = _75_225.encode_non_total_function_typ}))

# 168 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _75_3 -> (match (_75_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _75_235 -> begin
None
end)))) with
| None -> begin
(let _156_305 = (let _156_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _156_304))
in (FStar_All.failwith _156_305))
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
in (let _156_316 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _75_245 = env
in (let _156_315 = (let _156_314 = (let _156_313 = (let _156_312 = (let _156_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _156_310 -> Some (_156_310)) _156_311))
in (x, fname, _156_312, None))
in Binding_fvar (_156_313))
in (_156_314)::env.bindings)
in {bindings = _156_315; depth = _75_245.depth; tcenv = _75_245.tcenv; warn = _75_245.warn; cache = _75_245.cache; nolabels = _75_245.nolabels; use_zfuel_name = _75_245.use_zfuel_name; encode_non_total_function_typ = _75_245.encode_non_total_function_typ}))
in (fname, ftok, _156_316)))))

# 179 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _75_4 -> (match (_75_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _75_257 -> begin
None
end))))

# 181 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _156_327 = (let _156_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _156_326))
in (FStar_All.failwith _156_327))
end
| Some (s) -> begin
s
end))

# 185 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _75_267 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _75_267.depth; tcenv = _75_267.tcenv; warn = _75_267.warn; cache = _75_267.cache; nolabels = _75_267.nolabels; use_zfuel_name = _75_267.use_zfuel_name; encode_non_total_function_typ = _75_267.encode_non_total_function_typ}))

# 187 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _75_276 = (lookup_lid env x)
in (match (_75_276) with
| (t1, t2, _75_275) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _156_344 = (let _156_343 = (let _156_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_156_342)::[])
in (f, _156_343))
in (FStar_SMTEncoding_Term.mkApp _156_344))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _75_278 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _75_278.depth; tcenv = _75_278.tcenv; warn = _75_278.warn; cache = _75_278.cache; nolabels = _75_278.nolabels; use_zfuel_name = _75_278.use_zfuel_name; encode_non_total_function_typ = _75_278.encode_non_total_function_typ}))
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
| _75_291 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_75_295, fuel::[]) -> begin
if (let _156_350 = (let _156_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _156_349 Prims.fst))
in (FStar_Util.starts_with _156_350 "fuel")) then begin
(let _156_353 = (let _156_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _156_352 fuel))
in (FStar_All.pipe_left (fun _156_351 -> Some (_156_351)) _156_353))
end else begin
Some (t)
end
end
| _75_301 -> begin
Some (t)
end)
end
| _75_303 -> begin
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
(let _156_357 = (let _156_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _156_356))
in (FStar_All.failwith _156_357))
end))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _75_316 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_75_316) with
| (x, _75_313, _75_315) -> begin
x
end)))

# 213 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _75_322 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_75_322) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _75_326; FStar_SMTEncoding_Term.freevars = _75_324}) when env.use_zfuel_name -> begin
(g, zf)
end
| _75_334 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _75_344 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 225 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _75_5 -> (match (_75_5) with
| Binding_fvar (_75_349, nm', tok, _75_353) when (nm = nm') -> begin
tok
end
| _75_357 -> begin
None
end))))

# 234 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _75_362 -> (match (_75_362) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _75_364 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _75_367 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_75_367) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _75_377 -> begin
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
(let _156_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _156_374))
end
| _75_390 -> begin
(let _156_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _156_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _75_393 -> begin
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
(let _156_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv v.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _156_381 FStar_Option.isNone))
end
| _75_438 -> begin
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
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _156_394 = (let _156_392 = (FStar_Syntax_Syntax.null_binder t)
in (_156_392)::[])
in (let _156_393 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
in (FStar_Syntax_Util.abs _156_394 _156_393 None))))

# 279 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _156_401 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _156_401))
end
| s -> begin
(
# 282 "FStar.SMTEncoding.Encode.fst"
let _75_450 = ()
in (let _156_402 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _156_402)))
end)) e)))

# 283 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 285 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _75_6 -> (match (_75_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _75_460 -> begin
false
end))

# 290 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 291 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _75_471; FStar_SMTEncoding_Term.freevars = _75_469}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _75_489) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _75_496 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_75_498, []) -> begin
(
# 302 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _75_504 -> begin
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
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _75_7 -> (match (_75_7) with
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
(let _156_456 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _156_456))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _156_457 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _156_457))
end
| FStar_Const.Const_int (i) -> begin
(let _156_458 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _156_458))
end
| FStar_Const.Const_int32 (i) -> begin
(let _156_462 = (let _156_461 = (let _156_460 = (let _156_459 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _156_459))
in (_156_460)::[])
in ("FStar.Int32.Int32", _156_461))
in (FStar_SMTEncoding_Term.mkApp _156_462))
end
| FStar_Const.Const_string (bytes, _75_526) -> begin
(let _156_463 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _156_463))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _156_465 = (let _156_464 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _156_464))
in (FStar_All.failwith _156_465))
end))

# 356 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 357 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 358 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_75_540) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_75_543) -> begin
(let _156_474 = (FStar_Syntax_Util.unrefine t)
in (aux true _156_474))
end
| _75_546 -> begin
if norm then begin
(let _156_475 = (whnf env t)
in (aux false _156_475))
end else begin
(let _156_478 = (let _156_477 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _156_476 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _156_477 _156_476)))
in (FStar_All.failwith _156_478))
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
| _75_554 -> begin
(let _156_481 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _156_481))
end)))

# 374 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 381 "FStar.SMTEncoding.Encode.fst"
let _75_558 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_531 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _156_531))
end else begin
()
end
in (
# 383 "FStar.SMTEncoding.Encode.fst"
let _75_586 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _75_565 b -> (match (_75_565) with
| (vars, guards, env, decls, names) -> begin
(
# 384 "FStar.SMTEncoding.Encode.fst"
let _75_580 = (
# 385 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 386 "FStar.SMTEncoding.Encode.fst"
let _75_571 = (gen_term_var env x)
in (match (_75_571) with
| (xxsym, xx, env') -> begin
(
# 387 "FStar.SMTEncoding.Encode.fst"
let _75_574 = (let _156_534 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _156_534 env xx))
in (match (_75_574) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_75_580) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_75_586) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 402 "FStar.SMTEncoding.Encode.fst"
let _75_593 = (encode_term t env)
in (match (_75_593) with
| (t, decls) -> begin
(let _156_539 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_156_539, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 406 "FStar.SMTEncoding.Encode.fst"
let _75_600 = (encode_term t env)
in (match (_75_600) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _156_544 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_156_544, decls))
end
| Some (f) -> begin
(let _156_545 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_156_545, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 414 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 415 "FStar.SMTEncoding.Encode.fst"
let _75_607 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _156_550 = (FStar_Syntax_Print.tag_of_term t)
in (let _156_549 = (FStar_Syntax_Print.tag_of_term t0)
in (let _156_548 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _156_550 _156_549 _156_548))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _156_555 = (let _156_554 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _156_553 = (FStar_Syntax_Print.tag_of_term t0)
in (let _156_552 = (FStar_Syntax_Print.term_to_string t0)
in (let _156_551 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _156_554 _156_553 _156_552 _156_551)))))
in (FStar_All.failwith _156_555))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _156_557 = (let _156_556 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _156_556))
in (FStar_All.failwith _156_557))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _75_618) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _75_623) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 431 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v, _75_631) -> begin
(let _156_558 = (lookup_free_var env v)
in (_156_558, []))
end
| FStar_Syntax_Syntax.Tm_type (_75_635) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _75_639) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _156_559 = (encode_const c)
in (_156_559, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 447 "FStar.SMTEncoding.Encode.fst"
let _75_650 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_75_650) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 451 "FStar.SMTEncoding.Encode.fst"
let _75_657 = (encode_binders None binders env)
in (match (_75_657) with
| (vars, guards, env', decls, _75_656) -> begin
(
# 452 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _156_560 = (varops.fresh "f")
in (_156_560, FStar_SMTEncoding_Term.Term_sort))
in (
# 453 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 454 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 455 "FStar.SMTEncoding.Encode.fst"
let _75_663 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_75_663) with
| (pre_opt, res_t) -> begin
(
# 456 "FStar.SMTEncoding.Encode.fst"
let _75_666 = (encode_term_pred None res_t env' app)
in (match (_75_666) with
| (res_pred, decls') -> begin
(
# 457 "FStar.SMTEncoding.Encode.fst"
let _75_675 = (match (pre_opt) with
| None -> begin
(let _156_561 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_156_561, decls))
end
| Some (pre) -> begin
(
# 460 "FStar.SMTEncoding.Encode.fst"
let _75_672 = (encode_formula pre env')
in (match (_75_672) with
| (guard, decls0) -> begin
(let _156_562 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_156_562, (FStar_List.append decls decls0)))
end))
end)
in (match (_75_675) with
| (guards, guard_decls) -> begin
(
# 462 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _156_564 = (let _156_563 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _156_563))
in (FStar_SMTEncoding_Term.mkForall _156_564))
in (
# 467 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _156_566 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _156_566 (FStar_List.filter (fun _75_680 -> (match (_75_680) with
| (x, _75_679) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 468 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _75_686) -> begin
(let _156_569 = (let _156_568 = (let _156_567 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _156_567))
in (FStar_SMTEncoding_Term.mkApp _156_568))
in (_156_569, []))
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
(let _156_570 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_156_570))
end else begin
None
end
in (
# 481 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 483 "FStar.SMTEncoding.Encode.fst"
let t = (let _156_572 = (let _156_571 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _156_571))
in (FStar_SMTEncoding_Term.mkApp _156_572))
in (
# 484 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _156_574 = (let _156_573 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_156_573, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_156_574))
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 489 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 490 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _156_581 = (let _156_580 = (let _156_579 = (let _156_578 = (let _156_577 = (let _156_576 = (let _156_575 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _156_575))
in (f_has_t, _156_576))
in (FStar_SMTEncoding_Term.mkImp _156_577))
in (((f_has_t)::[])::[], (fsym)::cvars, _156_578))
in (mkForall_fuel _156_579))
in (_156_580, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_156_581))
in (
# 491 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _156_585 = (let _156_584 = (let _156_583 = (let _156_582 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _156_582))
in (FStar_SMTEncoding_Term.mkForall _156_583))
in (_156_584, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_156_585))
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 495 "FStar.SMTEncoding.Encode.fst"
let _75_702 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
let t_kinding = (let _156_587 = (let _156_586 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_156_586, None))
in FStar_SMTEncoding_Term.Assume (_156_587))
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
let t_interp = (let _156_594 = (let _156_593 = (let _156_592 = (let _156_591 = (let _156_590 = (let _156_589 = (let _156_588 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _156_588))
in (f_has_t, _156_589))
in (FStar_SMTEncoding_Term.mkImp _156_590))
in (((f_has_t)::[])::[], (fsym)::[], _156_591))
in (mkForall_fuel _156_592))
in (_156_593, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_156_594))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_75_713) -> begin
(
# 513 "FStar.SMTEncoding.Encode.fst"
let _75_733 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _75_720; FStar_Syntax_Syntax.pos = _75_718; FStar_Syntax_Syntax.vars = _75_716} -> begin
(
# 515 "FStar.SMTEncoding.Encode.fst"
let _75_728 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_75_728) with
| (b, f) -> begin
(let _156_596 = (let _156_595 = (FStar_List.hd b)
in (Prims.fst _156_595))
in (_156_596, f))
end))
end
| _75_730 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_75_733) with
| (x, f) -> begin
(
# 519 "FStar.SMTEncoding.Encode.fst"
let _75_736 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_75_736) with
| (base_t, decls) -> begin
(
# 520 "FStar.SMTEncoding.Encode.fst"
let _75_740 = (gen_term_var env x)
in (match (_75_740) with
| (x, xtm, env') -> begin
(
# 521 "FStar.SMTEncoding.Encode.fst"
let _75_743 = (encode_formula f env')
in (match (_75_743) with
| (refinement, decls') -> begin
(
# 523 "FStar.SMTEncoding.Encode.fst"
let _75_746 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_75_746) with
| (fsym, fterm) -> begin
(
# 525 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _156_598 = (let _156_597 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_156_597, refinement))
in (FStar_SMTEncoding_Term.mkAnd _156_598))
in (
# 527 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _156_600 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _156_600 (FStar_List.filter (fun _75_751 -> (match (_75_751) with
| (y, _75_750) -> begin
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
| Some (t, _75_758, _75_760) -> begin
(let _156_603 = (let _156_602 = (let _156_601 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _156_601))
in (FStar_SMTEncoding_Term.mkApp _156_602))
in (_156_603, []))
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
let t = (let _156_605 = (let _156_604 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _156_604))
in (FStar_SMTEncoding_Term.mkApp _156_605))
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
let assumption = (let _156_607 = (let _156_606 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _156_606))
in (FStar_SMTEncoding_Term.mkForall _156_607))
in (
# 548 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _156_614 = (let _156_613 = (let _156_612 = (let _156_611 = (let _156_610 = (let _156_609 = (let _156_608 = (FStar_Syntax_Print.term_to_string t0)
in Some (_156_608))
in (assumption, _156_609))
in FStar_SMTEncoding_Term.Assume (_156_610))
in (_156_611)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, None)))::_156_612)
in (tdecl)::_156_613)
in (FStar_List.append (FStar_List.append decls decls') _156_614))
in (
# 553 "FStar.SMTEncoding.Encode.fst"
let _75_773 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
let ttm = (let _156_615 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _156_615))
in (
# 559 "FStar.SMTEncoding.Encode.fst"
let _75_782 = (encode_term_pred None k env ttm)
in (match (_75_782) with
| (t_has_k, decls) -> begin
(
# 560 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_75_785) -> begin
(
# 564 "FStar.SMTEncoding.Encode.fst"
let _75_789 = (FStar_Syntax_Util.head_and_args t0)
in (match (_75_789) with
| (head, args_e) -> begin
(match ((let _156_617 = (let _156_616 = (FStar_Syntax_Subst.compress head)
in _156_616.FStar_Syntax_Syntax.n)
in (_156_617, args_e))) with
| (FStar_Syntax_Syntax.Tm_abs (_75_791), _75_794) -> begin
(let _156_618 = (whnf env t)
in (encode_term _156_618 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (l, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (l, _), _::(v1, _)::(v2, _)::[])) when (FStar_Ident.lid_equals l.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
(
# 571 "FStar.SMTEncoding.Encode.fst"
let _75_840 = (encode_term v1 env)
in (match (_75_840) with
| (v1, decls1) -> begin
(
# 572 "FStar.SMTEncoding.Encode.fst"
let _75_843 = (encode_term v2 env)
in (match (_75_843) with
| (v2, decls2) -> begin
(let _156_619 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_156_619, (FStar_List.append decls1 decls2)))
end))
end))
end
| _75_845 -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let _75_848 = (encode_args args_e env)
in (match (_75_848) with
| (args, decls) -> begin
(
# 578 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 579 "FStar.SMTEncoding.Encode.fst"
let _75_853 = (encode_term head env)
in (match (_75_853) with
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
let _75_862 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_75_862) with
| (formals, rest) -> begin
(
# 585 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _75_866 _75_870 -> (match ((_75_866, _75_870)) with
| ((bv, _75_865), (a, _75_869)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 586 "FStar.SMTEncoding.Encode.fst"
let ty = (let _156_624 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _156_624 (FStar_Syntax_Subst.subst subst)))
in (
# 587 "FStar.SMTEncoding.Encode.fst"
let _75_875 = (encode_term_pred None ty env app_tm)
in (match (_75_875) with
| (has_type, decls'') -> begin
(
# 588 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 589 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _156_626 = (let _156_625 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_156_625, None))
in FStar_SMTEncoding_Term.Assume (_156_626))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 593 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 594 "FStar.SMTEncoding.Encode.fst"
let _75_882 = (lookup_free_var_sym env fv)
in (match (_75_882) with
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
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(let _156_630 = (let _156_629 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _156_629 Prims.snd))
in Some (_156_630))
end
| FStar_Syntax_Syntax.Tm_ascribed (_75_920, t, _75_923) -> begin
Some (t)
end
| _75_927 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 611 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _156_631 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _156_631))
in (
# 612 "FStar.SMTEncoding.Encode.fst"
let _75_935 = (curried_arrow_formals_comp head_type)
in (match (_75_935) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _75_957 -> begin
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
let _75_966 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_75_966) with
| (bs, body, opening) -> begin
(
# 627 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _75_968 -> (match (()) with
| () -> begin
(
# 628 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 629 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _156_634 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_156_634, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 634 "FStar.SMTEncoding.Encode.fst"
let _75_972 = (let _156_636 = (let _156_635 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _156_635))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _156_636))
in (fallback ()))
end
| Some (lc) -> begin
if (let _156_637 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _156_637)) then begin
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
let _75_984 = (encode_binders None bs env)
in (match (_75_984) with
| (vars, guards, envbody, decls, _75_983) -> begin
(
# 645 "FStar.SMTEncoding.Encode.fst"
let _75_987 = (encode_term body envbody)
in (match (_75_987) with
| (body, decls') -> begin
(
# 646 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _156_641 = (let _156_640 = (let _156_639 = (let _156_638 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_156_638, body))
in (FStar_SMTEncoding_Term.mkImp _156_639))
in ([], vars, _156_640))
in (FStar_SMTEncoding_Term.mkForall _156_641))
in (
# 647 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 648 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _75_993, _75_995) -> begin
(let _156_644 = (let _156_643 = (let _156_642 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _156_642))
in (FStar_SMTEncoding_Term.mkApp _156_643))
in (_156_644, []))
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
let f = (let _156_646 = (let _156_645 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _156_645))
in (FStar_SMTEncoding_Term.mkApp _156_646))
in (
# 661 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 662 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 663 "FStar.SMTEncoding.Encode.fst"
let _75_1010 = (encode_term_pred None tfun env f)
in (match (_75_1010) with
| (f_has_t, decls'') -> begin
(
# 664 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _156_648 = (let _156_647 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_156_647, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_156_648))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _156_655 = (let _156_654 = (let _156_653 = (let _156_652 = (let _156_651 = (let _156_650 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _156_649 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_156_650, _156_649)))
in (FStar_SMTEncoding_Term.mkImp _156_651))
in (((app)::[])::[], (FStar_List.append vars cvars), _156_652))
in (FStar_SMTEncoding_Term.mkForall _156_653))
in (_156_654, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_156_655))
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 669 "FStar.SMTEncoding.Encode.fst"
let _75_1014 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_75_1017, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_75_1029); FStar_Syntax_Syntax.lbunivs = _75_1027; FStar_Syntax_Syntax.lbtyp = _75_1025; FStar_Syntax_Syntax.lbeff = _75_1023; FStar_Syntax_Syntax.lbdef = _75_1021}::_75_1019), _75_1035) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _75_1044; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _75_1041; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_75_1054) -> begin
(
# 682 "FStar.SMTEncoding.Encode.fst"
let _75_1056 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 683 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 684 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _156_656 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_156_656, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 691 "FStar.SMTEncoding.Encode.fst"
let _75_1072 = (encode_term e1 env)
in (match (_75_1072) with
| (ee1, decls1) -> begin
(
# 692 "FStar.SMTEncoding.Encode.fst"
let _75_1075 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_75_1075) with
| (xs, e2) -> begin
(
# 693 "FStar.SMTEncoding.Encode.fst"
let _75_1079 = (FStar_List.hd xs)
in (match (_75_1079) with
| (x, _75_1078) -> begin
(
# 694 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 695 "FStar.SMTEncoding.Encode.fst"
let _75_1083 = (encode_term e2 env')
in (match (_75_1083) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 699 "FStar.SMTEncoding.Encode.fst"
let _75_1091 = (encode_term e env)
in (match (_75_1091) with
| (scr, decls) -> begin
(
# 700 "FStar.SMTEncoding.Encode.fst"
let _75_1128 = (FStar_List.fold_right (fun b _75_1095 -> (match (_75_1095) with
| (else_case, decls) -> begin
(
# 701 "FStar.SMTEncoding.Encode.fst"
let _75_1099 = (FStar_Syntax_Subst.open_branch b)
in (match (_75_1099) with
| (p, w, br) -> begin
(
# 702 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _75_1103 _75_1106 -> (match ((_75_1103, _75_1106)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 704 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 705 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 706 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _75_1112 -> (match (_75_1112) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 707 "FStar.SMTEncoding.Encode.fst"
let _75_1122 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 710 "FStar.SMTEncoding.Encode.fst"
let _75_1119 = (encode_term w env)
in (match (_75_1119) with
| (w, decls2) -> begin
(let _156_690 = (let _156_689 = (let _156_688 = (let _156_687 = (let _156_686 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _156_686))
in (FStar_SMTEncoding_Term.mkEq _156_687))
in (guard, _156_688))
in (FStar_SMTEncoding_Term.mkAnd _156_689))
in (_156_690, decls2))
end))
end)
in (match (_75_1122) with
| (guard, decls2) -> begin
(
# 712 "FStar.SMTEncoding.Encode.fst"
let _75_1125 = (encode_br br env)
in (match (_75_1125) with
| (br, decls3) -> begin
(let _156_691 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_156_691, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_75_1128) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _75_1134 -> begin
(let _156_694 = (encode_one_pat env pat)
in (_156_694)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 726 "FStar.SMTEncoding.Encode.fst"
let _75_1137 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_697 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _156_697))
end else begin
()
end
in (
# 727 "FStar.SMTEncoding.Encode.fst"
let _75_1141 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_75_1141) with
| (vars, pat_term) -> begin
(
# 729 "FStar.SMTEncoding.Encode.fst"
let _75_1153 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _75_1144 v -> (match (_75_1144) with
| (env, vars) -> begin
(
# 730 "FStar.SMTEncoding.Encode.fst"
let _75_1150 = (gen_term_var env v)
in (match (_75_1150) with
| (xx, _75_1148, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_75_1153) with
| (env, vars) -> begin
(
# 733 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_75_1158) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _156_705 = (let _156_704 = (encode_const c)
in (scrutinee, _156_704))
in (FStar_SMTEncoding_Term.mkEq _156_705))
end
| FStar_Syntax_Syntax.Pat_cons ((f, _75_1173), args) -> begin
(
# 741 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.v scrutinee)
in (
# 742 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _75_1183 -> (match (_75_1183) with
| (arg, _75_1182) -> begin
(
# 743 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _156_708 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _156_708)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 747 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_75_1190) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_75_1200) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons ((f, _75_1204), args) -> begin
(let _156_716 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _75_1213 -> (match (_75_1213) with
| (arg, _75_1212) -> begin
(
# 759 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _156_715 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _156_715)))
end))))
in (FStar_All.pipe_right _156_716 FStar_List.flatten))
end))
in (
# 763 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _75_1216 -> (match (()) with
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
let _75_1232 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _75_1222 _75_1226 -> (match ((_75_1222, _75_1226)) with
| ((tms, decls), (t, _75_1225)) -> begin
(
# 776 "FStar.SMTEncoding.Encode.fst"
let _75_1229 = (encode_term t env)
in (match (_75_1229) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_75_1232) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 781 "FStar.SMTEncoding.Encode.fst"
let _75_1238 = (encode_formula_with_labels phi env)
in (match (_75_1238) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _75_1241 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 789 "FStar.SMTEncoding.Encode.fst"
let _75_1250 = (let _156_731 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _156_731))
in (match (_75_1250) with
| (head, args) -> begin
(match ((let _156_733 = (let _156_732 = (FStar_Syntax_Util.un_uinst head)
in _156_732.FStar_Syntax_Syntax.n)
in (_156_733, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _75_1253), _75_1257) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _75_1261), _75_1273::(hd, _75_1270)::(tl, _75_1266)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid) -> begin
(let _156_734 = (list_elements tl)
in (hd)::_156_734)
end
| _75_1277 -> begin
(
# 794 "FStar.SMTEncoding.Encode.fst"
let _75_1278 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 796 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 797 "FStar.SMTEncoding.Encode.fst"
let _75_1284 = (let _156_737 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _156_737 FStar_Syntax_Util.head_and_args))
in (match (_75_1284) with
| (head, args) -> begin
(match ((let _156_739 = (let _156_738 = (FStar_Syntax_Util.un_uinst head)
in _156_738.FStar_Syntax_Syntax.n)
in (_156_739, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _75_1287), (_75_1295, _75_1297)::(e, _75_1292)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _75_1303), (e, _75_1308)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _75_1313 -> begin
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
let _75_1321 = (let _156_744 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _156_744 FStar_Syntax_Util.head_and_args))
in (match (_75_1321) with
| (head, args) -> begin
(match ((let _156_746 = (let _156_745 = (FStar_Syntax_Util.un_uinst head)
in _156_745.FStar_Syntax_Syntax.n)
in (_156_746, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _75_1324), (e, _75_1329)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _75_1334 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _156_749 = (list_elements e)
in (FStar_All.pipe_right _156_749 (FStar_List.map (fun branch -> (let _156_748 = (list_elements branch)
in (FStar_All.pipe_right _156_748 (FStar_List.map one_pat)))))))
end
| _75_1341 -> begin
(let _156_750 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_156_750)::[])
end)
end
| _75_1343 -> begin
(let _156_751 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_156_751)::[])
end))))
in (
# 820 "FStar.SMTEncoding.Encode.fst"
let _75_1377 = (match ((let _156_752 = (FStar_Syntax_Subst.compress t)
in _156_752.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 822 "FStar.SMTEncoding.Encode.fst"
let _75_1350 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_75_1350) with
| (binders, c) -> begin
(
# 823 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _75_1362)::(post, _75_1358)::(pats, _75_1354)::[] -> begin
(
# 826 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _156_753 = (lemma_pats pats')
in (binders, pre, post, _156_753)))
end
| _75_1370 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _75_1372 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_75_1377) with
| (binders, pre, post, patterns) -> begin
(
# 834 "FStar.SMTEncoding.Encode.fst"
let _75_1384 = (encode_binders None binders env)
in (match (_75_1384) with
| (vars, guards, env, decls, _75_1383) -> begin
(
# 837 "FStar.SMTEncoding.Encode.fst"
let _75_1397 = (let _156_757 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 838 "FStar.SMTEncoding.Encode.fst"
let _75_1394 = (let _156_756 = (FStar_All.pipe_right branch (FStar_List.map (fun _75_1389 -> (match (_75_1389) with
| (t, _75_1388) -> begin
(encode_term t (
# 838 "FStar.SMTEncoding.Encode.fst"
let _75_1390 = env
in {bindings = _75_1390.bindings; depth = _75_1390.depth; tcenv = _75_1390.tcenv; warn = _75_1390.warn; cache = _75_1390.cache; nolabels = _75_1390.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _75_1390.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _156_756 FStar_List.unzip))
in (match (_75_1394) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _156_757 FStar_List.unzip))
in (match (_75_1397) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _156_760 = (let _156_759 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _156_759 e))
in (_156_760)::p))))
end
| _75_1407 -> begin
(
# 851 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _156_766 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_156_766)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _156_768 = (let _156_767 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _156_767 tl))
in (aux _156_768 vars))
end
| _75_1419 -> begin
pats
end))
in (let _156_769 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _156_769 vars)))
end)
end)
in (
# 858 "FStar.SMTEncoding.Encode.fst"
let env = (
# 858 "FStar.SMTEncoding.Encode.fst"
let _75_1421 = env
in {bindings = _75_1421.bindings; depth = _75_1421.depth; tcenv = _75_1421.tcenv; warn = _75_1421.warn; cache = _75_1421.cache; nolabels = true; use_zfuel_name = _75_1421.use_zfuel_name; encode_non_total_function_typ = _75_1421.encode_non_total_function_typ})
in (
# 859 "FStar.SMTEncoding.Encode.fst"
let _75_1426 = (let _156_770 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _156_770 env))
in (match (_75_1426) with
| (pre, decls'') -> begin
(
# 860 "FStar.SMTEncoding.Encode.fst"
let _75_1429 = (let _156_771 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _156_771 env))
in (match (_75_1429) with
| (post, decls''') -> begin
(
# 861 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _156_776 = (let _156_775 = (let _156_774 = (let _156_773 = (let _156_772 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_156_772, post))
in (FStar_SMTEncoding_Term.mkImp _156_773))
in (pats, vars, _156_774))
in (FStar_SMTEncoding_Term.mkForall _156_775))
in (_156_776, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * labels * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 865 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 866 "FStar.SMTEncoding.Encode.fst"
let _75_1443 = (FStar_Util.fold_map (fun decls x -> (
# 866 "FStar.SMTEncoding.Encode.fst"
let _75_1440 = (encode_term (Prims.fst x) env)
in (match (_75_1440) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_75_1443) with
| (decls, args) -> begin
(let _156_794 = (f args)
in (_156_794, [], decls))
end)))
in (
# 869 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _75_1446 -> (f, [], []))
in (
# 870 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _156_808 = (FStar_List.hd l)
in (FStar_All.pipe_left f _156_808)))
in (
# 871 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _75_8 -> (match (_75_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _75_1457 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 875 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 876 "FStar.SMTEncoding.Encode.fst"
let _75_1477 = (FStar_List.fold_right (fun _75_1465 _75_1469 -> (match ((_75_1465, _75_1469)) with
| ((t, _75_1464), (phis, labs, decls)) -> begin
(
# 878 "FStar.SMTEncoding.Encode.fst"
let _75_1473 = (encode_formula_with_labels t env)
in (match (_75_1473) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end)) l ([], [], []))
in (match (_75_1477) with
| (phis, labs, decls) -> begin
(let _156_833 = (f phis)
in (_156_833, labs, decls))
end)))
in (
# 883 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _75_9 -> (match (_75_9) with
| _75_1484::_75_1482::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 887 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _75_10 -> (match (_75_10) with
| (lhs, _75_1495)::(rhs, _75_1491)::[] -> begin
(
# 889 "FStar.SMTEncoding.Encode.fst"
let _75_1501 = (encode_formula_with_labels rhs env)
in (match (_75_1501) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _75_1504) -> begin
(l1, labs1, decls1)
end
| _75_1508 -> begin
(
# 893 "FStar.SMTEncoding.Encode.fst"
let _75_1512 = (encode_formula_with_labels lhs env)
in (match (_75_1512) with
| (l2, labs2, decls2) -> begin
(let _156_838 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_156_838, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _75_1514 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 898 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _75_11 -> (match (_75_11) with
| (guard, _75_1527)::(_then, _75_1523)::(_else, _75_1519)::[] -> begin
(
# 900 "FStar.SMTEncoding.Encode.fst"
let _75_1533 = (encode_formula_with_labels guard env)
in (match (_75_1533) with
| (g, labs1, decls1) -> begin
(
# 901 "FStar.SMTEncoding.Encode.fst"
let _75_1537 = (encode_formula_with_labels _then env)
in (match (_75_1537) with
| (t, labs2, decls2) -> begin
(
# 902 "FStar.SMTEncoding.Encode.fst"
let _75_1541 = (encode_formula_with_labels _else env)
in (match (_75_1541) with
| (e, labs3, decls3) -> begin
(
# 903 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _75_1544 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 908 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _156_850 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _156_850)))
in (
# 909 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _156_903 = (let _156_859 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _156_859))
in (let _156_902 = (let _156_901 = (let _156_865 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _156_865))
in (let _156_900 = (let _156_899 = (let _156_898 = (let _156_874 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _156_874))
in (let _156_897 = (let _156_896 = (let _156_895 = (let _156_883 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _156_883))
in (_156_895)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_156_896)
in (_156_898)::_156_897))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_156_899)
in (_156_901)::_156_900))
in (_156_903)::_156_902))
in (
# 921 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 923 "FStar.SMTEncoding.Encode.fst"
let _75_1563 = (encode_formula_with_labels phi' env)
in (match (_75_1563) with
| (phi, labs, decls) -> begin
(let _156_906 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_156_906, [], decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 927 "FStar.SMTEncoding.Encode.fst"
let _75_1570 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_75_1570) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _75_1577; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _75_1574; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 931 "FStar.SMTEncoding.Encode.fst"
let _75_1588 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_75_1588) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 935 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _75_1596), _75_1608::(x, _75_1605)::(t, _75_1601)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.has_type_lid) -> begin
(
# 938 "FStar.SMTEncoding.Encode.fst"
let _75_1613 = (encode_term x env)
in (match (_75_1613) with
| (x, decls) -> begin
(
# 939 "FStar.SMTEncoding.Encode.fst"
let _75_1616 = (encode_term t env)
in (match (_75_1616) with
| (t, decls') -> begin
(let _156_907 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_156_907, [], (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _75_1619), _75_1637::_75_1635::(r, _75_1632)::(msg, _75_1628)::(phi, _75_1624)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _156_911 = (let _156_908 = (FStar_Syntax_Subst.compress r)
in _156_908.FStar_Syntax_Syntax.n)
in (let _156_910 = (let _156_909 = (FStar_Syntax_Subst.compress msg)
in _156_909.FStar_Syntax_Syntax.n)
in (_156_911, _156_910)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _75_1645))) -> begin
(
# 945 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _75_1652 -> begin
(fallback phi)
end)
end
| _75_1654 -> begin
(
# 952 "FStar.SMTEncoding.Encode.fst"
let _75_1657 = (encode_term phi env)
in (match (_75_1657) with
| (tt, decls) -> begin
(let _156_912 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_156_912, [], decls))
end))
end))
end
| _75_1659 -> begin
(
# 957 "FStar.SMTEncoding.Encode.fst"
let _75_1662 = (encode_term phi env)
in (match (_75_1662) with
| (tt, decls) -> begin
(let _156_913 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_156_913, [], decls))
end))
end))
in (
# 960 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 961 "FStar.SMTEncoding.Encode.fst"
let _75_1674 = (encode_binders None bs env)
in (match (_75_1674) with
| (vars, guards, env, decls, _75_1673) -> begin
(
# 962 "FStar.SMTEncoding.Encode.fst"
let _75_1687 = (let _156_925 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 963 "FStar.SMTEncoding.Encode.fst"
let _75_1684 = (let _156_924 = (FStar_All.pipe_right p (FStar_List.map (fun _75_1679 -> (match (_75_1679) with
| (t, _75_1678) -> begin
(encode_term t (
# 963 "FStar.SMTEncoding.Encode.fst"
let _75_1680 = env
in {bindings = _75_1680.bindings; depth = _75_1680.depth; tcenv = _75_1680.tcenv; warn = _75_1680.warn; cache = _75_1680.cache; nolabels = _75_1680.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _75_1680.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _156_924 FStar_List.unzip))
in (match (_75_1684) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _156_925 FStar_List.unzip))
in (match (_75_1687) with
| (pats, decls') -> begin
(
# 965 "FStar.SMTEncoding.Encode.fst"
let _75_1691 = (encode_formula_with_labels body env)
in (match (_75_1691) with
| (body, labs, decls'') -> begin
(let _156_926 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _156_926, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 968 "FStar.SMTEncoding.Encode.fst"
let _75_1692 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_927 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _156_927))
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
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _75_1704 -> (match (_75_1704) with
| (l, _75_1703) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_75_1707, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 980 "FStar.SMTEncoding.Encode.fst"
let _75_1717 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_944 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _156_944))
end else begin
()
end
in (
# 983 "FStar.SMTEncoding.Encode.fst"
let _75_1725 = (encode_q_body env vars pats body)
in (match (_75_1725) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _156_947 = (let _156_946 = (let _156_945 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _156_945))
in (FStar_SMTEncoding_Term.mkForall _156_946))
in (_156_947, labs, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 987 "FStar.SMTEncoding.Encode.fst"
let _75_1738 = (encode_q_body env vars pats body)
in (match (_75_1738) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _156_950 = (let _156_949 = (let _156_948 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _156_948))
in (FStar_SMTEncoding_Term.mkExists _156_949))
in (_156_950, labs, decls))
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
let _75_1744 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_75_1744) with
| (asym, a) -> begin
(
# 1004 "FStar.SMTEncoding.Encode.fst"
let _75_1747 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_75_1747) with
| (xsym, x) -> begin
(
# 1005 "FStar.SMTEncoding.Encode.fst"
let _75_1750 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_75_1750) with
| (ysym, y) -> begin
(
# 1006 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 1007 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1008 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _156_993 = (let _156_992 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _156_992))
in (FStar_SMTEncoding_Term.mkApp _156_993))
in (
# 1009 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _156_995 = (let _156_994 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _156_994, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_156_995))
in (let _156_1001 = (let _156_1000 = (let _156_999 = (let _156_998 = (let _156_997 = (let _156_996 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _156_996))
in (FStar_SMTEncoding_Term.mkForall _156_997))
in (_156_998, None))
in FStar_SMTEncoding_Term.Assume (_156_999))
in (_156_1000)::[])
in (vname_decl)::_156_1001))))
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
let prims = (let _156_1161 = (let _156_1010 = (let _156_1009 = (let _156_1008 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1008))
in (quant axy _156_1009))
in (FStar_Syntax_Const.op_Eq, _156_1010))
in (let _156_1160 = (let _156_1159 = (let _156_1017 = (let _156_1016 = (let _156_1015 = (let _156_1014 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _156_1014))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1015))
in (quant axy _156_1016))
in (FStar_Syntax_Const.op_notEq, _156_1017))
in (let _156_1158 = (let _156_1157 = (let _156_1026 = (let _156_1025 = (let _156_1024 = (let _156_1023 = (let _156_1022 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1021 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1022, _156_1021)))
in (FStar_SMTEncoding_Term.mkLT _156_1023))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1024))
in (quant xy _156_1025))
in (FStar_Syntax_Const.op_LT, _156_1026))
in (let _156_1156 = (let _156_1155 = (let _156_1035 = (let _156_1034 = (let _156_1033 = (let _156_1032 = (let _156_1031 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1030 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1031, _156_1030)))
in (FStar_SMTEncoding_Term.mkLTE _156_1032))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1033))
in (quant xy _156_1034))
in (FStar_Syntax_Const.op_LTE, _156_1035))
in (let _156_1154 = (let _156_1153 = (let _156_1044 = (let _156_1043 = (let _156_1042 = (let _156_1041 = (let _156_1040 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1039 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1040, _156_1039)))
in (FStar_SMTEncoding_Term.mkGT _156_1041))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1042))
in (quant xy _156_1043))
in (FStar_Syntax_Const.op_GT, _156_1044))
in (let _156_1152 = (let _156_1151 = (let _156_1053 = (let _156_1052 = (let _156_1051 = (let _156_1050 = (let _156_1049 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1048 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1049, _156_1048)))
in (FStar_SMTEncoding_Term.mkGTE _156_1050))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1051))
in (quant xy _156_1052))
in (FStar_Syntax_Const.op_GTE, _156_1053))
in (let _156_1150 = (let _156_1149 = (let _156_1062 = (let _156_1061 = (let _156_1060 = (let _156_1059 = (let _156_1058 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1057 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1058, _156_1057)))
in (FStar_SMTEncoding_Term.mkSub _156_1059))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1060))
in (quant xy _156_1061))
in (FStar_Syntax_Const.op_Subtraction, _156_1062))
in (let _156_1148 = (let _156_1147 = (let _156_1069 = (let _156_1068 = (let _156_1067 = (let _156_1066 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _156_1066))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1067))
in (quant qx _156_1068))
in (FStar_Syntax_Const.op_Minus, _156_1069))
in (let _156_1146 = (let _156_1145 = (let _156_1078 = (let _156_1077 = (let _156_1076 = (let _156_1075 = (let _156_1074 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1073 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1074, _156_1073)))
in (FStar_SMTEncoding_Term.mkAdd _156_1075))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1076))
in (quant xy _156_1077))
in (FStar_Syntax_Const.op_Addition, _156_1078))
in (let _156_1144 = (let _156_1143 = (let _156_1087 = (let _156_1086 = (let _156_1085 = (let _156_1084 = (let _156_1083 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1082 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1083, _156_1082)))
in (FStar_SMTEncoding_Term.mkMul _156_1084))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1085))
in (quant xy _156_1086))
in (FStar_Syntax_Const.op_Multiply, _156_1087))
in (let _156_1142 = (let _156_1141 = (let _156_1096 = (let _156_1095 = (let _156_1094 = (let _156_1093 = (let _156_1092 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1091 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1092, _156_1091)))
in (FStar_SMTEncoding_Term.mkDiv _156_1093))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1094))
in (quant xy _156_1095))
in (FStar_Syntax_Const.op_Division, _156_1096))
in (let _156_1140 = (let _156_1139 = (let _156_1105 = (let _156_1104 = (let _156_1103 = (let _156_1102 = (let _156_1101 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1100 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1101, _156_1100)))
in (FStar_SMTEncoding_Term.mkMod _156_1102))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1103))
in (quant xy _156_1104))
in (FStar_Syntax_Const.op_Modulus, _156_1105))
in (let _156_1138 = (let _156_1137 = (let _156_1114 = (let _156_1113 = (let _156_1112 = (let _156_1111 = (let _156_1110 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _156_1109 = (FStar_SMTEncoding_Term.unboxBool y)
in (_156_1110, _156_1109)))
in (FStar_SMTEncoding_Term.mkAnd _156_1111))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1112))
in (quant xy _156_1113))
in (FStar_Syntax_Const.op_And, _156_1114))
in (let _156_1136 = (let _156_1135 = (let _156_1123 = (let _156_1122 = (let _156_1121 = (let _156_1120 = (let _156_1119 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _156_1118 = (FStar_SMTEncoding_Term.unboxBool y)
in (_156_1119, _156_1118)))
in (FStar_SMTEncoding_Term.mkOr _156_1120))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1121))
in (quant xy _156_1122))
in (FStar_Syntax_Const.op_Or, _156_1123))
in (let _156_1134 = (let _156_1133 = (let _156_1130 = (let _156_1129 = (let _156_1128 = (let _156_1127 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _156_1127))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1128))
in (quant qx _156_1129))
in (FStar_Syntax_Const.op_Negation, _156_1130))
in (_156_1133)::[])
in (_156_1135)::_156_1134))
in (_156_1137)::_156_1136))
in (_156_1139)::_156_1138))
in (_156_1141)::_156_1140))
in (_156_1143)::_156_1142))
in (_156_1145)::_156_1144))
in (_156_1147)::_156_1146))
in (_156_1149)::_156_1148))
in (_156_1151)::_156_1150))
in (_156_1153)::_156_1152))
in (_156_1155)::_156_1154))
in (_156_1157)::_156_1156))
in (_156_1159)::_156_1158))
in (_156_1161)::_156_1160))
in (
# 1032 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _156_1193 = (FStar_All.pipe_right prims (FStar_List.filter (fun _75_1770 -> (match (_75_1770) with
| (l', _75_1769) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _156_1193 (FStar_List.collect (fun _75_1774 -> (match (_75_1774) with
| (_75_1772, b) -> begin
(b v)
end))))))
in (
# 1034 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _75_1780 -> (match (_75_1780) with
| (l', _75_1779) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1039 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1040 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1041 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1043 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1044 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1046 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun _75_1786 tt -> (
# 1047 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _156_1225 = (let _156_1216 = (let _156_1215 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_156_1215, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_156_1216))
in (let _156_1224 = (let _156_1223 = (let _156_1222 = (let _156_1221 = (let _156_1220 = (let _156_1219 = (let _156_1218 = (let _156_1217 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _156_1217))
in (FStar_SMTEncoding_Term.mkImp _156_1218))
in (((typing_pred)::[])::[], (xx)::[], _156_1219))
in (mkForall_fuel _156_1220))
in (_156_1221, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1222))
in (_156_1223)::[])
in (_156_1225)::_156_1224))))
in (
# 1050 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun _75_1791 tt -> (
# 1051 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1052 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1053 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _156_1246 = (let _156_1235 = (let _156_1234 = (let _156_1233 = (let _156_1232 = (let _156_1231 = (let _156_1230 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _156_1230))
in (FStar_SMTEncoding_Term.mkImp _156_1231))
in (((typing_pred)::[])::[], (xx)::[], _156_1232))
in (mkForall_fuel _156_1233))
in (_156_1234, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1235))
in (let _156_1245 = (let _156_1244 = (let _156_1243 = (let _156_1242 = (let _156_1241 = (let _156_1240 = (let _156_1237 = (let _156_1236 = (FStar_SMTEncoding_Term.boxBool b)
in (_156_1236)::[])
in (_156_1237)::[])
in (let _156_1239 = (let _156_1238 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _156_1238 tt))
in (_156_1240, (bb)::[], _156_1239)))
in (FStar_SMTEncoding_Term.mkForall _156_1241))
in (_156_1242, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_156_1243))
in (_156_1244)::[])
in (_156_1246)::_156_1245))))))
in (
# 1056 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun _75_1798 tt -> (
# 1057 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1058 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1059 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1060 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1061 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1062 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1063 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _156_1258 = (let _156_1257 = (let _156_1256 = (let _156_1255 = (let _156_1254 = (let _156_1253 = (FStar_SMTEncoding_Term.boxInt a)
in (let _156_1252 = (let _156_1251 = (FStar_SMTEncoding_Term.boxInt b)
in (_156_1251)::[])
in (_156_1253)::_156_1252))
in (tt)::_156_1254)
in (tt)::_156_1255)
in ("Prims.Precedes", _156_1256))
in (FStar_SMTEncoding_Term.mkApp _156_1257))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _156_1258))
in (
# 1064 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _156_1259 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _156_1259))
in (let _156_1301 = (let _156_1265 = (let _156_1264 = (let _156_1263 = (let _156_1262 = (let _156_1261 = (let _156_1260 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _156_1260))
in (FStar_SMTEncoding_Term.mkImp _156_1261))
in (((typing_pred)::[])::[], (xx)::[], _156_1262))
in (mkForall_fuel _156_1263))
in (_156_1264, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1265))
in (let _156_1300 = (let _156_1299 = (let _156_1273 = (let _156_1272 = (let _156_1271 = (let _156_1270 = (let _156_1267 = (let _156_1266 = (FStar_SMTEncoding_Term.boxInt b)
in (_156_1266)::[])
in (_156_1267)::[])
in (let _156_1269 = (let _156_1268 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _156_1268 tt))
in (_156_1270, (bb)::[], _156_1269)))
in (FStar_SMTEncoding_Term.mkForall _156_1271))
in (_156_1272, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_156_1273))
in (let _156_1298 = (let _156_1297 = (let _156_1296 = (let _156_1295 = (let _156_1294 = (let _156_1293 = (let _156_1292 = (let _156_1291 = (let _156_1290 = (let _156_1289 = (let _156_1288 = (let _156_1287 = (let _156_1276 = (let _156_1275 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1274 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_156_1275, _156_1274)))
in (FStar_SMTEncoding_Term.mkGT _156_1276))
in (let _156_1286 = (let _156_1285 = (let _156_1279 = (let _156_1278 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _156_1277 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_156_1278, _156_1277)))
in (FStar_SMTEncoding_Term.mkGTE _156_1279))
in (let _156_1284 = (let _156_1283 = (let _156_1282 = (let _156_1281 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _156_1280 = (FStar_SMTEncoding_Term.unboxInt x)
in (_156_1281, _156_1280)))
in (FStar_SMTEncoding_Term.mkLT _156_1282))
in (_156_1283)::[])
in (_156_1285)::_156_1284))
in (_156_1287)::_156_1286))
in (typing_pred_y)::_156_1288)
in (typing_pred)::_156_1289)
in (FStar_SMTEncoding_Term.mk_and_l _156_1290))
in (_156_1291, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _156_1292))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _156_1293))
in (mkForall_fuel _156_1294))
in (_156_1295, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_156_1296))
in (_156_1297)::[])
in (_156_1299)::_156_1298))
in (_156_1301)::_156_1300)))))))))))
in (
# 1076 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun _75_1810 tt -> (let _156_1310 = (let _156_1309 = (let _156_1308 = (let _156_1307 = (let _156_1306 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _156_1306))
in (FStar_SMTEncoding_Term.mkEq _156_1307))
in (_156_1308, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_156_1309))
in (_156_1310)::[]))
in (
# 1078 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun _75_1814 tt -> (
# 1079 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1080 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1081 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _156_1331 = (let _156_1320 = (let _156_1319 = (let _156_1318 = (let _156_1317 = (let _156_1316 = (let _156_1315 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _156_1315))
in (FStar_SMTEncoding_Term.mkImp _156_1316))
in (((typing_pred)::[])::[], (xx)::[], _156_1317))
in (mkForall_fuel _156_1318))
in (_156_1319, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1320))
in (let _156_1330 = (let _156_1329 = (let _156_1328 = (let _156_1327 = (let _156_1326 = (let _156_1325 = (let _156_1322 = (let _156_1321 = (FStar_SMTEncoding_Term.boxString b)
in (_156_1321)::[])
in (_156_1322)::[])
in (let _156_1324 = (let _156_1323 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _156_1323 tt))
in (_156_1325, (bb)::[], _156_1324)))
in (FStar_SMTEncoding_Term.mkForall _156_1326))
in (_156_1327, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_156_1328))
in (_156_1329)::[])
in (_156_1331)::_156_1330))))))
in (
# 1084 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun reft_name _75_1822 -> (
# 1085 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1086 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1087 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1088 "FStar.SMTEncoding.Encode.fst"
let refa = (let _156_1338 = (let _156_1337 = (let _156_1336 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_156_1336)::[])
in (reft_name, _156_1337))
in (FStar_SMTEncoding_Term.mkApp _156_1338))
in (
# 1089 "FStar.SMTEncoding.Encode.fst"
let refb = (let _156_1341 = (let _156_1340 = (let _156_1339 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_156_1339)::[])
in (reft_name, _156_1340))
in (FStar_SMTEncoding_Term.mkApp _156_1341))
in (
# 1090 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1091 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _156_1360 = (let _156_1347 = (let _156_1346 = (let _156_1345 = (let _156_1344 = (let _156_1343 = (let _156_1342 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _156_1342))
in (FStar_SMTEncoding_Term.mkImp _156_1343))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _156_1344))
in (mkForall_fuel _156_1345))
in (_156_1346, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1347))
in (let _156_1359 = (let _156_1358 = (let _156_1357 = (let _156_1356 = (let _156_1355 = (let _156_1354 = (let _156_1353 = (let _156_1352 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _156_1351 = (let _156_1350 = (let _156_1349 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _156_1348 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_156_1349, _156_1348)))
in (FStar_SMTEncoding_Term.mkEq _156_1350))
in (_156_1352, _156_1351)))
in (FStar_SMTEncoding_Term.mkImp _156_1353))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _156_1354))
in (mkForall_fuel' 2 _156_1355))
in (_156_1356, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_156_1357))
in (_156_1358)::[])
in (_156_1360)::_156_1359))))))))))
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun _75_1832 false_tm -> (
# 1096 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _156_1367 = (let _156_1366 = (let _156_1365 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_156_1365, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1366))
in (_156_1367)::[])))
in (
# 1098 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun conj _75_1838 -> (
# 1099 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1100 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1101 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1102 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1103 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1374 = (let _156_1373 = (let _156_1372 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_156_1372)::[])
in ("Valid", _156_1373))
in (FStar_SMTEncoding_Term.mkApp _156_1374))
in (
# 1104 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1105 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _156_1381 = (let _156_1380 = (let _156_1379 = (let _156_1378 = (let _156_1377 = (let _156_1376 = (let _156_1375 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_156_1375, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1376))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1377))
in (FStar_SMTEncoding_Term.mkForall _156_1378))
in (_156_1379, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1380))
in (_156_1381)::[])))))))))
in (
# 1107 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun disj _75_1849 -> (
# 1108 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1109 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1110 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1112 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1388 = (let _156_1387 = (let _156_1386 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_156_1386)::[])
in ("Valid", _156_1387))
in (FStar_SMTEncoding_Term.mkApp _156_1388))
in (
# 1113 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1114 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _156_1395 = (let _156_1394 = (let _156_1393 = (let _156_1392 = (let _156_1391 = (let _156_1390 = (let _156_1389 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_156_1389, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1390))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1391))
in (FStar_SMTEncoding_Term.mkForall _156_1392))
in (_156_1393, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1394))
in (_156_1395)::[])))))))))
in (
# 1116 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun eq2 tt -> (
# 1117 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1118 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1119 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1120 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1121 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1122 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1123 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1125 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1402 = (let _156_1401 = (let _156_1400 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_156_1400)::[])
in ("Valid", _156_1401))
in (FStar_SMTEncoding_Term.mkApp _156_1402))
in (let _156_1409 = (let _156_1408 = (let _156_1407 = (let _156_1406 = (let _156_1405 = (let _156_1404 = (let _156_1403 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_156_1403, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1404))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _156_1405))
in (FStar_SMTEncoding_Term.mkForall _156_1406))
in (_156_1407, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1408))
in (_156_1409)::[])))))))))))
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun imp tt -> (
# 1128 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1129 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1130 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1131 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1132 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1416 = (let _156_1415 = (let _156_1414 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_156_1414)::[])
in ("Valid", _156_1415))
in (FStar_SMTEncoding_Term.mkApp _156_1416))
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1134 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _156_1423 = (let _156_1422 = (let _156_1421 = (let _156_1420 = (let _156_1419 = (let _156_1418 = (let _156_1417 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_156_1417, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1418))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1419))
in (FStar_SMTEncoding_Term.mkForall _156_1420))
in (_156_1421, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1422))
in (_156_1423)::[])))))))))
in (
# 1136 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun iff tt -> (
# 1137 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1138 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1139 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1140 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1141 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1430 = (let _156_1429 = (let _156_1428 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_156_1428)::[])
in ("Valid", _156_1429))
in (FStar_SMTEncoding_Term.mkApp _156_1430))
in (
# 1142 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1143 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _156_1437 = (let _156_1436 = (let _156_1435 = (let _156_1434 = (let _156_1433 = (let _156_1432 = (let _156_1431 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_156_1431, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1432))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1433))
in (FStar_SMTEncoding_Term.mkForall _156_1434))
in (_156_1435, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1436))
in (_156_1437)::[])))))))))
in (
# 1145 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun for_all tt -> (
# 1146 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1148 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1149 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1150 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1151 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1152 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1444 = (let _156_1443 = (let _156_1442 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_156_1442)::[])
in ("Valid", _156_1443))
in (FStar_SMTEncoding_Term.mkApp _156_1444))
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _156_1447 = (let _156_1446 = (let _156_1445 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_156_1445)::[])
in ("Valid", _156_1446))
in (FStar_SMTEncoding_Term.mkApp _156_1447))
in (let _156_1461 = (let _156_1460 = (let _156_1459 = (let _156_1458 = (let _156_1457 = (let _156_1456 = (let _156_1455 = (let _156_1454 = (let _156_1453 = (let _156_1449 = (let _156_1448 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_156_1448)::[])
in (_156_1449)::[])
in (let _156_1452 = (let _156_1451 = (let _156_1450 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_156_1450, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _156_1451))
in (_156_1453, (xx)::[], _156_1452)))
in (FStar_SMTEncoding_Term.mkForall _156_1454))
in (_156_1455, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1456))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1457))
in (FStar_SMTEncoding_Term.mkForall _156_1458))
in (_156_1459, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1460))
in (_156_1461)::[]))))))))))
in (
# 1155 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun for_some tt -> (
# 1156 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1157 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1158 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1159 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1160 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1161 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1162 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1468 = (let _156_1467 = (let _156_1466 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_156_1466)::[])
in ("Valid", _156_1467))
in (FStar_SMTEncoding_Term.mkApp _156_1468))
in (
# 1163 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _156_1471 = (let _156_1470 = (let _156_1469 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_156_1469)::[])
in ("Valid", _156_1470))
in (FStar_SMTEncoding_Term.mkApp _156_1471))
in (let _156_1485 = (let _156_1484 = (let _156_1483 = (let _156_1482 = (let _156_1481 = (let _156_1480 = (let _156_1479 = (let _156_1478 = (let _156_1477 = (let _156_1473 = (let _156_1472 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_156_1472)::[])
in (_156_1473)::[])
in (let _156_1476 = (let _156_1475 = (let _156_1474 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_156_1474, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _156_1475))
in (_156_1477, (xx)::[], _156_1476)))
in (FStar_SMTEncoding_Term.mkExists _156_1478))
in (_156_1479, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1480))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1481))
in (FStar_SMTEncoding_Term.mkForall _156_1482))
in (_156_1483, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1484))
in (_156_1485)::[]))))))))))
in (
# 1165 "FStar.SMTEncoding.Encode.fst"
let mk_range_of_interp = (fun range_of tt -> (
# 1166 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1167 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1168 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1169 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1170 "FStar.SMTEncoding.Encode.fst"
let range_of_ty = (FStar_SMTEncoding_Term.mkApp (range_of, (a)::(b)::[]))
in (let _156_1494 = (let _156_1493 = (let _156_1492 = (let _156_1491 = (let _156_1490 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_of_ty)
in (((range_of_ty)::[])::[], (aa)::(bb)::[], _156_1490))
in (FStar_SMTEncoding_Term.mkForall _156_1491))
in (_156_1492, Some ("Range_const typing")))
in FStar_SMTEncoding_Term.Assume (_156_1493))
in (_156_1494)::[])))))))
in (
# 1173 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_of_lid, mk_range_of_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _75_1928 -> (match (_75_1928) with
| (l, _75_1927) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_75_1931, f) -> begin
(f s tt)
end))))))))))))))))))))))

# 1195 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1196 "FStar.SMTEncoding.Encode.fst"
let _75_1937 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _156_1643 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _156_1643))
end else begin
()
end
in (
# 1199 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1202 "FStar.SMTEncoding.Encode.fst"
let _75_1945 = (encode_sigelt' env se)
in (match (_75_1945) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _156_1646 = (let _156_1645 = (let _156_1644 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_156_1644))
in (_156_1645)::[])
in (_156_1646, e))
end
| _75_1948 -> begin
(let _156_1653 = (let _156_1652 = (let _156_1648 = (let _156_1647 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_156_1647))
in (_156_1648)::g)
in (let _156_1651 = (let _156_1650 = (let _156_1649 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_156_1649))
in (_156_1650)::[])
in (FStar_List.append _156_1652 _156_1651)))
in (_156_1653, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1208 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1214 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1215 "FStar.SMTEncoding.Encode.fst"
let tt = (norm env t)
in (
# 1221 "FStar.SMTEncoding.Encode.fst"
let _75_1961 = (encode_free_var env lid t tt quals)
in (match (_75_1961) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _156_1667 = (let _156_1666 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _156_1666))
in (_156_1667, env))
end else begin
(decls, env)
end
end))))
in (
# 1227 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _75_1968 lb -> (match (_75_1968) with
| (decls, env) -> begin
(
# 1229 "FStar.SMTEncoding.Encode.fst"
let _75_1972 = (let _156_1676 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _156_1676 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_75_1972) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _75_1990, _75_1992, _75_1994, _75_1996) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1241 "FStar.SMTEncoding.Encode.fst"
let _75_2002 = (new_term_constant_and_tok_from_lid env lid)
in (match (_75_2002) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _75_2005, t, quals, _75_2009) -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _75_12 -> (match (_75_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _75_2021 -> begin
false
end)))) || env.tcenv.FStar_TypeChecker_Env.is_iface) then begin
(
# 1246 "FStar.SMTEncoding.Encode.fst"
let _75_2024 = (encode_top_level_val env lid t quals)
in (match (_75_2024) with
| (decls, env) -> begin
(
# 1247 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1248 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _156_1679 = (let _156_1678 = (primitive_type_axioms lid tname tsym)
in (FStar_List.append decls _156_1678))
in (_156_1679, env))))
end))
end else begin
([], env)
end
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _75_2030, _75_2032) -> begin
(
# 1255 "FStar.SMTEncoding.Encode.fst"
let _75_2037 = (encode_formula f env)
in (match (_75_2037) with
| (f, decls) -> begin
(
# 1256 "FStar.SMTEncoding.Encode.fst"
let g = (let _156_1684 = (let _156_1683 = (let _156_1682 = (let _156_1681 = (let _156_1680 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _156_1680))
in Some (_156_1681))
in (f, _156_1682))
in FStar_SMTEncoding_Term.Assume (_156_1683))
in (_156_1684)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _75_2042, _75_2044) when (FStar_All.pipe_right (Prims.snd lbs) (FStar_Util.for_some (fun lb -> (let _156_1686 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (should_skip _156_1686))))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_75_2049, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _75_2057; FStar_Syntax_Syntax.lbtyp = _75_2055; FStar_Syntax_Syntax.lbeff = _75_2053; FStar_Syntax_Syntax.lbdef = _75_2051}::[]), _75_2064, _75_2066, _75_2068) when (FStar_Ident.lid_equals b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1263 "FStar.SMTEncoding.Encode.fst"
let _75_2074 = (new_term_constant_and_tok_from_lid env b2t)
in (match (_75_2074) with
| (tname, ttok, env) -> begin
(
# 1264 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1265 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1266 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _156_1689 = (let _156_1688 = (let _156_1687 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_156_1687)::[])
in ("Valid", _156_1688))
in (FStar_SMTEncoding_Term.mkApp _156_1689))
in (
# 1267 "FStar.SMTEncoding.Encode.fst"
let decls = (let _156_1697 = (let _156_1696 = (let _156_1695 = (let _156_1694 = (let _156_1693 = (let _156_1692 = (let _156_1691 = (let _156_1690 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _156_1690))
in (FStar_SMTEncoding_Term.mkEq _156_1691))
in (((valid_b2t_x)::[])::[], (xx)::[], _156_1692))
in (FStar_SMTEncoding_Term.mkForall _156_1693))
in (_156_1694, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_156_1695))
in (_156_1696)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_156_1697)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_75_2080, _75_2082, _75_2084, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _75_13 -> (match (_75_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _75_2094 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _75_2100, _75_2102, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _75_14 -> (match (_75_14) with
| FStar_Syntax_Syntax.Projector (_75_2108) -> begin
true
end
| _75_2111 -> begin
false
end)))) -> begin
(
# 1281 "FStar.SMTEncoding.Encode.fst"
let l = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (match ((try_lookup_free_var env l)) with
| Some (_75_2114) -> begin
([], env)
end
| None -> begin
(
# 1286 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _75_2122, _75_2124, quals) -> begin
(
# 1292 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1293 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1294 "FStar.SMTEncoding.Encode.fst"
let _75_2136 = (FStar_Util.first_N nbinders formals)
in (match (_75_2136) with
| (formals, extra_formals) -> begin
(
# 1295 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _75_2140 _75_2144 -> (match ((_75_2140, _75_2144)) with
| ((formal, _75_2139), (binder, _75_2143)) -> begin
(let _156_1711 = (let _156_1710 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _156_1710))
in FStar_Syntax_Syntax.NT (_156_1711))
end)) formals binders)
in (
# 1296 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _156_1715 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _75_2148 -> (match (_75_2148) with
| (x, i) -> begin
(let _156_1714 = (
# 1296 "FStar.SMTEncoding.Encode.fst"
let _75_2149 = x
in (let _156_1713 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _75_2149.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _75_2149.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_1713}))
in (_156_1714, i))
end))))
in (FStar_All.pipe_right _156_1715 FStar_Syntax_Util.name_binders))
in (
# 1297 "FStar.SMTEncoding.Encode.fst"
let body = (let _156_1722 = (FStar_Syntax_Subst.compress body)
in (let _156_1721 = (let _156_1716 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _156_1716))
in (let _156_1720 = (let _156_1719 = (let _156_1718 = (FStar_Syntax_Subst.subst subst t)
in _156_1718.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _156_1717 -> Some (_156_1717)) _156_1719))
in (FStar_Syntax_Syntax.extend_app_n _156_1722 _156_1721 _156_1720 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1300 "FStar.SMTEncoding.Encode.fst"
let rec destruct_bound_function = (fun flid t_norm e -> (match ((let _156_1729 = (FStar_Syntax_Util.unascribe e)
in _156_1729.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1303 "FStar.SMTEncoding.Encode.fst"
let _75_2165 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_75_2165) with
| (binders, body, opening) -> begin
(match ((let _156_1730 = (FStar_Syntax_Subst.compress t_norm)
in _156_1730.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1306 "FStar.SMTEncoding.Encode.fst"
let _75_2172 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_75_2172) with
| (formals, c) -> begin
(
# 1307 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1308 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1309 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1311 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1312 "FStar.SMTEncoding.Encode.fst"
let _75_2179 = (FStar_Util.first_N nformals binders)
in (match (_75_2179) with
| (bs0, rest) -> begin
(
# 1313 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1314 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _75_2183 _75_2187 -> (match ((_75_2183, _75_2187)) with
| ((b, _75_2182), (x, _75_2186)) -> begin
(let _156_1734 = (let _156_1733 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _156_1733))
in FStar_Syntax_Syntax.NT (_156_1734))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1316 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1319 "FStar.SMTEncoding.Encode.fst"
let _75_2193 = (eta_expand binders formals body tres)
in (match (_75_2193) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| _75_2195 -> begin
(let _156_1737 = (let _156_1736 = (FStar_Syntax_Print.term_to_string e)
in (let _156_1735 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _156_1736 _156_1735)))
in (FStar_All.failwith _156_1737))
end)
end))
end
| _75_2197 -> begin
(match ((let _156_1738 = (FStar_Syntax_Subst.compress t_norm)
in _156_1738.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1329 "FStar.SMTEncoding.Encode.fst"
let _75_2204 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_75_2204) with
| (formals, c) -> begin
(
# 1330 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1331 "FStar.SMTEncoding.Encode.fst"
let _75_2208 = (eta_expand [] formals e tres)
in (match (_75_2208) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _75_2210 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _75_2212 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1339 "FStar.SMTEncoding.Encode.fst"
let _75_2238 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _75_2225 lb -> (match (_75_2225) with
| (toks, typs, decls, env) -> begin
(
# 1341 "FStar.SMTEncoding.Encode.fst"
let _75_2227 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1342 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1343 "FStar.SMTEncoding.Encode.fst"
let _75_2233 = (let _156_1743 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _156_1743 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_75_2233) with
| (tok, decl, env) -> begin
(let _156_1746 = (let _156_1745 = (let _156_1744 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_156_1744, tok))
in (_156_1745)::toks)
in (_156_1746, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_75_2238) with
| (toks, typs, decls, env) -> begin
(
# 1345 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1346 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1347 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _75_15 -> (match (_75_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _75_2245 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _156_1749 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _156_1749)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _75_2255; FStar_Syntax_Syntax.lbunivs = _75_2253; FStar_Syntax_Syntax.lbtyp = _75_2251; FStar_Syntax_Syntax.lbeff = _75_2249; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(
# 1354 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1355 "FStar.SMTEncoding.Encode.fst"
let _75_2274 = (destruct_bound_function flid t_norm e)
in (match (_75_2274) with
| (binders, body, _75_2271, _75_2273) -> begin
(
# 1356 "FStar.SMTEncoding.Encode.fst"
let _75_2281 = (encode_binders None binders env)
in (match (_75_2281) with
| (vars, guards, env', binder_decls, _75_2280) -> begin
(
# 1357 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _75_2284 -> begin
(let _156_1751 = (let _156_1750 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _156_1750))
in (FStar_SMTEncoding_Term.mkApp _156_1751))
end)
in (
# 1358 "FStar.SMTEncoding.Encode.fst"
let _75_2290 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _156_1753 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _156_1752 = (encode_formula body env')
in (_156_1753, _156_1752)))
end else begin
(let _156_1754 = (encode_term body env')
in (app, _156_1754))
end
in (match (_75_2290) with
| (app, (body, decls2)) -> begin
(
# 1362 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _156_1763 = (let _156_1762 = (let _156_1759 = (let _156_1758 = (let _156_1757 = (let _156_1756 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _156_1755 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_156_1756, _156_1755)))
in (FStar_SMTEncoding_Term.mkImp _156_1757))
in (((app)::[])::[], vars, _156_1758))
in (FStar_SMTEncoding_Term.mkForall _156_1759))
in (let _156_1761 = (let _156_1760 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_156_1760))
in (_156_1762, _156_1761)))
in FStar_SMTEncoding_Term.Assume (_156_1763))
in (let _156_1765 = (let _156_1764 = (primitive_type_axioms flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _156_1764))
in (_156_1765, env)))
end)))
end))
end)))
end
| _75_2293 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1368 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _156_1766 = (varops.fresh "fuel")
in (_156_1766, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1369 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1370 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1371 "FStar.SMTEncoding.Encode.fst"
let _75_2310 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _75_2299 _75_2304 -> (match ((_75_2299, _75_2304)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(
# 1372 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1373 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1374 "FStar.SMTEncoding.Encode.fst"
let env = (let _156_1771 = (let _156_1770 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _156_1769 -> Some (_156_1769)) _156_1770))
in (push_free_var env flid gtok _156_1771))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_75_2310) with
| (gtoks, env) -> begin
(
# 1376 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1377 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _75_2319 t_norm _75_2330 -> (match ((_75_2319, _75_2330)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _75_2329; FStar_Syntax_Syntax.lbunivs = _75_2327; FStar_Syntax_Syntax.lbtyp = _75_2325; FStar_Syntax_Syntax.lbeff = _75_2323; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1378 "FStar.SMTEncoding.Encode.fst"
let _75_2335 = (destruct_bound_function flid t_norm e)
in (match (_75_2335) with
| (binders, body, formals, tres) -> begin
(
# 1379 "FStar.SMTEncoding.Encode.fst"
let _75_2342 = (encode_binders None binders env)
in (match (_75_2342) with
| (vars, guards, env', binder_decls, _75_2341) -> begin
(
# 1380 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _156_1782 = (let _156_1781 = (let _156_1780 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_156_1780)
in (g, _156_1781, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_156_1782))
in (
# 1381 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1382 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1383 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1384 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1385 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _156_1785 = (let _156_1784 = (let _156_1783 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_156_1783)::vars_tm)
in (g, _156_1784))
in (FStar_SMTEncoding_Term.mkApp _156_1785))
in (
# 1386 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _156_1788 = (let _156_1787 = (let _156_1786 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_156_1786)::vars_tm)
in (g, _156_1787))
in (FStar_SMTEncoding_Term.mkApp _156_1788))
in (
# 1387 "FStar.SMTEncoding.Encode.fst"
let _75_2352 = (encode_term body env')
in (match (_75_2352) with
| (body_tm, decls2) -> begin
(
# 1388 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _156_1797 = (let _156_1796 = (let _156_1793 = (let _156_1792 = (let _156_1791 = (let _156_1790 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _156_1789 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_156_1790, _156_1789)))
in (FStar_SMTEncoding_Term.mkImp _156_1791))
in (((gsapp)::[])::[], (fuel)::vars, _156_1792))
in (FStar_SMTEncoding_Term.mkForall _156_1793))
in (let _156_1795 = (let _156_1794 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_156_1794))
in (_156_1796, _156_1795)))
in FStar_SMTEncoding_Term.Assume (_156_1797))
in (
# 1390 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _156_1801 = (let _156_1800 = (let _156_1799 = (let _156_1798 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _156_1798))
in (FStar_SMTEncoding_Term.mkForall _156_1799))
in (_156_1800, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_156_1801))
in (
# 1392 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _156_1810 = (let _156_1809 = (let _156_1808 = (let _156_1807 = (let _156_1806 = (let _156_1805 = (let _156_1804 = (let _156_1803 = (let _156_1802 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_156_1802)::vars_tm)
in (g, _156_1803))
in (FStar_SMTEncoding_Term.mkApp _156_1804))
in (gsapp, _156_1805))
in (FStar_SMTEncoding_Term.mkEq _156_1806))
in (((gsapp)::[])::[], (fuel)::vars, _156_1807))
in (FStar_SMTEncoding_Term.mkForall _156_1808))
in (_156_1809, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_156_1810))
in (
# 1394 "FStar.SMTEncoding.Encode.fst"
let _75_2375 = (
# 1395 "FStar.SMTEncoding.Encode.fst"
let _75_2362 = (encode_binders None formals env0)
in (match (_75_2362) with
| (vars, v_guards, env, binder_decls, _75_2361) -> begin
(
# 1396 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1397 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1398 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1399 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _156_1811 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _156_1811 ((fuel)::vars)))
in (let _156_1815 = (let _156_1814 = (let _156_1813 = (let _156_1812 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _156_1812))
in (FStar_SMTEncoding_Term.mkForall _156_1813))
in (_156_1814, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_156_1815)))
in (
# 1402 "FStar.SMTEncoding.Encode.fst"
let _75_2372 = (
# 1403 "FStar.SMTEncoding.Encode.fst"
let _75_2369 = (encode_term_pred None tres env gapp)
in (match (_75_2369) with
| (g_typing, d3) -> begin
(let _156_1823 = (let _156_1822 = (let _156_1821 = (let _156_1820 = (let _156_1819 = (let _156_1818 = (let _156_1817 = (let _156_1816 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_156_1816, g_typing))
in (FStar_SMTEncoding_Term.mkImp _156_1817))
in (((gapp)::[])::[], (fuel)::vars, _156_1818))
in (FStar_SMTEncoding_Term.mkForall _156_1819))
in (_156_1820, None))
in FStar_SMTEncoding_Term.Assume (_156_1821))
in (_156_1822)::[])
in (d3, _156_1823))
end))
in (match (_75_2372) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_75_2375) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1407 "FStar.SMTEncoding.Encode.fst"
let _75_2391 = (let _156_1826 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _75_2379 _75_2383 -> (match ((_75_2379, _75_2383)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1408 "FStar.SMTEncoding.Encode.fst"
let _75_2387 = (encode_one_binding env0 gtok ty bs)
in (match (_75_2387) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _156_1826))
in (match (_75_2391) with
| (decls, eqns, env0) -> begin
(
# 1410 "FStar.SMTEncoding.Encode.fst"
let _75_2400 = (let _156_1828 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _156_1828 (FStar_List.partition (fun _75_16 -> (match (_75_16) with
| FStar_SMTEncoding_Term.DeclFun (_75_2394) -> begin
true
end
| _75_2397 -> begin
false
end)))))
in (match (_75_2400) with
| (prefix_decls, rest) -> begin
(
# 1413 "FStar.SMTEncoding.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _75_2211 -> (match (_75_2211) with
| Let_rec_unencodeable -> begin
(
# 1416 "FStar.SMTEncoding.Encode.fst"
let msg = (let _156_1831 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _156_1831 (FStar_String.concat " and ")))
in (
# 1417 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _75_2404, _75_2406, _75_2408) -> begin
(
# 1422 "FStar.SMTEncoding.Encode.fst"
let _75_2413 = (encode_signature env ses)
in (match (_75_2413) with
| (g, env) -> begin
(
# 1423 "FStar.SMTEncoding.Encode.fst"
let _75_2425 = (FStar_All.pipe_right g (FStar_List.partition (fun _75_17 -> (match (_75_17) with
| FStar_SMTEncoding_Term.Assume (_75_2416, Some ("inversion axiom")) -> begin
false
end
| _75_2422 -> begin
true
end))))
in (match (_75_2425) with
| (g', inversions) -> begin
(
# 1426 "FStar.SMTEncoding.Encode.fst"
let _75_2434 = (FStar_All.pipe_right g' (FStar_List.partition (fun _75_18 -> (match (_75_18) with
| FStar_SMTEncoding_Term.DeclFun (_75_2428) -> begin
true
end
| _75_2431 -> begin
false
end))))
in (match (_75_2434) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _75_2437, tps, k, _75_2441, datas, quals, _75_2445) -> begin
(
# 1432 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _75_19 -> (match (_75_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _75_2452 -> begin
false
end))))
in (
# 1433 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1435 "FStar.SMTEncoding.Encode.fst"
let _75_2462 = c
in (match (_75_2462) with
| (name, args, _75_2459, _75_2461) -> begin
(let _156_1839 = (let _156_1838 = (let _156_1837 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _156_1837, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_156_1838))
in (_156_1839)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1439 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _156_1845 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _156_1845 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1443 "FStar.SMTEncoding.Encode.fst"
let _75_2469 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_75_2469) with
| (xxsym, xx) -> begin
(
# 1444 "FStar.SMTEncoding.Encode.fst"
let _75_2505 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _75_2472 l -> (match (_75_2472) with
| (out, decls) -> begin
(
# 1445 "FStar.SMTEncoding.Encode.fst"
let _75_2477 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_75_2477) with
| (_75_2475, data_t) -> begin
(
# 1446 "FStar.SMTEncoding.Encode.fst"
let _75_2480 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_75_2480) with
| (args, res) -> begin
(
# 1447 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _156_1848 = (FStar_Syntax_Subst.compress res)
in _156_1848.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_75_2482, indices) -> begin
indices
end
| _75_2487 -> begin
[]
end)
in (
# 1450 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _75_2493 -> (match (_75_2493) with
| (x, _75_2492) -> begin
(let _156_1853 = (let _156_1852 = (let _156_1851 = (mk_term_projector_name l x)
in (_156_1851, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _156_1852))
in (push_term_var env x _156_1853))
end)) env))
in (
# 1453 "FStar.SMTEncoding.Encode.fst"
let _75_2497 = (encode_args indices env)
in (match (_75_2497) with
| (indices, decls') -> begin
(
# 1454 "FStar.SMTEncoding.Encode.fst"
let _75_2498 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1456 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _156_1858 = (FStar_List.map2 (fun v a -> (let _156_1857 = (let _156_1856 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_156_1856, a))
in (FStar_SMTEncoding_Term.mkEq _156_1857))) vars indices)
in (FStar_All.pipe_right _156_1858 FStar_SMTEncoding_Term.mk_and_l))
in (let _156_1863 = (let _156_1862 = (let _156_1861 = (let _156_1860 = (let _156_1859 = (mk_data_tester env l xx)
in (_156_1859, eqs))
in (FStar_SMTEncoding_Term.mkAnd _156_1860))
in (out, _156_1861))
in (FStar_SMTEncoding_Term.mkOr _156_1862))
in (_156_1863, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_75_2505) with
| (data_ax, decls) -> begin
(
# 1458 "FStar.SMTEncoding.Encode.fst"
let _75_2508 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_75_2508) with
| (ffsym, ff) -> begin
(
# 1459 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _156_1864 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _156_1864 xx tapp))
in (let _156_1871 = (let _156_1870 = (let _156_1869 = (let _156_1868 = (let _156_1867 = (let _156_1866 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _156_1865 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _156_1866, _156_1865)))
in (FStar_SMTEncoding_Term.mkForall _156_1867))
in (_156_1868, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_156_1869))
in (_156_1870)::[])
in (FStar_List.append decls _156_1871)))
end))
end))
end))
end)
in (
# 1463 "FStar.SMTEncoding.Encode.fst"
let _75_2518 = (match ((let _156_1872 = (FStar_Syntax_Subst.compress k)
in _156_1872.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _75_2515 -> begin
(tps, k)
end)
in (match (_75_2518) with
| (formals, res) -> begin
(
# 1469 "FStar.SMTEncoding.Encode.fst"
let _75_2521 = (FStar_Syntax_Subst.open_term formals res)
in (match (_75_2521) with
| (formals, res) -> begin
(
# 1470 "FStar.SMTEncoding.Encode.fst"
let _75_2528 = (encode_binders None formals env)
in (match (_75_2528) with
| (vars, guards, env', binder_decls, _75_2527) -> begin
(
# 1472 "FStar.SMTEncoding.Encode.fst"
let pretype_axioms = (fun tapp vars -> (
# 1473 "FStar.SMTEncoding.Encode.fst"
let _75_2534 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_75_2534) with
| (xxsym, xx) -> begin
(
# 1474 "FStar.SMTEncoding.Encode.fst"
let _75_2537 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_75_2537) with
| (ffsym, ff) -> begin
(
# 1475 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _156_1885 = (let _156_1884 = (let _156_1883 = (let _156_1882 = (let _156_1881 = (let _156_1880 = (let _156_1879 = (let _156_1878 = (let _156_1877 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _156_1877))
in (FStar_SMTEncoding_Term.mkEq _156_1878))
in (xx_has_type, _156_1879))
in (FStar_SMTEncoding_Term.mkImp _156_1880))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _156_1881))
in (FStar_SMTEncoding_Term.mkForall _156_1882))
in (_156_1883, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_156_1884))
in (_156_1885)::[]))
end))
end)))
in (
# 1479 "FStar.SMTEncoding.Encode.fst"
let _75_2542 = (new_term_constant_and_tok_from_lid env t)
in (match (_75_2542) with
| (tname, ttok, env) -> begin
(
# 1480 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1481 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1482 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _156_1887 = (let _156_1886 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _156_1886))
in (FStar_SMTEncoding_Term.mkApp _156_1887))
in (
# 1483 "FStar.SMTEncoding.Encode.fst"
let _75_2563 = (
# 1484 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _156_1891 = (let _156_1890 = (FStar_All.pipe_right vars (FStar_List.map (fun _75_2548 -> (match (_75_2548) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _156_1889 = (varops.next_id ())
in (tname, _156_1890, FStar_SMTEncoding_Term.Term_sort, _156_1889)))
in (constructor_or_logic_type_decl _156_1891))
in (
# 1485 "FStar.SMTEncoding.Encode.fst"
let _75_2560 = (match (vars) with
| [] -> begin
(let _156_1895 = (let _156_1894 = (let _156_1893 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _156_1892 -> Some (_156_1892)) _156_1893))
in (push_free_var env t tname _156_1894))
in ([], _156_1895))
end
| _75_2552 -> begin
(
# 1488 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1489 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _156_1896 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _156_1896))
in (
# 1490 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1491 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1494 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _156_1900 = (let _156_1899 = (let _156_1898 = (let _156_1897 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _156_1897))
in (FStar_SMTEncoding_Term.mkForall' _156_1898))
in (_156_1899, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_156_1900))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_75_2560) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_75_2563) with
| (decls, env) -> begin
(
# 1497 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1498 "FStar.SMTEncoding.Encode.fst"
let _75_2566 = (encode_term_pred None res env' tapp)
in (match (_75_2566) with
| (k, decls) -> begin
(
# 1499 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _156_1904 = (let _156_1903 = (let _156_1902 = (let _156_1901 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _156_1901))
in (_156_1902, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_156_1903))
in (_156_1904)::[])
end else begin
[]
end
in (let _156_1910 = (let _156_1909 = (let _156_1908 = (let _156_1907 = (let _156_1906 = (let _156_1905 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _156_1905))
in (FStar_SMTEncoding_Term.mkForall _156_1906))
in (_156_1907, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_156_1908))
in (_156_1909)::[])
in (FStar_List.append (FStar_List.append decls karr) _156_1910)))
end))
in (
# 1504 "FStar.SMTEncoding.Encode.fst"
let aux = (let _156_1913 = (let _156_1911 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _156_1911))
in (let _156_1912 = (pretype_axioms tapp vars)
in (FStar_List.append _156_1913 _156_1912)))
in (
# 1509 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _75_2573, _75_2575, _75_2577, _75_2579, _75_2581, _75_2583, _75_2585) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _75_2590, t, _75_2593, n_tps, quals, _75_2597, drange) -> begin
(
# 1517 "FStar.SMTEncoding.Encode.fst"
let _75_2604 = (new_term_constant_and_tok_from_lid env d)
in (match (_75_2604) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1518 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1519 "FStar.SMTEncoding.Encode.fst"
let _75_2608 = (FStar_Syntax_Util.arrow_formals t)
in (match (_75_2608) with
| (formals, t_res) -> begin
(
# 1520 "FStar.SMTEncoding.Encode.fst"
let _75_2611 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_75_2611) with
| (fuel_var, fuel_tm) -> begin
(
# 1521 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1522 "FStar.SMTEncoding.Encode.fst"
let _75_2618 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_75_2618) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1523 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _156_1915 = (mk_term_projector_name d x)
in (_156_1915, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1524 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _156_1917 = (let _156_1916 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _156_1916))
in (FStar_All.pipe_right _156_1917 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1525 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1526 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1527 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1528 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1530 "FStar.SMTEncoding.Encode.fst"
let _75_2628 = (encode_term_pred None t env ddtok_tm)
in (match (_75_2628) with
| (tok_typing, decls3) -> begin
(
# 1532 "FStar.SMTEncoding.Encode.fst"
let _75_2635 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_75_2635) with
| (vars', guards', env'', decls_formals, _75_2634) -> begin
(
# 1533 "FStar.SMTEncoding.Encode.fst"
let _75_2640 = (
# 1534 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1535 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_75_2640) with
| (ty_pred', decls_pred) -> begin
(
# 1537 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1538 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _75_2644 -> begin
(let _156_1919 = (let _156_1918 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _156_1918))
in (_156_1919)::[])
end)
in (
# 1542 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _75_2647 -> (match (()) with
| () -> begin
(
# 1543 "FStar.SMTEncoding.Encode.fst"
let _75_2650 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_75_2650) with
| (head, args) -> begin
(match ((let _156_1922 = (FStar_Syntax_Subst.compress head)
in _156_1922.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(
# 1547 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv)
in (
# 1548 "FStar.SMTEncoding.Encode.fst"
let _75_2674 = (encode_args args env')
in (match (_75_2674) with
| (encoded_args, arg_decls) -> begin
(
# 1549 "FStar.SMTEncoding.Encode.fst"
let _75_2689 = (FStar_List.fold_left (fun _75_2678 arg -> (match (_75_2678) with
| (env, arg_vars, eqns) -> begin
(
# 1550 "FStar.SMTEncoding.Encode.fst"
let _75_2684 = (let _156_1925 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _156_1925))
in (match (_75_2684) with
| (_75_2681, xv, env) -> begin
(let _156_1927 = (let _156_1926 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_156_1926)::eqns)
in (env, (xv)::arg_vars, _156_1927))
end))
end)) (env', [], []) encoded_args)
in (match (_75_2689) with
| (_75_2686, arg_vars, eqns) -> begin
(
# 1552 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1553 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1554 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1555 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1556 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1557 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1558 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _156_1934 = (let _156_1933 = (let _156_1932 = (let _156_1931 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _156_1930 = (let _156_1929 = (let _156_1928 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _156_1928))
in (FStar_SMTEncoding_Term.mkImp _156_1929))
in (((ty_pred)::[])::[], _156_1931, _156_1930)))
in (FStar_SMTEncoding_Term.mkForall _156_1932))
in (_156_1933, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_156_1934))
in (
# 1563 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1565 "FStar.SMTEncoding.Encode.fst"
let x = (let _156_1935 = (varops.fresh "x")
in (_156_1935, FStar_SMTEncoding_Term.Term_sort))
in (
# 1566 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _156_1945 = (let _156_1944 = (let _156_1943 = (let _156_1942 = (let _156_1937 = (let _156_1936 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_156_1936)::[])
in (_156_1937)::[])
in (let _156_1941 = (let _156_1940 = (let _156_1939 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _156_1938 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_156_1939, _156_1938)))
in (FStar_SMTEncoding_Term.mkImp _156_1940))
in (_156_1942, (x)::[], _156_1941)))
in (FStar_SMTEncoding_Term.mkForall _156_1943))
in (_156_1944, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_156_1945))))
end else begin
(
# 1569 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _156_1948 = (let _156_1947 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _156_1947 dapp))
in (_156_1948)::[])
end
| _75_2703 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _156_1955 = (let _156_1954 = (let _156_1953 = (let _156_1952 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _156_1951 = (let _156_1950 = (let _156_1949 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _156_1949))
in (FStar_SMTEncoding_Term.mkImp _156_1950))
in (((ty_pred)::[])::[], _156_1952, _156_1951)))
in (FStar_SMTEncoding_Term.mkForall _156_1953))
in (_156_1954, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_156_1955)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _75_2707 -> begin
(
# 1577 "FStar.SMTEncoding.Encode.fst"
let _75_2708 = (let _156_1958 = (let _156_1957 = (FStar_Syntax_Print.lid_to_string d)
in (let _156_1956 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _156_1957 _156_1956)))
in (FStar_TypeChecker_Errors.warn drange _156_1958))
in ([], []))
end)
end))
end))
in (
# 1580 "FStar.SMTEncoding.Encode.fst"
let _75_2712 = (encode_elim ())
in (match (_75_2712) with
| (decls2, elim) -> begin
(
# 1581 "FStar.SMTEncoding.Encode.fst"
let g = (let _156_1983 = (let _156_1982 = (let _156_1967 = (let _156_1966 = (let _156_1965 = (let _156_1964 = (let _156_1963 = (let _156_1962 = (let _156_1961 = (let _156_1960 = (let _156_1959 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _156_1959))
in Some (_156_1960))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _156_1961))
in FStar_SMTEncoding_Term.DeclFun (_156_1962))
in (_156_1963)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _156_1964))
in (FStar_List.append _156_1965 proxy_fresh))
in (FStar_List.append _156_1966 decls_formals))
in (FStar_List.append _156_1967 decls_pred))
in (let _156_1981 = (let _156_1980 = (let _156_1979 = (let _156_1971 = (let _156_1970 = (let _156_1969 = (let _156_1968 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _156_1968))
in (FStar_SMTEncoding_Term.mkForall _156_1969))
in (_156_1970, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_156_1971))
in (let _156_1978 = (let _156_1977 = (let _156_1976 = (let _156_1975 = (let _156_1974 = (let _156_1973 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _156_1972 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _156_1973, _156_1972)))
in (FStar_SMTEncoding_Term.mkForall _156_1974))
in (_156_1975, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_156_1976))
in (_156_1977)::[])
in (_156_1979)::_156_1978))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_156_1980)
in (FStar_List.append _156_1982 _156_1981)))
in (FStar_List.append _156_1983 elim))
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
# 1599 "FStar.SMTEncoding.Encode.fst"
let _75_2721 = (encode_free_var env x t t_norm [])
in (match (_75_2721) with
| (decls, env) -> begin
(
# 1600 "FStar.SMTEncoding.Encode.fst"
let _75_2726 = (lookup_lid env x)
in (match (_75_2726) with
| (n, x', _75_2725) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _75_2730) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env lid t -> (
# 1606 "FStar.SMTEncoding.Encode.fst"
let _75_2738 = (encode_function_type_as_formula None None t env)
in (match (_75_2738) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _156_1996 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _156_1996)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1612 "FStar.SMTEncoding.Encode.fst"
let _75_2747 = (new_term_constant_and_tok_from_lid env lid)
in (match (_75_2747) with
| (vname, vtok, env) -> begin
(
# 1613 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _156_1997 = (FStar_Syntax_Subst.compress t_norm)
in _156_1997.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _75_2750) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _75_2753 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _75_2756 -> begin
[]
end)
in (
# 1616 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1617 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1620 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1621 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1622 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1624 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1625 "FStar.SMTEncoding.Encode.fst"
let _75_2771 = (
# 1626 "FStar.SMTEncoding.Encode.fst"
let _75_2766 = (curried_arrow_formals_comp t_norm)
in (match (_75_2766) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _156_1999 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _156_1999))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_75_2771) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1630 "FStar.SMTEncoding.Encode.fst"
let _75_2775 = (new_term_constant_and_tok_from_lid env lid)
in (match (_75_2775) with
| (vname, vtok, env) -> begin
(
# 1631 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _75_2778 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1634 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _75_20 -> (match (_75_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1636 "FStar.SMTEncoding.Encode.fst"
let _75_2794 = (FStar_Util.prefix vars)
in (match (_75_2794) with
| (_75_2789, (xxsym, _75_2792)) -> begin
(
# 1637 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _156_2016 = (let _156_2015 = (let _156_2014 = (let _156_2013 = (let _156_2012 = (let _156_2011 = (let _156_2010 = (let _156_2009 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_2009))
in (vapp, _156_2010))
in (FStar_SMTEncoding_Term.mkEq _156_2011))
in (((vapp)::[])::[], vars, _156_2012))
in (FStar_SMTEncoding_Term.mkForall _156_2013))
in (_156_2014, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_156_2015))
in (_156_2016)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1642 "FStar.SMTEncoding.Encode.fst"
let _75_2806 = (FStar_Util.prefix vars)
in (match (_75_2806) with
| (_75_2801, (xxsym, _75_2804)) -> begin
(
# 1643 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1644 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1645 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _156_2018 = (let _156_2017 = (mk_term_projector_name d f)
in (_156_2017, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _156_2018))
in (let _156_2023 = (let _156_2022 = (let _156_2021 = (let _156_2020 = (let _156_2019 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _156_2019))
in (FStar_SMTEncoding_Term.mkForall _156_2020))
in (_156_2021, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_156_2022))
in (_156_2023)::[]))))
end))
end
| _75_2811 -> begin
[]
end)))))
in (
# 1649 "FStar.SMTEncoding.Encode.fst"
let _75_2818 = (encode_binders None formals env)
in (match (_75_2818) with
| (vars, guards, env', decls1, _75_2817) -> begin
(
# 1650 "FStar.SMTEncoding.Encode.fst"
let _75_2827 = (match (pre_opt) with
| None -> begin
(let _156_2024 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_156_2024, decls1))
end
| Some (p) -> begin
(
# 1652 "FStar.SMTEncoding.Encode.fst"
let _75_2824 = (encode_formula p env')
in (match (_75_2824) with
| (g, ds) -> begin
(let _156_2025 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_156_2025, (FStar_List.append decls1 ds)))
end))
end)
in (match (_75_2827) with
| (guard, decls1) -> begin
(
# 1653 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1655 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _156_2027 = (let _156_2026 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _156_2026))
in (FStar_SMTEncoding_Term.mkApp _156_2027))
in (
# 1656 "FStar.SMTEncoding.Encode.fst"
let _75_2851 = (
# 1657 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _156_2030 = (let _156_2029 = (FStar_All.pipe_right formals (FStar_List.map (fun _75_2830 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _156_2029, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_156_2030))
in (
# 1658 "FStar.SMTEncoding.Encode.fst"
let _75_2838 = (
# 1659 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1659 "FStar.SMTEncoding.Encode.fst"
let _75_2833 = env
in {bindings = _75_2833.bindings; depth = _75_2833.depth; tcenv = _75_2833.tcenv; warn = _75_2833.warn; cache = _75_2833.cache; nolabels = _75_2833.nolabels; use_zfuel_name = _75_2833.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_75_2838) with
| (tok_typing, decls2) -> begin
(
# 1663 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1664 "FStar.SMTEncoding.Encode.fst"
let _75_2848 = (match (formals) with
| [] -> begin
(let _156_2034 = (let _156_2033 = (let _156_2032 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _156_2031 -> Some (_156_2031)) _156_2032))
in (push_free_var env lid vname _156_2033))
in ((FStar_List.append decls2 ((tok_typing)::[])), _156_2034))
end
| _75_2842 -> begin
(
# 1667 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1668 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _156_2035 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _156_2035))
in (
# 1669 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _156_2039 = (let _156_2038 = (let _156_2037 = (let _156_2036 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _156_2036))
in (FStar_SMTEncoding_Term.mkForall _156_2037))
in (_156_2038, None))
in FStar_SMTEncoding_Term.Assume (_156_2039))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_75_2848) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_75_2851) with
| (decls2, env) -> begin
(
# 1672 "FStar.SMTEncoding.Encode.fst"
let _75_2859 = (
# 1673 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1674 "FStar.SMTEncoding.Encode.fst"
let _75_2855 = (encode_term res_t env')
in (match (_75_2855) with
| (encoded_res_t, decls) -> begin
(let _156_2040 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _156_2040, decls))
end)))
in (match (_75_2859) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1676 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _156_2044 = (let _156_2043 = (let _156_2042 = (let _156_2041 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _156_2041))
in (FStar_SMTEncoding_Term.mkForall _156_2042))
in (_156_2043, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_156_2044))
in (
# 1677 "FStar.SMTEncoding.Encode.fst"
let g = (let _156_2046 = (let _156_2045 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_156_2045)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _156_2046))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _75_2866 se -> (match (_75_2866) with
| (g, env) -> begin
(
# 1683 "FStar.SMTEncoding.Encode.fst"
let _75_2870 = (encode_sigelt env se)
in (match (_75_2870) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1686 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1711 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _75_2877 -> (match (_75_2877) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_75_2879) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1716 "FStar.SMTEncoding.Encode.fst"
let _75_2886 = (new_term_constant env x)
in (match (_75_2886) with
| (xxsym, xx, env') -> begin
(
# 1717 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1718 "FStar.SMTEncoding.Encode.fst"
let _75_2888 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _156_2061 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_2060 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _156_2059 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _156_2061 _156_2060 _156_2059))))
end else begin
()
end
in (
# 1720 "FStar.SMTEncoding.Encode.fst"
let _75_2892 = (encode_term_pred None t1 env xx)
in (match (_75_2892) with
| (t, decls') -> begin
(
# 1721 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _156_2065 = (let _156_2064 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_2063 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _156_2062 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _156_2064 _156_2063 _156_2062))))
in Some (_156_2065))
end else begin
None
end
in (
# 1725 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((FStar_SMTEncoding_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_75_2897, t)) -> begin
(
# 1731 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1733 "FStar.SMTEncoding.Encode.fst"
let _75_2905 = (encode_free_var env x t t_norm [])
in (match (_75_2905) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1738 "FStar.SMTEncoding.Encode.fst"
let _75_2919 = (encode_sigelt env se)
in (match (_75_2919) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1743 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1744 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _75_2926 -> (match (_75_2926) with
| (l, _75_2923, _75_2925) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1745 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _75_2933 -> (match (_75_2933) with
| (l, _75_2930, _75_2932) -> begin
(let _156_2073 = (FStar_All.pipe_left (fun _156_2069 -> FStar_SMTEncoding_Term.Echo (_156_2069)) (Prims.fst l))
in (let _156_2072 = (let _156_2071 = (let _156_2070 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_156_2070))
in (_156_2071)::[])
in (_156_2073)::_156_2072))
end))))
in (prefix, suffix))))

# 1749 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1750 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _156_2078 = (let _156_2077 = (let _156_2076 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _156_2076; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_156_2077)::[])
in (FStar_ST.op_Colon_Equals last_env _156_2078)))

# 1753 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_75_2939 -> begin
(
# 1755 "FStar.SMTEncoding.Encode.fst"
let _75_2942 = e
in {bindings = _75_2942.bindings; depth = _75_2942.depth; tcenv = tcenv; warn = _75_2942.warn; cache = _75_2942.cache; nolabels = _75_2942.nolabels; use_zfuel_name = _75_2942.use_zfuel_name; encode_non_total_function_typ = _75_2942.encode_non_total_function_typ})
end))

# 1756 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _75_2948::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1759 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _75_2950 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1762 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1763 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1763 "FStar.SMTEncoding.Encode.fst"
let _75_2956 = hd
in {bindings = _75_2956.bindings; depth = _75_2956.depth; tcenv = _75_2956.tcenv; warn = _75_2956.warn; cache = refs; nolabels = _75_2956.nolabels; use_zfuel_name = _75_2956.use_zfuel_name; encode_non_total_function_typ = _75_2956.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1765 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _75_2959 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _75_2963::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1768 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _75_2965 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1769 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _75_2966 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1770 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _75_2967 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_75_2970::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _75_2975 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1776 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1777 "FStar.SMTEncoding.Encode.fst"
let _75_2977 = (init_env tcenv)
in (
# 1778 "FStar.SMTEncoding.Encode.fst"
let _75_2979 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1780 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1781 "FStar.SMTEncoding.Encode.fst"
let _75_2982 = (push_env ())
in (
# 1782 "FStar.SMTEncoding.Encode.fst"
let _75_2984 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1784 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1785 "FStar.SMTEncoding.Encode.fst"
let _75_2987 = (let _156_2099 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _156_2099))
in (
# 1786 "FStar.SMTEncoding.Encode.fst"
let _75_2989 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1788 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1789 "FStar.SMTEncoding.Encode.fst"
let _75_2992 = (mark_env ())
in (
# 1790 "FStar.SMTEncoding.Encode.fst"
let _75_2994 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1792 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1793 "FStar.SMTEncoding.Encode.fst"
let _75_2997 = (reset_mark_env ())
in (
# 1794 "FStar.SMTEncoding.Encode.fst"
let _75_2999 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1796 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1797 "FStar.SMTEncoding.Encode.fst"
let _75_3002 = (commit_mark_env ())
in (
# 1798 "FStar.SMTEncoding.Encode.fst"
let _75_3004 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1800 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1801 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _156_2115 = (let _156_2114 = (let _156_2113 = (let _156_2112 = (let _156_2111 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _156_2111 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _156_2112 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _156_2113))
in FStar_SMTEncoding_Term.Caption (_156_2114))
in (_156_2115)::decls)
end else begin
decls
end)
in (
# 1805 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1806 "FStar.SMTEncoding.Encode.fst"
let _75_3013 = (encode_sigelt env se)
in (match (_75_3013) with
| (decls, env) -> begin
(
# 1807 "FStar.SMTEncoding.Encode.fst"
let _75_3014 = (set_env env)
in (let _156_2116 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _156_2116)))
end)))))

# 1810 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1811 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1812 "FStar.SMTEncoding.Encode.fst"
let _75_3019 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _156_2121 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _156_2121))
end else begin
()
end
in (
# 1814 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1815 "FStar.SMTEncoding.Encode.fst"
let _75_3026 = (encode_signature (
# 1815 "FStar.SMTEncoding.Encode.fst"
let _75_3022 = env
in {bindings = _75_3022.bindings; depth = _75_3022.depth; tcenv = _75_3022.tcenv; warn = false; cache = _75_3022.cache; nolabels = _75_3022.nolabels; use_zfuel_name = _75_3022.use_zfuel_name; encode_non_total_function_typ = _75_3022.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_75_3026) with
| (decls, env) -> begin
(
# 1816 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1818 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1821 "FStar.SMTEncoding.Encode.fst"
let _75_3032 = (set_env (
# 1821 "FStar.SMTEncoding.Encode.fst"
let _75_3030 = env
in {bindings = _75_3030.bindings; depth = _75_3030.depth; tcenv = _75_3030.tcenv; warn = true; cache = _75_3030.cache; nolabels = _75_3030.nolabels; use_zfuel_name = _75_3030.use_zfuel_name; encode_non_total_function_typ = _75_3030.encode_non_total_function_typ}))
in (
# 1822 "FStar.SMTEncoding.Encode.fst"
let _75_3034 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1823 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1826 "FStar.SMTEncoding.Encode.fst"
let solve : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (
# 1827 "FStar.SMTEncoding.Encode.fst"
let _75_3039 = (let _156_2130 = (let _156_2129 = (let _156_2128 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _156_2128))
in (FStar_Util.format1 "Starting query at %s" _156_2129))
in (push _156_2130))
in (
# 1828 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _75_3042 -> (match (()) with
| () -> begin
(let _156_2135 = (let _156_2134 = (let _156_2133 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _156_2133))
in (FStar_Util.format1 "Ending query at %s" _156_2134))
in (pop _156_2135))
end))
in (
# 1829 "FStar.SMTEncoding.Encode.fst"
let _75_3096 = (
# 1830 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1831 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1832 "FStar.SMTEncoding.Encode.fst"
let _75_3066 = (
# 1833 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1835 "FStar.SMTEncoding.Encode.fst"
let _75_3055 = (aux rest)
in (match (_75_3055) with
| (out, rest) -> begin
(
# 1836 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _156_2141 = (let _156_2140 = (FStar_Syntax_Syntax.mk_binder (
# 1837 "FStar.SMTEncoding.Encode.fst"
let _75_3057 = x
in {FStar_Syntax_Syntax.ppname = _75_3057.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _75_3057.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_156_2140)::out)
in (_156_2141, rest)))
end))
end
| _75_3060 -> begin
([], bindings)
end))
in (
# 1839 "FStar.SMTEncoding.Encode.fst"
let _75_3063 = (aux bindings)
in (match (_75_3063) with
| (closing, bindings) -> begin
(let _156_2142 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_156_2142, bindings))
end)))
in (match (_75_3066) with
| (q, bindings) -> begin
(
# 1841 "FStar.SMTEncoding.Encode.fst"
let _75_3075 = (let _156_2144 = (FStar_List.filter (fun _75_21 -> (match (_75_21) with
| FStar_TypeChecker_Env.Binding_sig (_75_3069) -> begin
false
end
| _75_3072 -> begin
true
end)) bindings)
in (encode_env_bindings env _156_2144))
in (match (_75_3075) with
| (env_decls, env) -> begin
(
# 1842 "FStar.SMTEncoding.Encode.fst"
let _75_3076 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _156_2145 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _156_2145))
end else begin
()
end
in (
# 1845 "FStar.SMTEncoding.Encode.fst"
let _75_3080 = (encode_formula q env)
in (match (_75_3080) with
| (phi, qdecls) -> begin
(
# 1848 "FStar.SMTEncoding.Encode.fst"
let _75_3085 = (FStar_SMTEncoding_ErrorReporting.label_goals [] phi [])
in (match (_75_3085) with
| (phi, labels, _75_3084) -> begin
(
# 1849 "FStar.SMTEncoding.Encode.fst"
let _75_3088 = (encode_labels labels)
in (match (_75_3088) with
| (label_prefix, label_suffix) -> begin
(
# 1850 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1854 "FStar.SMTEncoding.Encode.fst"
let qry = (let _156_2147 = (let _156_2146 = (FStar_SMTEncoding_Term.mkNot phi)
in (_156_2146, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_156_2147))
in (
# 1855 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_75_3096) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _75_3103); FStar_SMTEncoding_Term.hash = _75_3100; FStar_SMTEncoding_Term.freevars = _75_3098}, _75_3108) -> begin
(
# 1858 "FStar.SMTEncoding.Encode.fst"
let _75_3111 = (pop ())
in ())
end
| _75_3114 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1859 "FStar.SMTEncoding.Encode.fst"
let _75_3115 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _75_3119) -> begin
(
# 1861 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1862 "FStar.SMTEncoding.Encode.fst"
let _75_3123 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 1864 "FStar.SMTEncoding.Encode.fst"
let with_fuel = (fun p _75_3129 -> (match (_75_3129) with
| (n, i) -> begin
(let _156_2170 = (let _156_2169 = (let _156_2154 = (let _156_2153 = (FStar_Util.string_of_int n)
in (let _156_2152 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _156_2153 _156_2152)))
in FStar_SMTEncoding_Term.Caption (_156_2154))
in (let _156_2168 = (let _156_2167 = (let _156_2159 = (let _156_2158 = (let _156_2157 = (let _156_2156 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _156_2155 = (FStar_SMTEncoding_Term.n_fuel n)
in (_156_2156, _156_2155)))
in (FStar_SMTEncoding_Term.mkEq _156_2157))
in (_156_2158, None))
in FStar_SMTEncoding_Term.Assume (_156_2159))
in (let _156_2166 = (let _156_2165 = (let _156_2164 = (let _156_2163 = (let _156_2162 = (let _156_2161 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _156_2160 = (FStar_SMTEncoding_Term.n_fuel i)
in (_156_2161, _156_2160)))
in (FStar_SMTEncoding_Term.mkEq _156_2162))
in (_156_2163, None))
in FStar_SMTEncoding_Term.Assume (_156_2164))
in (_156_2165)::(p)::(FStar_SMTEncoding_Term.CheckSat)::[])
in (_156_2167)::_156_2166))
in (_156_2169)::_156_2168))
in (FStar_List.append _156_2170 suffix))
end))
in (
# 1871 "FStar.SMTEncoding.Encode.fst"
let check = (fun p -> (
# 1872 "FStar.SMTEncoding.Encode.fst"
let initial_config = (let _156_2174 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _156_2173 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_156_2174, _156_2173)))
in (
# 1873 "FStar.SMTEncoding.Encode.fst"
let alt_configs = (let _156_2193 = (let _156_2192 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _156_2177 = (let _156_2176 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _156_2175 = (FStar_ST.read FStar_Options.max_ifuel)
in (_156_2176, _156_2175)))
in (_156_2177)::[])
end else begin
[]
end
in (let _156_2191 = (let _156_2190 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _156_2180 = (let _156_2179 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _156_2178 = (FStar_ST.read FStar_Options.max_ifuel)
in (_156_2179, _156_2178)))
in (_156_2180)::[])
end else begin
[]
end
in (let _156_2189 = (let _156_2188 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _156_2183 = (let _156_2182 = (FStar_ST.read FStar_Options.max_fuel)
in (let _156_2181 = (FStar_ST.read FStar_Options.max_ifuel)
in (_156_2182, _156_2181)))
in (_156_2183)::[])
end else begin
[]
end
in (let _156_2187 = (let _156_2186 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _156_2185 = (let _156_2184 = (FStar_ST.read FStar_Options.min_fuel)
in (_156_2184, 1))
in (_156_2185)::[])
end else begin
[]
end
in (_156_2186)::[])
in (_156_2188)::_156_2187))
in (_156_2190)::_156_2189))
in (_156_2192)::_156_2191))
in (FStar_List.flatten _156_2193))
in (
# 1878 "FStar.SMTEncoding.Encode.fst"
let report = (fun errs -> (
# 1879 "FStar.SMTEncoding.Encode.fst"
let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _75_3138 -> begin
errs
end)
in (
# 1882 "FStar.SMTEncoding.Encode.fst"
let _75_3140 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _156_2201 = (let _156_2196 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _156_2196))
in (let _156_2200 = (let _156_2197 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _156_2197 FStar_Util.string_of_int))
in (let _156_2199 = (let _156_2198 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _156_2198 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _156_2201 _156_2200 _156_2199))))
end else begin
()
end
in (FStar_TypeChecker_Errors.add_errors tcenv errs))))
in (
# 1889 "FStar.SMTEncoding.Encode.fst"
let rec try_alt_configs = (fun p errs _75_22 -> (match (_75_22) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _156_2212 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _156_2212 (cb mi p [])))
end
| _75_3152 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _156_2214 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _156_2214 (fun _75_3158 -> (match (_75_3158) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _75_3161 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _75_3164 p alt _75_3169 -> (match ((_75_3164, _75_3169)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _156_2222 = (let _156_2219 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _156_2219))
in (let _156_2221 = (FStar_Util.string_of_int prev_fuel)
in (let _156_2220 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _156_2222 _156_2221 _156_2220))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _156_2223 = (with_fuel p initial_config)
in (FStar_SMTEncoding_Z3.ask fresh labels _156_2223 (cb initial_config p alt_configs))))))))
in (
# 1914 "FStar.SMTEncoding.Encode.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 1916 "FStar.SMTEncoding.Encode.fst"
let _75_3174 = (let _156_2229 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _156_2229 q))
in (match (_75_3174) with
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
# 1921 "FStar.SMTEncoding.Encode.fst"
let _75_3175 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _75_3178 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1927 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1928 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1929 "FStar.SMTEncoding.Encode.fst"
let _75_3182 = (push "query")
in (
# 1930 "FStar.SMTEncoding.Encode.fst"
let _75_3189 = (encode_formula_with_labels q env)
in (match (_75_3189) with
| (f, _75_3186, _75_3188) -> begin
(
# 1931 "FStar.SMTEncoding.Encode.fst"
let _75_3190 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _75_3194) -> begin
true
end
| _75_3198 -> begin
false
end))
end)))))

# 1936 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1950 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _75_3199 -> ()); FStar_TypeChecker_Env.push = (fun _75_3201 -> ()); FStar_TypeChecker_Env.pop = (fun _75_3203 -> ()); FStar_TypeChecker_Env.mark = (fun _75_3205 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _75_3207 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _75_3209 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _75_3211 _75_3213 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _75_3215 _75_3217 -> ()); FStar_TypeChecker_Env.solve = (fun _75_3219 _75_3221 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _75_3223 _75_3225 -> false); FStar_TypeChecker_Env.finish = (fun _75_3227 -> ()); FStar_TypeChecker_Env.refresh = (fun _75_3228 -> ())}





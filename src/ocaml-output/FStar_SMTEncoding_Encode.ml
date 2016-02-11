
open Prims
# 34 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 35 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let withenv = (fun c _100_28 -> (match (_100_28) with
| (a, b) -> begin
(a, b, c)
end))

# 36 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let vargs = (fun args -> (FStar_List.filter (fun _100_1 -> (match (_100_1) with
| (FStar_Util.Inl (_100_32), _100_35) -> begin
false
end
| _100_38 -> begin
true
end)) args))

# 37 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _202_13 = (let _202_12 = (let _202_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _202_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _202_12))
in Some (_202_13))
end))

# 42 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 43 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (let a = (let _100_47 = a
in (let _202_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _202_20; FStar_Syntax_Syntax.index = _100_47.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _100_47.FStar_Syntax_Syntax.sort}))
in (let _202_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _202_21))))

# 46 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (let fail = (fun _100_54 -> (match (()) with
| () -> begin
(let _202_31 = (let _202_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _202_30 lid.FStar_Ident.str))
in (FStar_All.failwith _202_31))
end))
in (let _100_58 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_100_58) with
| (_100_56, t) -> begin
(match ((let _202_32 = (FStar_Syntax_Subst.compress t)
in _202_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _100_66 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_100_66) with
| (binders, _100_65) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _100_69 -> begin
(fail ())
end)
end))))

# 57 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _202_38 = (let _202_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _202_37))
in (FStar_All.pipe_left escape _202_38)))

# 58 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _202_44 = (let _202_43 = (mk_term_projector_name lid a)
in (_202_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _202_44)))

# 60 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _202_50 = (let _202_49 = (mk_term_projector_name_by_pos lid i)
in (_202_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _202_50)))

# 62 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

# 65 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}

# 65 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

# 77 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let varops : varops_t = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _100_93 -> (match (()) with
| () -> begin
(let _202_154 = (FStar_Util.smap_create 100)
in (let _202_153 = (FStar_Util.smap_create 100)
in (_202_154, _202_153)))
end))
in (let scopes = (let _202_156 = (let _202_155 = (new_scope ())
in (_202_155)::[])
in (FStar_Util.mk_ref _202_156))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _202_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _202_160 (fun _100_101 -> (match (_100_101) with
| (names, _100_100) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_100_104) -> begin
(let _100_106 = (FStar_Util.incr ctr)
in (let _202_162 = (let _202_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _202_161))
in (Prims.strcat (Prims.strcat y "__") _202_162)))
end)
in (let top_scope = (let _202_164 = (let _202_163 = (FStar_ST.read scopes)
in (FStar_List.hd _202_163))
in (FStar_All.pipe_left Prims.fst _202_164))
in (let _100_110 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _202_171 = (let _202_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _202_169 "__"))
in (let _202_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _202_171 _202_170))))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (let next_id = (fun _100_118 -> (match (()) with
| () -> begin
(let _100_119 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _202_179 = (let _202_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _202_178))
in (FStar_Util.format2 "%s_%s" pfx _202_179)))
in (let string_const = (fun s -> (match ((let _202_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _202_183 (fun _100_128 -> (match (_100_128) with
| (_100_126, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _202_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _202_184))
in (let top_scope = (let _202_186 = (let _202_185 = (FStar_ST.read scopes)
in (FStar_List.hd _202_185))
in (FStar_All.pipe_left Prims.snd _202_186))
in (let _100_135 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _100_138 -> (match (()) with
| () -> begin
(let _202_191 = (let _202_190 = (new_scope ())
in (let _202_189 = (FStar_ST.read scopes)
in (_202_190)::_202_189))
in (FStar_ST.op_Colon_Equals scopes _202_191))
end))
in (let pop = (fun _100_140 -> (match (()) with
| () -> begin
(let _202_195 = (let _202_194 = (FStar_ST.read scopes)
in (FStar_List.tl _202_194))
in (FStar_ST.op_Colon_Equals scopes _202_195))
end))
in (let mark = (fun _100_142 -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _100_144 -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _100_146 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _100_159 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (let _100_164 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _100_167 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 122 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (let _100_169 = x
in (let _202_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _202_210; FStar_Syntax_Syntax.index = _100_169.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _100_169.FStar_Syntax_Syntax.sort})))

# 126 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)

# 127 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 127 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let ___Binding_var____0 : binding  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) = (fun projectee -> (match (projectee) with
| Binding_var (_100_173) -> begin
_100_173
end))

# 128 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let ___Binding_fvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_100_176) -> begin
_100_176
end))

# 131 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let binder_of_eithervar = (fun v -> (v, None))

# 132 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 142 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let print_env : env_t  ->  Prims.string = (fun e -> (let _202_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _100_2 -> (match (_100_2) with
| Binding_var (x, _100_191) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _100_196, _100_198, _100_200) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _202_268 (FStar_String.concat ", "))))

# 147 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _202_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_202_278))
end else begin
None
end)

# 154 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (let xsym = (varops.fresh x)
in (let _202_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _202_283))))

# 158 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (let ysym = (let _202_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _202_288))
in (let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (let _100_214 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _100_214.tcenv; warn = _100_214.warn; cache = _100_214.cache; nolabels = _100_214.nolabels; use_zfuel_name = _100_214.use_zfuel_name; encode_non_total_function_typ = _100_214.encode_non_total_function_typ})))))

# 162 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (let _100_220 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _100_220.depth; tcenv = _100_220.tcenv; warn = _100_220.warn; cache = _100_220.cache; nolabels = _100_220.nolabels; use_zfuel_name = _100_220.use_zfuel_name; encode_non_total_function_typ = _100_220.encode_non_total_function_typ})))))

# 166 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (let _100_225 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _100_225.depth; tcenv = _100_225.tcenv; warn = _100_225.warn; cache = _100_225.cache; nolabels = _100_225.nolabels; use_zfuel_name = _100_225.use_zfuel_name; encode_non_total_function_typ = _100_225.encode_non_total_function_typ}))

# 168 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _100_3 -> (match (_100_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _100_235 -> begin
None
end)))) with
| None -> begin
(let _202_305 = (let _202_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _202_304))
in (FStar_All.failwith _202_305))
end
| Some (b, t) -> begin
t
end))

# 174 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _202_316 = (let _100_245 = env
in (let _202_315 = (let _202_314 = (let _202_313 = (let _202_312 = (let _202_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _202_310 -> Some (_202_310)) _202_311))
in (x, fname, _202_312, None))
in Binding_fvar (_202_313))
in (_202_314)::env.bindings)
in {bindings = _202_315; depth = _100_245.depth; tcenv = _100_245.tcenv; warn = _100_245.warn; cache = _100_245.cache; nolabels = _100_245.nolabels; use_zfuel_name = _100_245.use_zfuel_name; encode_non_total_function_typ = _100_245.encode_non_total_function_typ}))
in (fname, ftok, _202_316)))))

# 179 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _100_4 -> (match (_100_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _100_257 -> begin
None
end))))

# 181 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _202_326 = (FStar_Util.format1 "Name not found: %s" (FStar_Syntax_Print.lid_to_string a))
in (FStar_All.failwith _202_326))
end
| Some (s) -> begin
s
end))

# 185 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (let _100_267 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _100_267.depth; tcenv = _100_267.tcenv; warn = _100_267.warn; cache = _100_267.cache; nolabels = _100_267.nolabels; use_zfuel_name = _100_267.use_zfuel_name; encode_non_total_function_typ = _100_267.encode_non_total_function_typ}))

# 187 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (let _100_276 = (lookup_lid env x)
in (match (_100_276) with
| (t1, t2, _100_275) -> begin
(let t3 = (let _202_343 = (let _202_342 = (let _202_341 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_202_341)::[])
in (f, _202_342))
in (FStar_SMTEncoding_Term.mkApp _202_343))
in (let _100_278 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _100_278.depth; tcenv = _100_278.tcenv; warn = _100_278.warn; cache = _100_278.cache; nolabels = _100_278.nolabels; use_zfuel_name = _100_278.use_zfuel_name; encode_non_total_function_typ = _100_278.encode_non_total_function_typ}))
end)))

# 191 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| _100_291 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_100_295, fuel::[]) -> begin
if (let _202_349 = (let _202_348 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _202_348 Prims.fst))
in (FStar_Util.starts_with _202_349 "fuel")) then begin
(let _202_352 = (let _202_351 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _202_351 fuel))
in (FStar_All.pipe_left (fun _202_350 -> Some (_202_350)) _202_352))
end else begin
Some (t)
end
end
| _100_301 -> begin
Some (t)
end)
end
| _100_303 -> begin
None
end)
end)
end))

# 208 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _202_355 = (FStar_Util.format1 "Name not found: %s" (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v))
in (FStar_All.failwith _202_355))
end))

# 212 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let lookup_free_var_name = (fun env a -> (let _100_316 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_100_316) with
| (x, _100_313, _100_315) -> begin
x
end)))

# 213 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let lookup_free_var_sym = (fun env a -> (let _100_322 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_100_322) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _100_326; FStar_SMTEncoding_Term.freevars = _100_324}) when env.use_zfuel_name -> begin
(g, zf)
end
| _100_334 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _100_344 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 225 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _100_5 -> (match (_100_5) with
| Binding_fvar (_100_349, nm', tok, _100_353) when (nm = nm') -> begin
tok
end
| _100_357 -> begin
None
end))))

# 234 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mkForall_fuel' = (fun n _100_362 -> (match (_100_362) with
| (pats, vars, body) -> begin
(let fallback = (fun _100_364 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(let _100_367 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_100_367) with
| (fsym, fterm) -> begin
(let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _100_377 -> begin
p
end)))))
in (let pats = (FStar_List.map add_fuel pats)
in (let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, guard::body'::[]) -> begin
(let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _202_372 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _202_372))
end
| _100_390 -> begin
(let _202_373 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _202_373 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _100_393 -> begin
body
end)
in (let vars = ((fsym, FStar_SMTEncoding_Term.Fuel_sort))::vars
in (FStar_SMTEncoding_Term.mkForall (pats, vars, body))))))
end))
end)
end))

# 254 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mkForall_fuel : (FStar_SMTEncoding_Term.term Prims.list Prims.list * FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' 1)

# 256 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (v, _)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _202_379 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv v.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _202_379 FStar_Option.isNone))
end
| _100_438 -> begin
false
end)))

# 269 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)

# 272 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))

# 274 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let trivial_post : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (let _202_390 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
in (FStar_Syntax_Util.abs (((FStar_Syntax_Syntax.null_binder t))::[]) _202_390 None)))

# 279 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _202_397 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _202_397))
end
| s -> begin
(let _100_450 = ()
in (let _202_398 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _202_398)))
end)) e)))

# 283 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 285 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _100_6 -> (match (_100_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _100_460 -> begin
false
end))

# 290 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _100_471; FStar_SMTEncoding_Term.freevars = _100_469}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _100_489) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _100_496 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_100_498, []) -> begin
(let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _100_504 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

# 333 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)

# 334 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

type labels =
label Prims.list

# 335 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}

# 335 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

# 341 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

exception Let_rec_unencodeable

# 341 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))

# 343 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _100_7 -> (match (_100_7) with
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
(let _202_452 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _202_452))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _202_453 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _202_453))
end
| FStar_Const.Const_int (i) -> begin
(let _202_454 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _202_454))
end
| FStar_Const.Const_int32 (i) -> begin
(let _202_458 = (let _202_457 = (let _202_456 = (let _202_455 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _202_455))
in (_202_456)::[])
in ("FStar.Int32.Int32", _202_457))
in (FStar_SMTEncoding_Term.mkApp _202_458))
end
| FStar_Const.Const_string (bytes, _100_526) -> begin
(let _202_459 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _202_459))
end
| c -> begin
(let _202_461 = (let _202_460 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _202_460))
in (FStar_All.failwith _202_461))
end))

# 354 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_100_537) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_100_540) -> begin
(let _202_470 = (FStar_Syntax_Util.unrefine t)
in (aux true _202_470))
end
| _100_543 -> begin
if norm then begin
(let _202_471 = (whnf env t)
in (aux false _202_471))
end else begin
(let _202_474 = (let _202_473 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _202_472 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _202_473 _202_472)))
in (FStar_All.failwith _202_474))
end
end)))
in (aux true t0)))

# 365 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax) = (fun k -> (let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _100_551 -> begin
(let _202_477 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _202_477))
end)))

# 372 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (let _100_555 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _202_527 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _202_527))
end else begin
()
end
in (let _100_583 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _100_562 b -> (match (_100_562) with
| (vars, guards, env, decls, names) -> begin
(let _100_577 = (let x = (unmangle (Prims.fst b))
in (let _100_568 = (gen_term_var env x)
in (match (_100_568) with
| (xxsym, xx, env') -> begin
(let _100_571 = (let _202_530 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _202_530 env xx))
in (match (_100_571) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_100_577) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_100_583) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (let _100_590 = (encode_term t env)
in (match (_100_590) with
| (t, decls) -> begin
(let _202_535 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_202_535, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (let _100_597 = (encode_term t env)
in (match (_100_597) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _202_540 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_202_540, decls))
end
| Some (f) -> begin
(let _202_541 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_202_541, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (let t0 = (FStar_Syntax_Subst.compress t)
in (let _100_604 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _202_546 = (FStar_Syntax_Print.tag_of_term t)
in (let _202_545 = (FStar_Syntax_Print.tag_of_term t0)
in (let _202_544 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _202_546 _202_545 _202_544))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _202_551 = (let _202_550 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _202_549 = (FStar_Syntax_Print.tag_of_term t0)
in (let _202_548 = (FStar_Syntax_Print.term_to_string t0)
in (let _202_547 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _202_550 _202_549 _202_548 _202_547)))))
in (FStar_All.failwith _202_551))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _202_553 = (let _202_552 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _202_552))
in (FStar_All.failwith _202_553))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _100_615) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _100_620) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v, _100_628) -> begin
(let _202_554 = (lookup_free_var env v)
in (_202_554, []))
end
| FStar_Syntax_Syntax.Tm_type (_100_632) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _100_636) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _202_555 = (encode_const c)
in (_202_555, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(let _100_647 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_100_647) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(let _100_654 = (encode_binders None binders env)
in (match (_100_654) with
| (vars, guards, env', decls, _100_653) -> begin
(let fsym = (let _202_556 = (varops.fresh "f")
in (_202_556, FStar_SMTEncoding_Term.Term_sort))
in (let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (let app = (mk_Apply f vars)
in (let _100_660 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_100_660) with
| (pre_opt, res_t) -> begin
(let _100_663 = (encode_term_pred None res_t env' app)
in (match (_100_663) with
| (res_pred, decls') -> begin
(let _100_672 = (match (pre_opt) with
| None -> begin
(let _202_557 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_202_557, decls))
end
| Some (pre) -> begin
(let _100_669 = (encode_formula pre env')
in (match (_100_669) with
| (guard, decls0) -> begin
(let _202_558 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_202_558, (FStar_List.append decls decls0)))
end))
end)
in (match (_100_672) with
| (guards, guard_decls) -> begin
(let t_interp = (let _202_560 = (let _202_559 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _202_559))
in (FStar_SMTEncoding_Term.mkForall _202_560))
in (let cvars = (let _202_562 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _202_562 (FStar_List.filter (fun _100_677 -> (match (_100_677) with
| (x, _100_676) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _100_683) -> begin
(let _202_565 = (let _202_564 = (let _202_563 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _202_563))
in (FStar_SMTEncoding_Term.mkApp _202_564))
in (_202_565, []))
end
| None -> begin
(let tsym = (varops.fresh "Tm_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _202_566 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_202_566))
end else begin
None
end
in (let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (let t = (let _202_568 = (let _202_567 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _202_567))
in (FStar_SMTEncoding_Term.mkApp _202_568))
in (let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (let k_assumption = (let _202_570 = (let _202_569 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_202_569, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_202_570))
in (let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _202_577 = (let _202_576 = (let _202_575 = (let _202_574 = (let _202_573 = (let _202_572 = (let _202_571 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _202_571))
in (f_has_t, _202_572))
in (FStar_SMTEncoding_Term.mkImp _202_573))
in (((f_has_t)::[])::[], (fsym)::cvars, _202_574))
in (mkForall_fuel _202_575))
in (_202_576, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_202_577))
in (let t_interp = (let _202_581 = (let _202_580 = (let _202_579 = (let _202_578 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _202_578))
in (FStar_SMTEncoding_Term.mkForall _202_579))
in (_202_580, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_202_581))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _100_699 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(let tsym = (varops.fresh "Non_total_Tm_arrow")
in (let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (let t_kinding = (let _202_583 = (let _202_582 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_202_582, None))
in FStar_SMTEncoding_Term.Assume (_202_583))
in (let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (let t_interp = (let _202_590 = (let _202_589 = (let _202_588 = (let _202_587 = (let _202_586 = (let _202_585 = (let _202_584 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _202_584))
in (f_has_t, _202_585))
in (FStar_SMTEncoding_Term.mkImp _202_586))
in (((f_has_t)::[])::[], (fsym)::[], _202_587))
in (mkForall_fuel _202_588))
in (_202_589, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_202_590))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_100_710) -> begin
(let _100_730 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _100_717; FStar_Syntax_Syntax.pos = _100_715; FStar_Syntax_Syntax.vars = _100_713} -> begin
(let _100_725 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_100_725) with
| (b, f) -> begin
(let _202_592 = (let _202_591 = (FStar_List.hd b)
in (Prims.fst _202_591))
in (_202_592, f))
end))
end
| _100_727 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_100_730) with
| (x, f) -> begin
(let _100_733 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_100_733) with
| (base_t, decls) -> begin
(let _100_737 = (gen_term_var env x)
in (match (_100_737) with
| (x, xtm, env') -> begin
(let _100_740 = (encode_formula f env')
in (match (_100_740) with
| (refinement, decls') -> begin
(let _100_743 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_100_743) with
| (fsym, fterm) -> begin
(let encoding = (let _202_594 = (let _202_593 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_202_593, refinement))
in (FStar_SMTEncoding_Term.mkAnd _202_594))
in (let cvars = (let _202_596 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _202_596 (FStar_List.filter (fun _100_748 -> (match (_100_748) with
| (y, _100_747) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _100_755, _100_757) -> begin
(let _202_599 = (let _202_598 = (let _202_597 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _202_597))
in (FStar_SMTEncoding_Term.mkApp _202_598))
in (_202_599, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (let t = (let _202_601 = (let _202_600 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _202_600))
in (FStar_SMTEncoding_Term.mkApp _202_601))
in (let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (let t_kinding = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (let assumption = (let _202_603 = (let _202_602 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _202_602))
in (FStar_SMTEncoding_Term.mkForall _202_603))
in (let t_decls = (let _202_610 = (let _202_609 = (let _202_608 = (let _202_607 = (let _202_606 = (let _202_605 = (let _202_604 = (FStar_Syntax_Print.term_to_string t0)
in Some (_202_604))
in (assumption, _202_605))
in FStar_SMTEncoding_Term.Assume (_202_606))
in (_202_607)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, None)))::_202_608)
in (tdecl)::_202_609)
in (FStar_List.append (FStar_List.append decls decls') _202_610))
in (let _100_770 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(let ttm = (let _202_611 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _202_611))
in (let _100_779 = (encode_term_pred None k env ttm)
in (match (_100_779) with
| (t_has_k, decls) -> begin
(let d = FStar_SMTEncoding_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_100_782) -> begin
(let _100_786 = (FStar_Syntax_Util.head_and_args t0)
in (match (_100_786) with
| (head, args_e) -> begin
(match ((let _202_613 = (let _202_612 = (FStar_Syntax_Subst.compress head)
in _202_612.FStar_Syntax_Syntax.n)
in (_202_613, args_e))) with
| (FStar_Syntax_Syntax.Tm_abs (_100_788), _100_791) -> begin
(let _202_614 = (whnf env t)
in (encode_term _202_614 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (l, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (l, _), _::(v1, _)::(v2, _)::[])) when (FStar_Ident.lid_equals l.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
(let _100_837 = (encode_term v1 env)
in (match (_100_837) with
| (v1, decls1) -> begin
(let _100_840 = (encode_term v2 env)
in (match (_100_840) with
| (v2, decls2) -> begin
(let _202_615 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_202_615, (FStar_List.append decls1 decls2)))
end))
end))
end
| _100_842 -> begin
(let _100_845 = (encode_args args_e env)
in (match (_100_845) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _100_850 = (encode_term head env)
in (match (_100_850) with
| (head, decls') -> begin
(let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(let _100_859 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_100_859) with
| (formals, rest) -> begin
(let subst = (FStar_List.map2 (fun _100_863 _100_867 -> (match ((_100_863, _100_867)) with
| ((bv, _100_862), (a, _100_866)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (let ty = (let _202_620 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _202_620 (FStar_Syntax_Subst.subst subst)))
in (let _100_872 = (encode_term_pred None ty env app_tm)
in (match (_100_872) with
| (has_type, decls'') -> begin
(let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (let e_typing = (let _202_622 = (let _202_621 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_202_621, None))
in FStar_SMTEncoding_Term.Assume (_202_622))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _100_879 = (lookup_free_var_sym env fv)
in (match (_100_879) with
| (fname, fuel_args) -> begin
(let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (let head = (FStar_Syntax_Subst.compress head)
in (let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
x.FStar_Syntax_Syntax.sort
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(let _202_625 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _202_625 Prims.snd))
end
| FStar_Syntax_Syntax.Tm_ascribed (_100_917, t, _100_920) -> begin
t
end
| _100_924 -> begin
(let _202_629 = (let _202_628 = (FStar_Syntax_Print.term_to_string t0)
in (let _202_627 = (FStar_Syntax_Print.tag_of_term head)
in (let _202_626 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format3 "Unexpected head of application %s is: %s, %s" _202_628 _202_627 _202_626))))
in (FStar_All.failwith _202_629))
end)
in (let head_type = (let _202_630 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _202_630))
in (let _100_927 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _202_633 = (FStar_Syntax_Print.term_to_string head)
in (let _202_632 = (FStar_Syntax_Print.tag_of_term head)
in (let _202_631 = (FStar_Syntax_Print.term_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _202_633 _202_632 _202_631))))
end else begin
()
end
in (let _100_931 = (curried_arrow_formals_comp head_type)
in (match (_100_931) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _100_953 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end))))))))
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let _100_962 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_100_962) with
| (bs, body, opening) -> begin
(let fallback = (fun _100_964 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Tm_abs")
in (let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _202_636 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_202_636, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(let _100_968 = (let _202_638 = (let _202_637 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _202_637))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _202_638))
in (fallback ()))
end
| Some (lc) -> begin
if (let _202_639 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _202_639)) then begin
(fallback ())
end else begin
(let c0 = (lc.FStar_Syntax_Syntax.comp ())
in (let c = (FStar_Syntax_Subst.subst_comp opening c0)
in (let _100_980 = (encode_binders None bs env)
in (match (_100_980) with
| (vars, guards, envbody, decls, _100_979) -> begin
(let _100_983 = (encode_term body envbody)
in (match (_100_983) with
| (body, decls') -> begin
(let key_body = (let _202_643 = (let _202_642 = (let _202_641 = (let _202_640 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_202_640, body))
in (FStar_SMTEncoding_Term.mkImp _202_641))
in ([], vars, _202_642))
in (FStar_SMTEncoding_Term.mkForall _202_643))
in (let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _100_989, _100_991) -> begin
(let _202_646 = (let _202_645 = (let _202_644 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _202_644))
in (FStar_SMTEncoding_Term.mkApp _202_645))
in (_202_646, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let fsym = (varops.fresh "Exp_abs")
in (let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (let f = (let _202_648 = (let _202_647 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _202_647))
in (FStar_SMTEncoding_Term.mkApp _202_648))
in (let app = (mk_Apply f vars)
in (let tfun = (FStar_Syntax_Util.arrow bs c)
in (let _100_1006 = (encode_term_pred None tfun env f)
in (match (_100_1006) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _202_650 = (let _202_649 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_202_649, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_202_650))
in (let interp_f = (let _202_657 = (let _202_656 = (let _202_655 = (let _202_654 = (let _202_653 = (let _202_652 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _202_651 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_202_652, _202_651)))
in (FStar_SMTEncoding_Term.mkImp _202_653))
in (((app)::[])::[], (FStar_List.append vars cvars), _202_654))
in (FStar_SMTEncoding_Term.mkForall _202_655))
in (_202_656, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_202_657))
in (let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _100_1010 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_100_1013, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_100_1025); FStar_Syntax_Syntax.lbunivs = _100_1023; FStar_Syntax_Syntax.lbtyp = _100_1021; FStar_Syntax_Syntax.lbeff = _100_1019; FStar_Syntax_Syntax.lbdef = _100_1017}::_100_1015), _100_1031) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _100_1040; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _100_1037; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_100_1050) -> begin
(let _100_1052 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _202_658 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_202_658, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (let _100_1068 = (encode_term e1 env)
in (match (_100_1068) with
| (ee1, decls1) -> begin
(let _100_1071 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_100_1071) with
| (xs, e2) -> begin
(let _100_1075 = (FStar_List.hd xs)
in (match (_100_1075) with
| (x, _100_1074) -> begin
(let env' = (push_term_var env x ee1)
in (let _100_1079 = (encode_term e2 env')
in (match (_100_1079) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (let _100_1087 = (encode_term e env)
in (match (_100_1087) with
| (scr, decls) -> begin
(let _100_1124 = (FStar_List.fold_right (fun b _100_1091 -> (match (_100_1091) with
| (else_case, decls) -> begin
(let _100_1095 = (FStar_Syntax_Subst.open_branch b)
in (match (_100_1095) with
| (p, w, br) -> begin
(let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _100_1099 _100_1102 -> (match ((_100_1099, _100_1102)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _100_1108 -> (match (_100_1108) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (let _100_1118 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _100_1115 = (encode_term w env)
in (match (_100_1115) with
| (w, decls2) -> begin
(let _202_692 = (let _202_691 = (let _202_690 = (let _202_689 = (let _202_688 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _202_688))
in (FStar_SMTEncoding_Term.mkEq _202_689))
in (guard, _202_690))
in (FStar_SMTEncoding_Term.mkAnd _202_691))
in (_202_692, decls2))
end))
end)
in (match (_100_1118) with
| (guard, decls2) -> begin
(let _100_1121 = (encode_br br env)
in (match (_100_1121) with
| (br, decls3) -> begin
(let _202_693 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_202_693, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_100_1124) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _100_1130 -> begin
(let _202_696 = (encode_one_pat env pat)
in (_202_696)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (let _100_1133 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _202_699 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _202_699))
end else begin
()
end
in (let _100_1137 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_100_1137) with
| (vars, pat_term) -> begin
(let _100_1149 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _100_1140 v -> (match (_100_1140) with
| (env, vars) -> begin
(let _100_1146 = (gen_term_var env v)
in (match (_100_1146) with
| (xx, _100_1144, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_100_1149) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_100_1154) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _202_707 = (let _202_706 = (encode_const c)
in (scrutinee, _202_706))
in (FStar_SMTEncoding_Term.mkEq _202_707))
end
| FStar_Syntax_Syntax.Pat_cons ((f, _100_1169), args) -> begin
(let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _100_1179 -> (match (_100_1179) with
| (arg, _100_1178) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _202_710 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _202_710)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_100_1186) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_100_1196) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons ((f, _100_1200), args) -> begin
(let _202_718 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _100_1209 -> (match (_100_1209) with
| (arg, _100_1208) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _202_717 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _202_717)))
end))))
in (FStar_All.pipe_right _202_718 FStar_List.flatten))
end))
in (let pat_term = (fun _100_1212 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (let _100_1228 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _100_1218 _100_1222 -> (match ((_100_1218, _100_1222)) with
| ((tms, decls), (t, _100_1221)) -> begin
(let _100_1225 = (encode_term t env)
in (match (_100_1225) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_100_1228) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (let _100_1234 = (encode_formula_with_labels phi env)
in (match (_100_1234) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _100_1237 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (let rec list_elements = (fun e -> (let _100_1246 = (let _202_733 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _202_733))
in (match (_100_1246) with
| (head, args) -> begin
(match ((let _202_735 = (let _202_734 = (FStar_Syntax_Util.un_uinst head)
in _202_734.FStar_Syntax_Syntax.n)
in (_202_735, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _100_1249), _100_1253) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _100_1257), _100_1269::(hd, _100_1266)::(tl, _100_1262)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid) -> begin
(let _202_736 = (list_elements tl)
in (hd)::_202_736)
end
| _100_1273 -> begin
(let _100_1274 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (let v_or_t_pat = (fun p -> (let _100_1280 = (let _202_739 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _202_739 FStar_Syntax_Util.head_and_args))
in (match (_100_1280) with
| (head, args) -> begin
(match ((let _202_741 = (let _202_740 = (FStar_Syntax_Util.un_uinst head)
in _202_740.FStar_Syntax_Syntax.n)
in (_202_741, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _100_1283), (_100_1291, _100_1293)::(e, _100_1288)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _100_1299), (t, _100_1304)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatT_lid) -> begin
(t, None)
end
| _100_1309 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (let lemma_pats = (fun p -> (let elts = (list_elements p)
in (let smt_pat_or = (fun t -> (let _100_1317 = (let _202_746 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _202_746 FStar_Syntax_Util.head_and_args))
in (match (_100_1317) with
| (head, args) -> begin
(match ((let _202_748 = (let _202_747 = (FStar_Syntax_Util.un_uinst head)
in _202_747.FStar_Syntax_Syntax.n)
in (_202_748, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _100_1320), (e, _100_1325)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _100_1330 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _202_751 = (list_elements e)
in (FStar_All.pipe_right _202_751 (FStar_List.map (fun branch -> (let _202_750 = (list_elements branch)
in (FStar_All.pipe_right _202_750 (FStar_List.map v_or_t_pat)))))))
end
| _100_1337 -> begin
(let _202_752 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_202_752)::[])
end)
end
| _100_1339 -> begin
(let _202_753 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_202_753)::[])
end))))
in (let _100_1373 = (match ((let _202_754 = (FStar_Syntax_Subst.compress t)
in _202_754.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(let _100_1346 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_100_1346) with
| (binders, c) -> begin
(let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _100_1358)::(post, _100_1354)::(pats, _100_1350)::[] -> begin
(let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _202_755 = (lemma_pats pats')
in (binders, pre, post, _202_755)))
end
| _100_1366 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _100_1368 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_100_1373) with
| (binders, pre, post, patterns) -> begin
(let _100_1380 = (encode_binders None binders env)
in (match (_100_1380) with
| (vars, guards, env, decls, _100_1379) -> begin
(let _100_1393 = (let _202_759 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (let _100_1390 = (let _202_758 = (FStar_All.pipe_right branch (FStar_List.map (fun _100_1385 -> (match (_100_1385) with
| (t, _100_1384) -> begin
(encode_term t (let _100_1386 = env
in {bindings = _100_1386.bindings; depth = _100_1386.depth; tcenv = _100_1386.tcenv; warn = _100_1386.warn; cache = _100_1386.cache; nolabels = _100_1386.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _100_1386.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _202_758 FStar_List.unzip))
in (match (_100_1390) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _202_759 FStar_List.unzip))
in (match (_100_1393) with
| (pats, decls') -> begin
(let decls' = (FStar_List.flatten decls')
in (let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _202_762 = (let _202_761 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _202_761 e))
in (_202_762)::p))))
end
| _100_1403 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _202_768 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_202_768)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _202_770 = (let _202_769 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _202_769 tl))
in (aux _202_770 vars))
end
| _100_1415 -> begin
pats
end))
in (let _202_771 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _202_771 vars)))
end)
end)
in (let env = (let _100_1417 = env
in {bindings = _100_1417.bindings; depth = _100_1417.depth; tcenv = _100_1417.tcenv; warn = _100_1417.warn; cache = _100_1417.cache; nolabels = true; use_zfuel_name = _100_1417.use_zfuel_name; encode_non_total_function_typ = _100_1417.encode_non_total_function_typ})
in (let _100_1422 = (let _202_772 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _202_772 env))
in (match (_100_1422) with
| (pre, decls'') -> begin
(let _100_1425 = (let _202_773 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _202_773 env))
in (match (_100_1425) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _202_778 = (let _202_777 = (let _202_776 = (let _202_775 = (let _202_774 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_202_774, post))
in (FStar_SMTEncoding_Term.mkImp _202_775))
in (pats, vars, _202_776))
in (FStar_SMTEncoding_Term.mkForall _202_777))
in (_202_778, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * labels * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (let enc = (fun f l -> (let _100_1439 = (FStar_Util.fold_map (fun decls x -> (let _100_1436 = (encode_term (Prims.fst x) env)
in (match (_100_1436) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_100_1439) with
| (decls, args) -> begin
(let _202_796 = (f args)
in (_202_796, [], decls))
end)))
in (let const_op = (fun f _100_1442 -> (f, [], []))
in (let un_op = (fun f l -> (let _202_810 = (FStar_List.hd l)
in (FStar_All.pipe_left f _202_810)))
in (let bin_op = (fun f _100_8 -> (match (_100_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _100_1453 -> begin
(FStar_All.failwith "Impossible")
end))
in (let enc_prop_c = (fun f l -> (let _100_1473 = (FStar_List.fold_right (fun _100_1461 _100_1465 -> (match ((_100_1461, _100_1465)) with
| ((t, _100_1460), (phis, labs, decls)) -> begin
(let _100_1469 = (encode_formula_with_labels t env)
in (match (_100_1469) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end)) l ([], [], []))
in (match (_100_1473) with
| (phis, labs, decls) -> begin
(let _202_835 = (f phis)
in (_202_835, labs, decls))
end)))
in (let eq_op = (fun _100_9 -> (match (_100_9) with
| _100_1480::_100_1478::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (let mk_imp = (fun _100_10 -> (match (_100_10) with
| (lhs, _100_1491)::(rhs, _100_1487)::[] -> begin
(let _100_1497 = (encode_formula_with_labels rhs env)
in (match (_100_1497) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _100_1500) -> begin
(l1, labs1, decls1)
end
| _100_1504 -> begin
(let _100_1508 = (encode_formula_with_labels lhs env)
in (match (_100_1508) with
| (l2, labs2, decls2) -> begin
(let _202_840 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_202_840, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _100_1510 -> begin
(FStar_All.failwith "impossible")
end))
in (let mk_ite = (fun _100_11 -> (match (_100_11) with
| (guard, _100_1523)::(_then, _100_1519)::(_else, _100_1515)::[] -> begin
(let _100_1529 = (encode_formula_with_labels guard env)
in (match (_100_1529) with
| (g, labs1, decls1) -> begin
(let _100_1533 = (encode_formula_with_labels _then env)
in (match (_100_1533) with
| (t, labs2, decls2) -> begin
(let _100_1537 = (encode_formula_with_labels _else env)
in (match (_100_1537) with
| (e, labs3, decls3) -> begin
(let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _100_1540 -> begin
(FStar_All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _202_852 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _202_852)))
in (let connectives = (let _202_905 = (let _202_861 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _202_861))
in (let _202_904 = (let _202_903 = (let _202_867 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _202_867))
in (let _202_902 = (let _202_901 = (let _202_900 = (let _202_876 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _202_876))
in (let _202_899 = (let _202_898 = (let _202_897 = (let _202_885 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _202_885))
in (_202_897)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_202_898)
in (_202_900)::_202_899))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_202_901)
in (_202_903)::_202_902))
in (_202_905)::_202_904))
in (let fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(let _100_1559 = (encode_formula_with_labels phi' env)
in (match (_100_1559) with
| (phi, labs, decls) -> begin
(let _202_908 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_202_908, [], decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(let _100_1566 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_100_1566) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _100_1573; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _100_1570; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(let _100_1584 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_100_1584) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| _100_1586 -> begin
(let _100_1589 = (encode_term phi env)
in (match (_100_1589) with
| (tt, decls) -> begin
(let _202_909 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_202_909, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _100_1601 = (encode_binders None bs env)
in (match (_100_1601) with
| (vars, guards, env, decls, _100_1600) -> begin
(let _100_1614 = (let _202_921 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (let _100_1611 = (let _202_920 = (FStar_All.pipe_right p (FStar_List.map (fun _100_1606 -> (match (_100_1606) with
| (t, _100_1605) -> begin
(encode_term t (let _100_1607 = env
in {bindings = _100_1607.bindings; depth = _100_1607.depth; tcenv = _100_1607.tcenv; warn = _100_1607.warn; cache = _100_1607.cache; nolabels = _100_1607.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _100_1607.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _202_920 FStar_List.unzip))
in (match (_100_1611) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _202_921 FStar_List.unzip))
in (match (_100_1614) with
| (pats, decls') -> begin
(let _100_1618 = (encode_formula_with_labels body env)
in (match (_100_1618) with
| (body, labs, decls'') -> begin
(let _202_922 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _202_922, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _100_1619 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _202_923 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _202_923))
end else begin
()
end
in (let phi = (FStar_Syntax_Subst.compress phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _100_1631 -> (match (_100_1631) with
| (l, _100_1630) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_100_1634, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(let _100_1644 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _202_940 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _202_940))
end else begin
()
end
in (let _100_1652 = (encode_q_body env vars pats body)
in (match (_100_1652) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _202_943 = (let _202_942 = (let _202_941 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _202_941))
in (FStar_SMTEncoding_Term.mkForall _202_942))
in (_202_943, labs, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(let _100_1665 = (encode_q_body env vars pats body)
in (match (_100_1665) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _202_946 = (let _202_945 = (let _202_944 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _202_944))
in (FStar_SMTEncoding_Term.mkExists _202_945))
in (_202_946, labs, decls))
end))
end))))))))))))))))

# 974 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 974 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 980 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let prims : prims_t = (let _100_1671 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_100_1671) with
| (asym, a) -> begin
(let _100_1674 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_100_1674) with
| (xsym, x) -> begin
(let _100_1677 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_100_1677) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body x -> (let t1 = (let _202_989 = (let _202_988 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _202_988))
in (FStar_SMTEncoding_Term.mkApp _202_989))
in (let vname_decl = (let _202_991 = (let _202_990 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _202_990, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_202_991))
in (let _202_997 = (let _202_996 = (let _202_995 = (let _202_994 = (let _202_993 = (let _202_992 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _202_992))
in (FStar_SMTEncoding_Term.mkForall _202_993))
in (_202_994, None))
in FStar_SMTEncoding_Term.Assume (_202_995))
in (_202_996)::[])
in (vname_decl)::_202_997))))
in (let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (let prims = (let _202_1157 = (let _202_1006 = (let _202_1005 = (let _202_1004 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1004))
in (quant axy _202_1005))
in (FStar_Syntax_Const.op_Eq, _202_1006))
in (let _202_1156 = (let _202_1155 = (let _202_1013 = (let _202_1012 = (let _202_1011 = (let _202_1010 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _202_1010))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1011))
in (quant axy _202_1012))
in (FStar_Syntax_Const.op_notEq, _202_1013))
in (let _202_1154 = (let _202_1153 = (let _202_1022 = (let _202_1021 = (let _202_1020 = (let _202_1019 = (let _202_1018 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1017 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1018, _202_1017)))
in (FStar_SMTEncoding_Term.mkLT _202_1019))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1020))
in (quant xy _202_1021))
in (FStar_Syntax_Const.op_LT, _202_1022))
in (let _202_1152 = (let _202_1151 = (let _202_1031 = (let _202_1030 = (let _202_1029 = (let _202_1028 = (let _202_1027 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1026 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1027, _202_1026)))
in (FStar_SMTEncoding_Term.mkLTE _202_1028))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1029))
in (quant xy _202_1030))
in (FStar_Syntax_Const.op_LTE, _202_1031))
in (let _202_1150 = (let _202_1149 = (let _202_1040 = (let _202_1039 = (let _202_1038 = (let _202_1037 = (let _202_1036 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1035 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1036, _202_1035)))
in (FStar_SMTEncoding_Term.mkGT _202_1037))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1038))
in (quant xy _202_1039))
in (FStar_Syntax_Const.op_GT, _202_1040))
in (let _202_1148 = (let _202_1147 = (let _202_1049 = (let _202_1048 = (let _202_1047 = (let _202_1046 = (let _202_1045 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1044 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1045, _202_1044)))
in (FStar_SMTEncoding_Term.mkGTE _202_1046))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1047))
in (quant xy _202_1048))
in (FStar_Syntax_Const.op_GTE, _202_1049))
in (let _202_1146 = (let _202_1145 = (let _202_1058 = (let _202_1057 = (let _202_1056 = (let _202_1055 = (let _202_1054 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1053 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1054, _202_1053)))
in (FStar_SMTEncoding_Term.mkSub _202_1055))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _202_1056))
in (quant xy _202_1057))
in (FStar_Syntax_Const.op_Subtraction, _202_1058))
in (let _202_1144 = (let _202_1143 = (let _202_1065 = (let _202_1064 = (let _202_1063 = (let _202_1062 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _202_1062))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _202_1063))
in (quant qx _202_1064))
in (FStar_Syntax_Const.op_Minus, _202_1065))
in (let _202_1142 = (let _202_1141 = (let _202_1074 = (let _202_1073 = (let _202_1072 = (let _202_1071 = (let _202_1070 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1069 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1070, _202_1069)))
in (FStar_SMTEncoding_Term.mkAdd _202_1071))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _202_1072))
in (quant xy _202_1073))
in (FStar_Syntax_Const.op_Addition, _202_1074))
in (let _202_1140 = (let _202_1139 = (let _202_1083 = (let _202_1082 = (let _202_1081 = (let _202_1080 = (let _202_1079 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1078 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1079, _202_1078)))
in (FStar_SMTEncoding_Term.mkMul _202_1080))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _202_1081))
in (quant xy _202_1082))
in (FStar_Syntax_Const.op_Multiply, _202_1083))
in (let _202_1138 = (let _202_1137 = (let _202_1092 = (let _202_1091 = (let _202_1090 = (let _202_1089 = (let _202_1088 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1087 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1088, _202_1087)))
in (FStar_SMTEncoding_Term.mkDiv _202_1089))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _202_1090))
in (quant xy _202_1091))
in (FStar_Syntax_Const.op_Division, _202_1092))
in (let _202_1136 = (let _202_1135 = (let _202_1101 = (let _202_1100 = (let _202_1099 = (let _202_1098 = (let _202_1097 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1096 = (FStar_SMTEncoding_Term.unboxInt y)
in (_202_1097, _202_1096)))
in (FStar_SMTEncoding_Term.mkMod _202_1098))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _202_1099))
in (quant xy _202_1100))
in (FStar_Syntax_Const.op_Modulus, _202_1101))
in (let _202_1134 = (let _202_1133 = (let _202_1110 = (let _202_1109 = (let _202_1108 = (let _202_1107 = (let _202_1106 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _202_1105 = (FStar_SMTEncoding_Term.unboxBool y)
in (_202_1106, _202_1105)))
in (FStar_SMTEncoding_Term.mkAnd _202_1107))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1108))
in (quant xy _202_1109))
in (FStar_Syntax_Const.op_And, _202_1110))
in (let _202_1132 = (let _202_1131 = (let _202_1119 = (let _202_1118 = (let _202_1117 = (let _202_1116 = (let _202_1115 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _202_1114 = (FStar_SMTEncoding_Term.unboxBool y)
in (_202_1115, _202_1114)))
in (FStar_SMTEncoding_Term.mkOr _202_1116))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1117))
in (quant xy _202_1118))
in (FStar_Syntax_Const.op_Or, _202_1119))
in (let _202_1130 = (let _202_1129 = (let _202_1126 = (let _202_1125 = (let _202_1124 = (let _202_1123 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _202_1123))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1124))
in (quant qx _202_1125))
in (FStar_Syntax_Const.op_Negation, _202_1126))
in (_202_1129)::[])
in (_202_1131)::_202_1130))
in (_202_1133)::_202_1132))
in (_202_1135)::_202_1134))
in (_202_1137)::_202_1136))
in (_202_1139)::_202_1138))
in (_202_1141)::_202_1140))
in (_202_1143)::_202_1142))
in (_202_1145)::_202_1144))
in (_202_1147)::_202_1146))
in (_202_1149)::_202_1148))
in (_202_1151)::_202_1150))
in (_202_1153)::_202_1152))
in (_202_1155)::_202_1154))
in (_202_1157)::_202_1156))
in (let mk = (fun l v -> (let _202_1189 = (FStar_All.pipe_right prims (FStar_List.filter (fun _100_1697 -> (match (_100_1697) with
| (l', _100_1696) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _202_1189 (FStar_List.collect (fun _100_1701 -> (match (_100_1701) with
| (_100_1699, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _100_1707 -> (match (_100_1707) with
| (l', _100_1706) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1017 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (let mk_unit = (fun _100_1713 tt -> (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _202_1221 = (let _202_1212 = (let _202_1211 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_202_1211, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_202_1212))
in (let _202_1220 = (let _202_1219 = (let _202_1218 = (let _202_1217 = (let _202_1216 = (let _202_1215 = (let _202_1214 = (let _202_1213 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _202_1213))
in (FStar_SMTEncoding_Term.mkImp _202_1214))
in (((typing_pred)::[])::[], (xx)::[], _202_1215))
in (mkForall_fuel _202_1216))
in (_202_1217, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_202_1218))
in (_202_1219)::[])
in (_202_1221)::_202_1220))))
in (let mk_bool = (fun _100_1718 tt -> (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _202_1242 = (let _202_1231 = (let _202_1230 = (let _202_1229 = (let _202_1228 = (let _202_1227 = (let _202_1226 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _202_1226))
in (FStar_SMTEncoding_Term.mkImp _202_1227))
in (((typing_pred)::[])::[], (xx)::[], _202_1228))
in (mkForall_fuel _202_1229))
in (_202_1230, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_202_1231))
in (let _202_1241 = (let _202_1240 = (let _202_1239 = (let _202_1238 = (let _202_1237 = (let _202_1236 = (let _202_1233 = (let _202_1232 = (FStar_SMTEncoding_Term.boxBool b)
in (_202_1232)::[])
in (_202_1233)::[])
in (let _202_1235 = (let _202_1234 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _202_1234 tt))
in (_202_1236, (bb)::[], _202_1235)))
in (FStar_SMTEncoding_Term.mkForall _202_1237))
in (_202_1238, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_202_1239))
in (_202_1240)::[])
in (_202_1242)::_202_1241))))))
in (let mk_int = (fun _100_1725 tt -> (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let precedes = (let _202_1254 = (let _202_1253 = (let _202_1252 = (let _202_1251 = (let _202_1250 = (let _202_1249 = (FStar_SMTEncoding_Term.boxInt a)
in (let _202_1248 = (let _202_1247 = (FStar_SMTEncoding_Term.boxInt b)
in (_202_1247)::[])
in (_202_1249)::_202_1248))
in (tt)::_202_1250)
in (tt)::_202_1251)
in ("Prims.Precedes", _202_1252))
in (FStar_SMTEncoding_Term.mkApp _202_1253))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _202_1254))
in (let precedes_y_x = (let _202_1255 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _202_1255))
in (let _202_1297 = (let _202_1261 = (let _202_1260 = (let _202_1259 = (let _202_1258 = (let _202_1257 = (let _202_1256 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _202_1256))
in (FStar_SMTEncoding_Term.mkImp _202_1257))
in (((typing_pred)::[])::[], (xx)::[], _202_1258))
in (mkForall_fuel _202_1259))
in (_202_1260, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_202_1261))
in (let _202_1296 = (let _202_1295 = (let _202_1269 = (let _202_1268 = (let _202_1267 = (let _202_1266 = (let _202_1263 = (let _202_1262 = (FStar_SMTEncoding_Term.boxInt b)
in (_202_1262)::[])
in (_202_1263)::[])
in (let _202_1265 = (let _202_1264 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _202_1264 tt))
in (_202_1266, (bb)::[], _202_1265)))
in (FStar_SMTEncoding_Term.mkForall _202_1267))
in (_202_1268, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_202_1269))
in (let _202_1294 = (let _202_1293 = (let _202_1292 = (let _202_1291 = (let _202_1290 = (let _202_1289 = (let _202_1288 = (let _202_1287 = (let _202_1286 = (let _202_1285 = (let _202_1284 = (let _202_1283 = (let _202_1272 = (let _202_1271 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _202_1270 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_202_1271, _202_1270)))
in (FStar_SMTEncoding_Term.mkGT _202_1272))
in (let _202_1282 = (let _202_1281 = (let _202_1275 = (let _202_1274 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _202_1273 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_202_1274, _202_1273)))
in (FStar_SMTEncoding_Term.mkGTE _202_1275))
in (let _202_1280 = (let _202_1279 = (let _202_1278 = (let _202_1277 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _202_1276 = (FStar_SMTEncoding_Term.unboxInt x)
in (_202_1277, _202_1276)))
in (FStar_SMTEncoding_Term.mkLT _202_1278))
in (_202_1279)::[])
in (_202_1281)::_202_1280))
in (_202_1283)::_202_1282))
in (typing_pred_y)::_202_1284)
in (typing_pred)::_202_1285)
in (FStar_SMTEncoding_Term.mk_and_l _202_1286))
in (_202_1287, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _202_1288))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _202_1289))
in (mkForall_fuel _202_1290))
in (_202_1291, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_202_1292))
in (_202_1293)::[])
in (_202_1295)::_202_1294))
in (_202_1297)::_202_1296)))))))))))
in (let mk_int_alias = (fun _100_1737 tt -> (let _202_1306 = (let _202_1305 = (let _202_1304 = (let _202_1303 = (let _202_1302 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _202_1302))
in (FStar_SMTEncoding_Term.mkEq _202_1303))
in (_202_1304, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_202_1305))
in (_202_1306)::[]))
in (let mk_str = (fun _100_1741 tt -> (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _202_1327 = (let _202_1316 = (let _202_1315 = (let _202_1314 = (let _202_1313 = (let _202_1312 = (let _202_1311 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _202_1311))
in (FStar_SMTEncoding_Term.mkImp _202_1312))
in (((typing_pred)::[])::[], (xx)::[], _202_1313))
in (mkForall_fuel _202_1314))
in (_202_1315, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_202_1316))
in (let _202_1326 = (let _202_1325 = (let _202_1324 = (let _202_1323 = (let _202_1322 = (let _202_1321 = (let _202_1318 = (let _202_1317 = (FStar_SMTEncoding_Term.boxString b)
in (_202_1317)::[])
in (_202_1318)::[])
in (let _202_1320 = (let _202_1319 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _202_1319 tt))
in (_202_1321, (bb)::[], _202_1320)))
in (FStar_SMTEncoding_Term.mkForall _202_1322))
in (_202_1323, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_202_1324))
in (_202_1325)::[])
in (_202_1327)::_202_1326))))))
in (let mk_ref = (fun reft_name _100_1749 -> (let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let refa = (let _202_1334 = (let _202_1333 = (let _202_1332 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_202_1332)::[])
in (reft_name, _202_1333))
in (FStar_SMTEncoding_Term.mkApp _202_1334))
in (let refb = (let _202_1337 = (let _202_1336 = (let _202_1335 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_202_1335)::[])
in (reft_name, _202_1336))
in (FStar_SMTEncoding_Term.mkApp _202_1337))
in (let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _202_1356 = (let _202_1343 = (let _202_1342 = (let _202_1341 = (let _202_1340 = (let _202_1339 = (let _202_1338 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _202_1338))
in (FStar_SMTEncoding_Term.mkImp _202_1339))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _202_1340))
in (mkForall_fuel _202_1341))
in (_202_1342, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_202_1343))
in (let _202_1355 = (let _202_1354 = (let _202_1353 = (let _202_1352 = (let _202_1351 = (let _202_1350 = (let _202_1349 = (let _202_1348 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _202_1347 = (let _202_1346 = (let _202_1345 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _202_1344 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_202_1345, _202_1344)))
in (FStar_SMTEncoding_Term.mkEq _202_1346))
in (_202_1348, _202_1347)))
in (FStar_SMTEncoding_Term.mkImp _202_1349))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _202_1350))
in (mkForall_fuel' 2 _202_1351))
in (_202_1352, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_202_1353))
in (_202_1354)::[])
in (_202_1356)::_202_1355))))))))))
in (let mk_false_interp = (fun _100_1759 false_tm -> (let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _202_1363 = (let _202_1362 = (let _202_1361 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_202_1361, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_202_1362))
in (_202_1363)::[])))
in (let mk_and_interp = (fun conj _100_1765 -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let valid = (let _202_1370 = (let _202_1369 = (let _202_1368 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_202_1368)::[])
in ("Valid", _202_1369))
in (FStar_SMTEncoding_Term.mkApp _202_1370))
in (let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _202_1377 = (let _202_1376 = (let _202_1375 = (let _202_1374 = (let _202_1373 = (let _202_1372 = (let _202_1371 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_202_1371, valid))
in (FStar_SMTEncoding_Term.mkIff _202_1372))
in (((valid)::[])::[], (aa)::(bb)::[], _202_1373))
in (FStar_SMTEncoding_Term.mkForall _202_1374))
in (_202_1375, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_202_1376))
in (_202_1377)::[])))))))))
in (let mk_or_interp = (fun disj _100_1776 -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let valid = (let _202_1384 = (let _202_1383 = (let _202_1382 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_202_1382)::[])
in ("Valid", _202_1383))
in (FStar_SMTEncoding_Term.mkApp _202_1384))
in (let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _202_1391 = (let _202_1390 = (let _202_1389 = (let _202_1388 = (let _202_1387 = (let _202_1386 = (let _202_1385 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_202_1385, valid))
in (FStar_SMTEncoding_Term.mkIff _202_1386))
in (((valid)::[])::[], (aa)::(bb)::[], _202_1387))
in (FStar_SMTEncoding_Term.mkForall _202_1388))
in (_202_1389, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_202_1390))
in (_202_1391)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (let valid = (let _202_1398 = (let _202_1397 = (let _202_1396 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_202_1396)::[])
in ("Valid", _202_1397))
in (FStar_SMTEncoding_Term.mkApp _202_1398))
in (let _202_1405 = (let _202_1404 = (let _202_1403 = (let _202_1402 = (let _202_1401 = (let _202_1400 = (let _202_1399 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_202_1399, valid))
in (FStar_SMTEncoding_Term.mkIff _202_1400))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _202_1401))
in (FStar_SMTEncoding_Term.mkForall _202_1402))
in (_202_1403, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_202_1404))
in (_202_1405)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let valid = (let _202_1412 = (let _202_1411 = (let _202_1410 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_202_1410)::[])
in ("Valid", _202_1411))
in (FStar_SMTEncoding_Term.mkApp _202_1412))
in (let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _202_1419 = (let _202_1418 = (let _202_1417 = (let _202_1416 = (let _202_1415 = (let _202_1414 = (let _202_1413 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_202_1413, valid))
in (FStar_SMTEncoding_Term.mkIff _202_1414))
in (((valid)::[])::[], (aa)::(bb)::[], _202_1415))
in (FStar_SMTEncoding_Term.mkForall _202_1416))
in (_202_1417, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_202_1418))
in (_202_1419)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let valid = (let _202_1426 = (let _202_1425 = (let _202_1424 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_202_1424)::[])
in ("Valid", _202_1425))
in (FStar_SMTEncoding_Term.mkApp _202_1426))
in (let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _202_1433 = (let _202_1432 = (let _202_1431 = (let _202_1430 = (let _202_1429 = (let _202_1428 = (let _202_1427 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_202_1427, valid))
in (FStar_SMTEncoding_Term.mkIff _202_1428))
in (((valid)::[])::[], (aa)::(bb)::[], _202_1429))
in (FStar_SMTEncoding_Term.mkForall _202_1430))
in (_202_1431, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_202_1432))
in (_202_1433)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let valid = (let _202_1440 = (let _202_1439 = (let _202_1438 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_202_1438)::[])
in ("Valid", _202_1439))
in (FStar_SMTEncoding_Term.mkApp _202_1440))
in (let valid_b_x = (let _202_1443 = (let _202_1442 = (let _202_1441 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_202_1441)::[])
in ("Valid", _202_1442))
in (FStar_SMTEncoding_Term.mkApp _202_1443))
in (let _202_1457 = (let _202_1456 = (let _202_1455 = (let _202_1454 = (let _202_1453 = (let _202_1452 = (let _202_1451 = (let _202_1450 = (let _202_1449 = (let _202_1445 = (let _202_1444 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_202_1444)::[])
in (_202_1445)::[])
in (let _202_1448 = (let _202_1447 = (let _202_1446 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_202_1446, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _202_1447))
in (_202_1449, (xx)::[], _202_1448)))
in (FStar_SMTEncoding_Term.mkForall _202_1450))
in (_202_1451, valid))
in (FStar_SMTEncoding_Term.mkIff _202_1452))
in (((valid)::[])::[], (aa)::(bb)::[], _202_1453))
in (FStar_SMTEncoding_Term.mkForall _202_1454))
in (_202_1455, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_202_1456))
in (_202_1457)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let valid = (let _202_1464 = (let _202_1463 = (let _202_1462 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_202_1462)::[])
in ("Valid", _202_1463))
in (FStar_SMTEncoding_Term.mkApp _202_1464))
in (let valid_b_x = (let _202_1467 = (let _202_1466 = (let _202_1465 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_202_1465)::[])
in ("Valid", _202_1466))
in (FStar_SMTEncoding_Term.mkApp _202_1467))
in (let _202_1481 = (let _202_1480 = (let _202_1479 = (let _202_1478 = (let _202_1477 = (let _202_1476 = (let _202_1475 = (let _202_1474 = (let _202_1473 = (let _202_1469 = (let _202_1468 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_202_1468)::[])
in (_202_1469)::[])
in (let _202_1472 = (let _202_1471 = (let _202_1470 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_202_1470, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _202_1471))
in (_202_1473, (xx)::[], _202_1472)))
in (FStar_SMTEncoding_Term.mkExists _202_1474))
in (_202_1475, valid))
in (FStar_SMTEncoding_Term.mkIff _202_1476))
in (((valid)::[])::[], (aa)::(bb)::[], _202_1477))
in (FStar_SMTEncoding_Term.mkForall _202_1478))
in (_202_1479, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_202_1480))
in (_202_1481)::[]))))))))))
in (let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _100_1847 -> (match (_100_1847) with
| (l, _100_1846) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_100_1850, f) -> begin
(f s tt)
end)))))))))))))))))))))

# 1165 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (let _100_1856 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _202_1624 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _202_1624))
end else begin
()
end
in (let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (let _100_1864 = (encode_sigelt' env se)
in (match (_100_1864) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _202_1627 = (let _202_1626 = (let _202_1625 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_202_1625))
in (_202_1626)::[])
in (_202_1627, e))
end
| _100_1867 -> begin
(let _202_1634 = (let _202_1633 = (let _202_1629 = (let _202_1628 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_202_1628))
in (_202_1629)::g)
in (let _202_1632 = (let _202_1631 = (let _202_1630 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_202_1630))
in (_202_1631)::[])
in (FStar_List.append _202_1633 _202_1632)))
in (_202_1634, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (let should_skip = (fun l -> false)
in (let encode_top_level_val = (fun env lid t quals -> (let tt = (whnf env t)
in (let _100_1880 = (encode_free_var env lid t tt quals)
in (match (_100_1880) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _202_1648 = (let _202_1647 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _202_1647))
in (_202_1648, env))
end else begin
(decls, env)
end
end))))
in (let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _100_1887 lb -> (match (_100_1887) with
| (decls, env) -> begin
(let _100_1891 = (let _202_1657 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _202_1657 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_100_1891) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _100_1909, _100_1911, _100_1913, _100_1915) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(let _100_1921 = (new_term_constant_and_tok_from_lid env lid)
in (match (_100_1921) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _100_1924, t, quals, _100_1928) -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _100_12 -> (match (_100_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _100_1940 -> begin
false
end)))) || env.tcenv.FStar_TypeChecker_Env.is_iface) then begin
(let _100_1943 = (encode_top_level_val env lid t quals)
in (match (_100_1943) with
| (decls, env) -> begin
(let tname = lid.FStar_Ident.str
in (let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _202_1660 = (let _202_1659 = (primitive_type_axioms lid tname tsym)
in (FStar_List.append decls _202_1659))
in (_202_1660, env))))
end))
end else begin
([], env)
end
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _100_1949, _100_1951) -> begin
(let _100_1956 = (encode_formula f env)
in (match (_100_1956) with
| (f, decls) -> begin
(let g = (let _202_1664 = (let _202_1663 = (let _202_1662 = (let _202_1661 = (FStar_Util.format1 "Assumption: %s" (FStar_Syntax_Print.lid_to_string l))
in Some (_202_1661))
in (f, _202_1662))
in FStar_SMTEncoding_Term.Assume (_202_1663))
in (_202_1664)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _100_1961, _100_1963) when (FStar_All.pipe_right (Prims.snd lbs) (FStar_Util.for_some (fun lb -> (let _202_1666 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (should_skip _202_1666))))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_100_1968, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _100_1976; FStar_Syntax_Syntax.lbtyp = _100_1974; FStar_Syntax_Syntax.lbeff = _100_1972; FStar_Syntax_Syntax.lbdef = _100_1970}::[]), _100_1983, _100_1985, _100_1987) when (FStar_Ident.lid_equals b2t FStar_Syntax_Const.b2t_lid) -> begin
(let _100_1993 = (new_term_constant_and_tok_from_lid env b2t)
in (match (_100_1993) with
| (tname, ttok, env) -> begin
(let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (let valid_b2t_x = (let _202_1669 = (let _202_1668 = (let _202_1667 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_202_1667)::[])
in ("Valid", _202_1668))
in (FStar_SMTEncoding_Term.mkApp _202_1669))
in (let decls = (let _202_1677 = (let _202_1676 = (let _202_1675 = (let _202_1674 = (let _202_1673 = (let _202_1672 = (let _202_1671 = (let _202_1670 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _202_1670))
in (FStar_SMTEncoding_Term.mkEq _202_1671))
in (((valid_b2t_x)::[])::[], (xx)::[], _202_1672))
in (FStar_SMTEncoding_Term.mkForall _202_1673))
in (_202_1674, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_202_1675))
in (_202_1676)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_202_1677)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_100_1999, _100_2001, _100_2003, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _100_13 -> (match (_100_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _100_2013 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _100_2019, _100_2021, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _100_14 -> (match (_100_14) with
| FStar_Syntax_Syntax.Projector (_100_2027) -> begin
true
end
| _100_2030 -> begin
false
end)))) -> begin
(let l = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (match ((try_lookup_free_var env l)) with
| Some (_100_2033) -> begin
([], env)
end
| None -> begin
(let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _100_2041, _100_2043, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (FStar_List.length binders)
in (let _100_2055 = (FStar_Util.first_N nbinders formals)
in (match (_100_2055) with
| (formals, extra_formals) -> begin
(let subst = (FStar_List.map2 (fun _100_2059 _100_2063 -> (match ((_100_2059, _100_2063)) with
| ((formal, _100_2058), (binder, _100_2062)) -> begin
(let _202_1691 = (let _202_1690 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _202_1690))
in FStar_Syntax_Syntax.NT (_202_1691))
end)) formals binders)
in (let extra_formals = (let _202_1695 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _100_2067 -> (match (_100_2067) with
| (x, i) -> begin
(let _202_1694 = (let _100_2068 = x
in (let _202_1693 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _100_2068.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _100_2068.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _202_1693}))
in (_202_1694, i))
end))))
in (FStar_All.pipe_right _202_1695 FStar_Syntax_Util.name_binders))
in (let body = (let _202_1702 = (FStar_Syntax_Subst.compress body)
in (let _202_1701 = (let _202_1696 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _202_1696))
in (let _202_1700 = (let _202_1699 = (let _202_1698 = (FStar_Syntax_Subst.subst subst t)
in _202_1698.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _202_1697 -> Some (_202_1697)) _202_1699))
in (FStar_Syntax_Syntax.extend_app_n _202_1702 _202_1701 _202_1700 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (let rec destruct_bound_function = (fun flid t_norm e -> (match ((let _202_1709 = (FStar_Syntax_Util.unascribe e)
in _202_1709.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(let _100_2084 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_100_2084) with
| (binders, body, opening) -> begin
(match ((let _202_1710 = (FStar_Syntax_Subst.compress t_norm)
in _202_1710.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(let _100_2091 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_100_2091) with
| (formals, c) -> begin
(let nformals = (FStar_List.length formals)
in (let nbinders = (FStar_List.length binders)
in (let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(let lopt = (subst_lcomp_opt opening lopt)
in (let _100_2098 = (FStar_Util.first_N nformals binders)
in (match (_100_2098) with
| (bs0, rest) -> begin
(let c = (let subst = (FStar_List.map2 (fun _100_2102 _100_2106 -> (match ((_100_2102, _100_2106)) with
| ((b, _100_2101), (x, _100_2105)) -> begin
(let _202_1714 = (let _202_1713 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _202_1713))
in FStar_Syntax_Syntax.NT (_202_1714))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(let _100_2112 = (eta_expand binders formals body tres)
in (match (_100_2112) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| _100_2114 -> begin
(let _202_1717 = (let _202_1716 = (FStar_Syntax_Print.term_to_string e)
in (let _202_1715 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _202_1716 _202_1715)))
in (FStar_All.failwith _202_1717))
end)
end))
end
| _100_2116 -> begin
(match ((let _202_1718 = (FStar_Syntax_Subst.compress t_norm)
in _202_1718.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(let _100_2123 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_100_2123) with
| (formals, c) -> begin
(let tres = (FStar_Syntax_Util.comp_result c)
in (let _100_2127 = (eta_expand [] formals e tres)
in (match (_100_2127) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _100_2129 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _100_2131 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(let _100_2157 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _100_2144 lb -> (match (_100_2144) with
| (toks, typs, decls, env) -> begin
(let _100_2146 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (let _100_2152 = (let _202_1723 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _202_1723 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_100_2152) with
| (tok, decl, env) -> begin
(let _202_1726 = (let _202_1725 = (let _202_1724 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_202_1724, tok))
in (_202_1725)::toks)
in (_202_1726, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_100_2157) with
| (toks, typs, decls, env) -> begin
(let toks = (FStar_List.rev toks)
in (let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _100_15 -> (match (_100_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _100_2164 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _202_1729 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _202_1729)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _100_2174; FStar_Syntax_Syntax.lbunivs = _100_2172; FStar_Syntax_Syntax.lbtyp = _100_2170; FStar_Syntax_Syntax.lbeff = _100_2168; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let e = (FStar_Syntax_Subst.compress e)
in (let _100_2193 = (destruct_bound_function flid t_norm e)
in (match (_100_2193) with
| (binders, body, _100_2190, _100_2192) -> begin
(let _100_2200 = (encode_binders None binders env)
in (match (_100_2200) with
| (vars, guards, env', binder_decls, _100_2199) -> begin
(let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _100_2203 -> begin
(let _202_1731 = (let _202_1730 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _202_1730))
in (FStar_SMTEncoding_Term.mkApp _202_1731))
end)
in (let _100_2209 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _202_1733 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _202_1732 = (encode_formula body env')
in (_202_1733, _202_1732)))
end else begin
(let _202_1734 = (encode_term body env')
in (app, _202_1734))
end
in (match (_100_2209) with
| (app, (body, decls2)) -> begin
(let eqn = (let _202_1743 = (let _202_1742 = (let _202_1739 = (let _202_1738 = (let _202_1737 = (let _202_1736 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _202_1735 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_202_1736, _202_1735)))
in (FStar_SMTEncoding_Term.mkImp _202_1737))
in (((app)::[])::[], vars, _202_1738))
in (FStar_SMTEncoding_Term.mkForall _202_1739))
in (let _202_1741 = (let _202_1740 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_202_1740))
in (_202_1742, _202_1741)))
in FStar_SMTEncoding_Term.Assume (_202_1743))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end)))
end
| _100_2212 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let fuel = (let _202_1744 = (varops.fresh "fuel")
in (_202_1744, FStar_SMTEncoding_Term.Fuel_sort))
in (let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (let env0 = env
in (let _100_2229 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _100_2218 _100_2223 -> (match ((_100_2218, _100_2223)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _202_1749 = (let _202_1748 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _202_1747 -> Some (_202_1747)) _202_1748))
in (push_free_var env flid gtok _202_1749))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_100_2229) with
| (gtoks, env) -> begin
(let gtoks = (FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _100_2238 t_norm _100_2249 -> (match ((_100_2238, _100_2249)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _100_2248; FStar_Syntax_Syntax.lbunivs = _100_2246; FStar_Syntax_Syntax.lbtyp = _100_2244; FStar_Syntax_Syntax.lbeff = _100_2242; FStar_Syntax_Syntax.lbdef = e}) -> begin
(let _100_2254 = (destruct_bound_function flid t_norm e)
in (match (_100_2254) with
| (binders, body, formals, tres) -> begin
(let _100_2261 = (encode_binders None binders env)
in (match (_100_2261) with
| (vars, guards, env', binder_decls, _100_2260) -> begin
(let decl_g = (let _202_1760 = (let _202_1759 = (let _202_1758 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_202_1758)
in (g, _202_1759, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_202_1760))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (let gsapp = (let _202_1763 = (let _202_1762 = (let _202_1761 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_202_1761)::vars_tm)
in (g, _202_1762))
in (FStar_SMTEncoding_Term.mkApp _202_1763))
in (let gmax = (let _202_1766 = (let _202_1765 = (let _202_1764 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_202_1764)::vars_tm)
in (g, _202_1765))
in (FStar_SMTEncoding_Term.mkApp _202_1766))
in (let _100_2271 = (encode_term body env')
in (match (_100_2271) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _202_1775 = (let _202_1774 = (let _202_1771 = (let _202_1770 = (let _202_1769 = (let _202_1768 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _202_1767 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_202_1768, _202_1767)))
in (FStar_SMTEncoding_Term.mkImp _202_1769))
in (((gsapp)::[])::[], (fuel)::vars, _202_1770))
in (FStar_SMTEncoding_Term.mkForall _202_1771))
in (let _202_1773 = (let _202_1772 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_202_1772))
in (_202_1774, _202_1773)))
in FStar_SMTEncoding_Term.Assume (_202_1775))
in (let eqn_f = (let _202_1779 = (let _202_1778 = (let _202_1777 = (let _202_1776 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _202_1776))
in (FStar_SMTEncoding_Term.mkForall _202_1777))
in (_202_1778, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_202_1779))
in (let eqn_g' = (let _202_1788 = (let _202_1787 = (let _202_1786 = (let _202_1785 = (let _202_1784 = (let _202_1783 = (let _202_1782 = (let _202_1781 = (let _202_1780 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_202_1780)::vars_tm)
in (g, _202_1781))
in (FStar_SMTEncoding_Term.mkApp _202_1782))
in (gsapp, _202_1783))
in (FStar_SMTEncoding_Term.mkEq _202_1784))
in (((gsapp)::[])::[], (fuel)::vars, _202_1785))
in (FStar_SMTEncoding_Term.mkForall _202_1786))
in (_202_1787, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_202_1788))
in (let _100_2294 = (let _100_2281 = (encode_binders None formals env0)
in (match (_100_2281) with
| (vars, v_guards, env, binder_decls, _100_2280) -> begin
(let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _202_1789 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _202_1789 ((fuel)::vars)))
in (let _202_1793 = (let _202_1792 = (let _202_1791 = (let _202_1790 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _202_1790))
in (FStar_SMTEncoding_Term.mkForall _202_1791))
in (_202_1792, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_202_1793)))
in (let _100_2291 = (let _100_2288 = (encode_term_pred None tres env gapp)
in (match (_100_2288) with
| (g_typing, d3) -> begin
(let _202_1801 = (let _202_1800 = (let _202_1799 = (let _202_1798 = (let _202_1797 = (let _202_1796 = (let _202_1795 = (let _202_1794 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_202_1794, g_typing))
in (FStar_SMTEncoding_Term.mkImp _202_1795))
in (((gapp)::[])::[], (fuel)::vars, _202_1796))
in (FStar_SMTEncoding_Term.mkForall _202_1797))
in (_202_1798, None))
in FStar_SMTEncoding_Term.Assume (_202_1799))
in (_202_1800)::[])
in (d3, _202_1801))
end))
in (match (_100_2291) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_100_2294) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _100_2310 = (let _202_1804 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _100_2298 _100_2302 -> (match ((_100_2298, _100_2302)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _100_2306 = (encode_one_binding env0 gtok ty bs)
in (match (_100_2306) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _202_1804))
in (match (_100_2310) with
| (decls, eqns, env0) -> begin
(let _100_2319 = (let _202_1806 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _202_1806 (FStar_List.partition (fun _100_16 -> (match (_100_16) with
| FStar_SMTEncoding_Term.DeclFun (_100_2313) -> begin
true
end
| _100_2316 -> begin
false
end)))))
in (match (_100_2319) with
| (prefix_decls, rest) -> begin
(let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _100_2130 -> (match (_100_2130) with
| Let_rec_unencodeable -> begin
(let msg = (let _202_1809 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _202_1809 (FStar_String.concat " and ")))
in (let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _100_2323, _100_2325, _100_2327) -> begin
(let _100_2332 = (encode_signature env ses)
in (match (_100_2332) with
| (g, env) -> begin
(let _100_2344 = (FStar_All.pipe_right g (FStar_List.partition (fun _100_17 -> (match (_100_17) with
| FStar_SMTEncoding_Term.Assume (_100_2335, Some ("inversion axiom")) -> begin
false
end
| _100_2341 -> begin
true
end))))
in (match (_100_2344) with
| (g', inversions) -> begin
(let _100_2353 = (FStar_All.pipe_right g' (FStar_List.partition (fun _100_18 -> (match (_100_18) with
| FStar_SMTEncoding_Term.DeclFun (_100_2347) -> begin
true
end
| _100_2350 -> begin
false
end))))
in (match (_100_2353) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _100_2356, tps, k, _100_2360, datas, quals, _100_2364) -> begin
(let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _100_19 -> (match (_100_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _100_2371 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(let _100_2381 = c
in (match (_100_2381) with
| (name, args, _100_2378, _100_2380) -> begin
(let _202_1817 = (let _202_1816 = (let _202_1815 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _202_1815, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_202_1816))
in (_202_1817)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _202_1823 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _202_1823 FStar_Option.isNone)))))) then begin
[]
end else begin
(let _100_2388 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_100_2388) with
| (xxsym, xx) -> begin
(let _100_2424 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _100_2391 l -> (match (_100_2391) with
| (out, decls) -> begin
(let _100_2396 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_100_2396) with
| (_100_2394, data_t) -> begin
(let _100_2399 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_100_2399) with
| (args, res) -> begin
(let indices = (match ((let _202_1826 = (FStar_Syntax_Subst.compress res)
in _202_1826.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_100_2401, indices) -> begin
indices
end
| _100_2406 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _100_2412 -> (match (_100_2412) with
| (x, _100_2411) -> begin
(let _202_1831 = (let _202_1830 = (let _202_1829 = (mk_term_projector_name l x)
in (_202_1829, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _202_1830))
in (push_term_var env x _202_1831))
end)) env))
in (let _100_2416 = (encode_args indices env)
in (match (_100_2416) with
| (indices, decls') -> begin
(let _100_2417 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (let eqs = (let _202_1836 = (FStar_List.map2 (fun v a -> (let _202_1835 = (let _202_1834 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_202_1834, a))
in (FStar_SMTEncoding_Term.mkEq _202_1835))) vars indices)
in (FStar_All.pipe_right _202_1836 FStar_SMTEncoding_Term.mk_and_l))
in (let _202_1841 = (let _202_1840 = (let _202_1839 = (let _202_1838 = (let _202_1837 = (mk_data_tester env l xx)
in (_202_1837, eqs))
in (FStar_SMTEncoding_Term.mkAnd _202_1838))
in (out, _202_1839))
in (FStar_SMTEncoding_Term.mkOr _202_1840))
in (_202_1841, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_100_2424) with
| (data_ax, decls) -> begin
(let _100_2427 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_100_2427) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _202_1842 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _202_1842 xx tapp))
in (let _202_1849 = (let _202_1848 = (let _202_1847 = (let _202_1846 = (let _202_1845 = (let _202_1844 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _202_1843 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _202_1844, _202_1843)))
in (FStar_SMTEncoding_Term.mkForall _202_1845))
in (_202_1846, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_202_1847))
in (_202_1848)::[])
in (FStar_List.append decls _202_1849)))
end))
end))
end))
end)
in (let _100_2437 = (match ((let _202_1850 = (FStar_Syntax_Subst.compress k)
in _202_1850.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _100_2434 -> begin
(tps, k)
end)
in (match (_100_2437) with
| (formals, res) -> begin
(let _100_2440 = (FStar_Syntax_Subst.open_term formals res)
in (match (_100_2440) with
| (formals, res) -> begin
(let _100_2447 = (encode_binders None formals env)
in (match (_100_2447) with
| (vars, guards, env', binder_decls, _100_2446) -> begin
(let pretype_axioms = (fun tapp vars -> (let _100_2453 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_100_2453) with
| (xxsym, xx) -> begin
(let _100_2456 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_100_2456) with
| (ffsym, ff) -> begin
(let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _202_1863 = (let _202_1862 = (let _202_1861 = (let _202_1860 = (let _202_1859 = (let _202_1858 = (let _202_1857 = (let _202_1856 = (let _202_1855 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _202_1855))
in (FStar_SMTEncoding_Term.mkEq _202_1856))
in (xx_has_type, _202_1857))
in (FStar_SMTEncoding_Term.mkImp _202_1858))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _202_1859))
in (FStar_SMTEncoding_Term.mkForall _202_1860))
in (_202_1861, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_202_1862))
in (_202_1863)::[]))
end))
end)))
in (let _100_2461 = (new_term_constant_and_tok_from_lid env t)
in (match (_100_2461) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let tapp = (let _202_1865 = (let _202_1864 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _202_1864))
in (FStar_SMTEncoding_Term.mkApp _202_1865))
in (let _100_2482 = (let tname_decl = (let _202_1869 = (let _202_1868 = (FStar_All.pipe_right vars (FStar_List.map (fun _100_2467 -> (match (_100_2467) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _202_1867 = (varops.next_id ())
in (tname, _202_1868, FStar_SMTEncoding_Term.Term_sort, _202_1867)))
in (constructor_or_logic_type_decl _202_1869))
in (let _100_2479 = (match (vars) with
| [] -> begin
(let _202_1873 = (let _202_1872 = (let _202_1871 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _202_1870 -> Some (_202_1870)) _202_1871))
in (push_free_var env t tname _202_1872))
in ([], _202_1873))
end
| _100_2471 -> begin
(let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (let ttok_fresh = (let _202_1874 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _202_1874))
in (let ttok_app = (mk_Apply ttok_tm vars)
in (let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (let name_tok_corr = (let _202_1878 = (let _202_1877 = (let _202_1876 = (let _202_1875 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _202_1875))
in (FStar_SMTEncoding_Term.mkForall' _202_1876))
in (_202_1877, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_202_1878))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_100_2479) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_100_2482) with
| (decls, env) -> begin
(let kindingAx = (let _100_2485 = (encode_term_pred None res env' tapp)
in (match (_100_2485) with
| (k, decls) -> begin
(let karr = if ((FStar_List.length formals) > 0) then begin
(let _202_1882 = (let _202_1881 = (let _202_1880 = (let _202_1879 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _202_1879))
in (_202_1880, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_202_1881))
in (_202_1882)::[])
end else begin
[]
end
in (let _202_1888 = (let _202_1887 = (let _202_1886 = (let _202_1885 = (let _202_1884 = (let _202_1883 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _202_1883))
in (FStar_SMTEncoding_Term.mkForall _202_1884))
in (_202_1885, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_202_1886))
in (_202_1887)::[])
in (FStar_List.append (FStar_List.append decls karr) _202_1888)))
end))
in (let aux = (let _202_1891 = (let _202_1889 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _202_1889))
in (let _202_1890 = (pretype_axioms tapp vars)
in (FStar_List.append _202_1891 _202_1890)))
in (let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _100_2492, _100_2494, _100_2496, _100_2498, _100_2500, _100_2502, _100_2504) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _100_2509, t, _100_2512, n_tps, quals, _100_2516, drange) -> begin
(let _100_2523 = (new_term_constant_and_tok_from_lid env d)
in (match (_100_2523) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (let _100_2527 = (FStar_Syntax_Util.arrow_formals t)
in (match (_100_2527) with
| (formals, t_res) -> begin
(let _100_2530 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_100_2530) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _100_2537 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_100_2537) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _202_1893 = (mk_term_projector_name d x)
in (_202_1893, FStar_SMTEncoding_Term.Term_sort)))))
in (let datacons = (let _202_1895 = (let _202_1894 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _202_1894))
in (FStar_All.pipe_right _202_1895 FStar_SMTEncoding_Term.constructor_to_decl))
in (let app = (mk_Apply ddtok_tm vars)
in (let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (let _100_2547 = (encode_term_pred None t env ddtok_tm)
in (match (_100_2547) with
| (tok_typing, decls3) -> begin
(let _100_2554 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_100_2554) with
| (vars', guards', env'', decls_formals, _100_2553) -> begin
(let _100_2559 = (let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_100_2559) with
| (ty_pred', decls_pred) -> begin
(let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _100_2563 -> begin
(let _202_1897 = (let _202_1896 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _202_1896))
in (_202_1897)::[])
end)
in (let encode_elim = (fun _100_2566 -> (match (()) with
| () -> begin
(let _100_2569 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_100_2569) with
| (head, args) -> begin
(match ((let _202_1900 = (FStar_Syntax_Subst.compress head)
in _202_1900.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(let encoded_head = (lookup_free_var_name env' fv)
in (let _100_2593 = (encode_args args env')
in (match (_100_2593) with
| (encoded_args, arg_decls) -> begin
(let _100_2608 = (FStar_List.fold_left (fun _100_2597 arg -> (match (_100_2597) with
| (env, arg_vars, eqns) -> begin
(let _100_2603 = (let _202_1903 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _202_1903))
in (match (_100_2603) with
| (_100_2600, xv, env) -> begin
(let _202_1905 = (let _202_1904 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_202_1904)::eqns)
in (env, (xv)::arg_vars, _202_1905))
end))
end)) (env', [], []) encoded_args)
in (match (_100_2608) with
| (_100_2605, arg_vars, eqns) -> begin
(let arg_vars = (FStar_List.rev arg_vars)
in (let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _202_1912 = (let _202_1911 = (let _202_1910 = (let _202_1909 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _202_1908 = (let _202_1907 = (let _202_1906 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _202_1906))
in (FStar_SMTEncoding_Term.mkImp _202_1907))
in (((ty_pred)::[])::[], _202_1909, _202_1908)))
in (FStar_SMTEncoding_Term.mkForall _202_1910))
in (_202_1911, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_202_1912))
in (let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(let x = (let _202_1913 = (varops.fresh "x")
in (_202_1913, FStar_SMTEncoding_Term.Term_sort))
in (let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _202_1923 = (let _202_1922 = (let _202_1921 = (let _202_1920 = (let _202_1915 = (let _202_1914 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_202_1914)::[])
in (_202_1915)::[])
in (let _202_1919 = (let _202_1918 = (let _202_1917 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _202_1916 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_202_1917, _202_1916)))
in (FStar_SMTEncoding_Term.mkImp _202_1918))
in (_202_1920, (x)::[], _202_1919)))
in (FStar_SMTEncoding_Term.mkForall _202_1921))
in (_202_1922, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_202_1923))))
end else begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _202_1926 = (let _202_1925 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _202_1925 dapp))
in (_202_1926)::[])
end
| _100_2622 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _202_1933 = (let _202_1932 = (let _202_1931 = (let _202_1930 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _202_1929 = (let _202_1928 = (let _202_1927 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _202_1927))
in (FStar_SMTEncoding_Term.mkImp _202_1928))
in (((ty_pred)::[])::[], _202_1930, _202_1929)))
in (FStar_SMTEncoding_Term.mkForall _202_1931))
in (_202_1932, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_202_1933)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _100_2626 -> begin
(let _100_2627 = (let _202_1935 = (let _202_1934 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" (FStar_Syntax_Print.lid_to_string d) _202_1934))
in (FStar_TypeChecker_Errors.warn drange _202_1935))
in ([], []))
end)
end))
end))
in (let _100_2631 = (encode_elim ())
in (match (_100_2631) with
| (decls2, elim) -> begin
(let g = (let _202_1959 = (let _202_1958 = (let _202_1943 = (let _202_1942 = (let _202_1941 = (let _202_1940 = (let _202_1939 = (let _202_1938 = (let _202_1937 = (let _202_1936 = (FStar_Util.format1 "data constructor proxy: %s" (FStar_Syntax_Print.lid_to_string d))
in Some (_202_1936))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _202_1937))
in FStar_SMTEncoding_Term.DeclFun (_202_1938))
in (_202_1939)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _202_1940))
in (FStar_List.append _202_1941 proxy_fresh))
in (FStar_List.append _202_1942 decls_formals))
in (FStar_List.append _202_1943 decls_pred))
in (let _202_1957 = (let _202_1956 = (let _202_1955 = (let _202_1947 = (let _202_1946 = (let _202_1945 = (let _202_1944 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _202_1944))
in (FStar_SMTEncoding_Term.mkForall _202_1945))
in (_202_1946, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_202_1947))
in (let _202_1954 = (let _202_1953 = (let _202_1952 = (let _202_1951 = (let _202_1950 = (let _202_1949 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _202_1948 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _202_1949, _202_1948)))
in (FStar_SMTEncoding_Term.mkForall _202_1950))
in (_202_1951, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_202_1952))
in (_202_1953)::[])
in (_202_1955)::_202_1954))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_202_1956)
in (FStar_List.append _202_1958 _202_1957)))
in (FStar_List.append _202_1959 elim))
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
(let _100_2640 = (encode_free_var env x t t_norm [])
in (match (_100_2640) with
| (decls, env) -> begin
(let _100_2645 = (lookup_lid env x)
in (match (_100_2645) with
| (n, x', _100_2644) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _100_2649) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env lid t -> (let _100_2657 = (encode_function_type_as_formula None None t env)
in (match (_100_2657) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _202_1972 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _202_1972)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(let _100_2666 = (new_term_constant_and_tok_from_lid env lid)
in (match (_100_2666) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match ((let _202_1973 = (FStar_Syntax_Subst.compress t_norm)
in _202_1973.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _100_2669) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _100_2672 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _100_2675 -> begin
[]
end)
in (let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(let vname = (varops.new_fvar lid)
in (let definition = (prims.mk lid vname)
in (let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (let _100_2690 = (let _100_2685 = (curried_arrow_formals_comp t_norm)
in (match (_100_2685) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _202_1975 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _202_1975))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_100_2690) with
| (formals, (pre_opt, res_t)) -> begin
(let _100_2694 = (new_term_constant_and_tok_from_lid env lid)
in (match (_100_2694) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _100_2697 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _100_20 -> (match (_100_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(let _100_2713 = (FStar_Util.prefix vars)
in (match (_100_2713) with
| (_100_2708, (xxsym, _100_2711)) -> begin
(let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _202_1992 = (let _202_1991 = (let _202_1990 = (let _202_1989 = (let _202_1988 = (let _202_1987 = (let _202_1986 = (let _202_1985 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _202_1985))
in (vapp, _202_1986))
in (FStar_SMTEncoding_Term.mkEq _202_1987))
in (((vapp)::[])::[], vars, _202_1988))
in (FStar_SMTEncoding_Term.mkForall _202_1989))
in (_202_1990, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_202_1991))
in (_202_1992)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(let _100_2725 = (FStar_Util.prefix vars)
in (match (_100_2725) with
| (_100_2720, (xxsym, _100_2723)) -> begin
(let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (let prim_app = (let _202_1994 = (let _202_1993 = (mk_term_projector_name d f)
in (_202_1993, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _202_1994))
in (let _202_1999 = (let _202_1998 = (let _202_1997 = (let _202_1996 = (let _202_1995 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _202_1995))
in (FStar_SMTEncoding_Term.mkForall _202_1996))
in (_202_1997, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_202_1998))
in (_202_1999)::[]))))
end))
end
| _100_2730 -> begin
[]
end)))))
in (let _100_2737 = (encode_binders None formals env)
in (match (_100_2737) with
| (vars, guards, env', decls1, _100_2736) -> begin
(let _100_2746 = (match (pre_opt) with
| None -> begin
(let _202_2000 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_202_2000, decls1))
end
| Some (p) -> begin
(let _100_2743 = (encode_formula p env')
in (match (_100_2743) with
| (g, ds) -> begin
(let _202_2001 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_202_2001, (FStar_List.append decls1 ds)))
end))
end)
in (match (_100_2746) with
| (guard, decls1) -> begin
(let vtok_app = (mk_Apply vtok_tm vars)
in (let vapp = (let _202_2003 = (let _202_2002 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _202_2002))
in (FStar_SMTEncoding_Term.mkApp _202_2003))
in (let _100_2770 = (let vname_decl = (let _202_2006 = (let _202_2005 = (FStar_All.pipe_right formals (FStar_List.map (fun _100_2749 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _202_2005, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_202_2006))
in (let _100_2757 = (let env = (let _100_2752 = env
in {bindings = _100_2752.bindings; depth = _100_2752.depth; tcenv = _100_2752.tcenv; warn = _100_2752.warn; cache = _100_2752.cache; nolabels = _100_2752.nolabels; use_zfuel_name = _100_2752.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_100_2757) with
| (tok_typing, decls2) -> begin
(let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _100_2767 = (match (formals) with
| [] -> begin
(let _202_2010 = (let _202_2009 = (let _202_2008 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _202_2007 -> Some (_202_2007)) _202_2008))
in (push_free_var env lid vname _202_2009))
in ((FStar_List.append decls2 ((tok_typing)::[])), _202_2010))
end
| _100_2761 -> begin
(let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let vtok_fresh = (let _202_2011 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _202_2011))
in (let name_tok_corr = (let _202_2015 = (let _202_2014 = (let _202_2013 = (let _202_2012 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _202_2012))
in (FStar_SMTEncoding_Term.mkForall _202_2013))
in (_202_2014, None))
in FStar_SMTEncoding_Term.Assume (_202_2015))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_100_2767) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_100_2770) with
| (decls2, env) -> begin
(let _100_2778 = (let res_t = (FStar_Syntax_Subst.compress res_t)
in (let _100_2774 = (encode_term res_t env')
in (match (_100_2774) with
| (encoded_res_t, decls) -> begin
(let _202_2016 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _202_2016, decls))
end)))
in (match (_100_2778) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _202_2020 = (let _202_2019 = (let _202_2018 = (let _202_2017 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _202_2017))
in (FStar_SMTEncoding_Term.mkForall _202_2018))
in (_202_2019, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_202_2020))
in (let g = (let _202_2022 = (let _202_2021 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_202_2021)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _202_2022))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _100_2785 se -> (match (_100_2785) with
| (g, env) -> begin
(let _100_2789 = (encode_sigelt env se)
in (match (_100_2789) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1654 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (let encode_binding = (fun b _100_2796 -> (match (_100_2796) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_100_2798) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(let _100_2805 = (new_term_constant env x)
in (match (_100_2805) with
| (xxsym, xx, env') -> begin
(let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _100_2807 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _202_2037 = (FStar_Syntax_Print.bv_to_string x)
in (let _202_2036 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _202_2035 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _202_2037 _202_2036 _202_2035))))
end else begin
()
end
in (let _100_2811 = (encode_term_pred None t1 env xx)
in (match (_100_2811) with
| (t, decls') -> begin
(let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _202_2041 = (let _202_2040 = (FStar_Syntax_Print.bv_to_string x)
in (let _202_2039 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _202_2038 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _202_2040 _202_2039 _202_2038))))
in Some (_202_2041))
end else begin
None
end
in (let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((FStar_SMTEncoding_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_100_2816, t)) -> begin
(let t_norm = (whnf env t)
in (let _100_2824 = (encode_free_var env x t t_norm [])
in (match (_100_2824) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(let _100_2838 = (encode_sigelt env se)
in (match (_100_2838) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1711 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let encode_labels = (fun labs -> (let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _100_2845 -> (match (_100_2845) with
| (l, _100_2842, _100_2844) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _100_2852 -> (match (_100_2852) with
| (l, _100_2849, _100_2851) -> begin
(let _202_2049 = (FStar_All.pipe_left (fun _202_2045 -> FStar_SMTEncoding_Term.Echo (_202_2045)) (Prims.fst l))
in (let _202_2048 = (let _202_2047 = (let _202_2046 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_202_2046))
in (_202_2047)::[])
in (_202_2049)::_202_2048))
end))))
in (prefix, suffix))))

# 1717 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1718 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _202_2054 = (let _202_2053 = (let _202_2052 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _202_2052; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_202_2053)::[])
in (FStar_ST.op_Colon_Equals last_env _202_2054)))

# 1721 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_100_2858 -> begin
(let _100_2861 = e
in {bindings = _100_2861.bindings; depth = _100_2861.depth; tcenv = tcenv; warn = _100_2861.warn; cache = _100_2861.cache; nolabels = _100_2861.nolabels; use_zfuel_name = _100_2861.use_zfuel_name; encode_non_total_function_typ = _100_2861.encode_non_total_function_typ})
end))

# 1724 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _100_2867::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1727 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let push_env : Prims.unit  ->  Prims.unit = (fun _100_2869 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (FStar_Util.smap_copy hd.cache)
in (let top = (let _100_2875 = hd
in {bindings = _100_2875.bindings; depth = _100_2875.depth; tcenv = _100_2875.tcenv; warn = _100_2875.warn; cache = refs; nolabels = _100_2875.nolabels; use_zfuel_name = _100_2875.use_zfuel_name; encode_non_total_function_typ = _100_2875.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1733 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let pop_env : Prims.unit  ->  Prims.unit = (fun _100_2878 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _100_2882::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1736 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mark_env : Prims.unit  ->  Prims.unit = (fun _100_2884 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1737 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _100_2885 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1738 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _100_2886 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_100_2889::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _100_2894 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1744 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _100_2896 = (init_env tcenv)
in (let _100_2898 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1748 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let push : Prims.string  ->  Prims.unit = (fun msg -> (let _100_2901 = (push_env ())
in (let _100_2903 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1752 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let pop : Prims.string  ->  Prims.unit = (fun msg -> (let _100_2906 = (let _202_2075 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _202_2075))
in (let _100_2908 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1756 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let mark : Prims.string  ->  Prims.unit = (fun msg -> (let _100_2911 = (mark_env ())
in (let _100_2913 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1760 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (let _100_2916 = (reset_mark_env ())
in (let _100_2918 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1764 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let commit_mark = (fun msg -> (let _100_2921 = (commit_mark_env ())
in (let _100_2923 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1768 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _202_2091 = (let _202_2090 = (let _202_2089 = (let _202_2088 = (let _202_2087 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _202_2087 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _202_2088 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _202_2089))
in FStar_SMTEncoding_Term.Caption (_202_2090))
in (_202_2091)::decls)
end else begin
decls
end)
in (let env = (get_env tcenv)
in (let _100_2932 = (encode_sigelt env se)
in (match (_100_2932) with
| (decls, env) -> begin
(let _100_2933 = (set_env env)
in (let _202_2092 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _202_2092)))
end)))))

# 1778 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (let _100_2938 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _202_2097 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _202_2097))
end else begin
()
end
in (let env = (get_env tcenv)
in (let _100_2945 = (encode_signature (let _100_2941 = env
in {bindings = _100_2941.bindings; depth = _100_2941.depth; tcenv = _100_2941.tcenv; warn = false; cache = _100_2941.cache; nolabels = _100_2941.nolabels; use_zfuel_name = _100_2941.use_zfuel_name; encode_non_total_function_typ = _100_2941.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_100_2945) with
| (decls, env) -> begin
(let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (let _100_2951 = (set_env (let _100_2949 = env
in {bindings = _100_2949.bindings; depth = _100_2949.depth; tcenv = _100_2949.tcenv; warn = true; cache = _100_2949.cache; nolabels = _100_2949.nolabels; use_zfuel_name = _100_2949.use_zfuel_name; encode_non_total_function_typ = _100_2949.encode_non_total_function_typ}))
in (let _100_2953 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1794 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let solve : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (let _100_2958 = (let _202_2105 = (let _202_2104 = (FStar_All.pipe_left FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range tcenv))
in (FStar_Util.format1 "Starting query at %s" _202_2104))
in (push _202_2105))
in (let pop = (fun _100_2961 -> (match (()) with
| () -> begin
(let _202_2109 = (let _202_2108 = (FStar_All.pipe_left FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range tcenv))
in (FStar_Util.format1 "Ending query at %s" _202_2108))
in (pop _202_2109))
end))
in (let _100_3015 = (let env = (get_env tcenv)
in (let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _100_2985 = (let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(let _100_2974 = (aux rest)
in (match (_100_2974) with
| (out, rest) -> begin
(let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (((FStar_Syntax_Syntax.mk_binder (let _100_2976 = x
in {FStar_Syntax_Syntax.ppname = _100_2976.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _100_2976.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})))::out, rest))
end))
end
| _100_2979 -> begin
([], bindings)
end))
in (let _100_2982 = (aux bindings)
in (match (_100_2982) with
| (closing, bindings) -> begin
(let _202_2114 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_202_2114, bindings))
end)))
in (match (_100_2985) with
| (q, bindings) -> begin
(let _100_2994 = (let _202_2116 = (FStar_List.filter (fun _100_21 -> (match (_100_21) with
| FStar_TypeChecker_Env.Binding_sig (_100_2988) -> begin
false
end
| _100_2991 -> begin
true
end)) bindings)
in (encode_env_bindings env _202_2116))
in (match (_100_2994) with
| (env_decls, env) -> begin
(let _100_2995 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _202_2117 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _202_2117))
end else begin
()
end
in (let _100_2999 = (encode_formula q env)
in (match (_100_2999) with
| (phi, qdecls) -> begin
(let _100_3004 = (FStar_SMTEncoding_ErrorReporting.label_goals [] phi [])
in (match (_100_3004) with
| (phi, labels, _100_3003) -> begin
(let _100_3007 = (encode_labels labels)
in (match (_100_3007) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _202_2119 = (let _202_2118 = (FStar_SMTEncoding_Term.mkNot phi)
in (_202_2118, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_202_2119))
in (let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_100_3015) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _100_3022); FStar_SMTEncoding_Term.hash = _100_3019; FStar_SMTEncoding_Term.freevars = _100_3017}, _100_3027) -> begin
(let _100_3030 = (pop ())
in ())
end
| _100_3033 when tcenv.FStar_TypeChecker_Env.admit -> begin
(let _100_3034 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _100_3038) -> begin
(let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (let _100_3042 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _100_3048 -> (match (_100_3048) with
| (n, i) -> begin
(let _202_2142 = (let _202_2141 = (let _202_2126 = (let _202_2125 = (FStar_Util.string_of_int n)
in (let _202_2124 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _202_2125 _202_2124)))
in FStar_SMTEncoding_Term.Caption (_202_2126))
in (let _202_2140 = (let _202_2139 = (let _202_2131 = (let _202_2130 = (let _202_2129 = (let _202_2128 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _202_2127 = (FStar_SMTEncoding_Term.n_fuel n)
in (_202_2128, _202_2127)))
in (FStar_SMTEncoding_Term.mkEq _202_2129))
in (_202_2130, None))
in FStar_SMTEncoding_Term.Assume (_202_2131))
in (let _202_2138 = (let _202_2137 = (let _202_2136 = (let _202_2135 = (let _202_2134 = (let _202_2133 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _202_2132 = (FStar_SMTEncoding_Term.n_fuel i)
in (_202_2133, _202_2132)))
in (FStar_SMTEncoding_Term.mkEq _202_2134))
in (_202_2135, None))
in FStar_SMTEncoding_Term.Assume (_202_2136))
in (_202_2137)::(p)::(FStar_SMTEncoding_Term.CheckSat)::[])
in (_202_2139)::_202_2138))
in (_202_2141)::_202_2140))
in (FStar_List.append _202_2142 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _202_2146 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _202_2145 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_202_2146, _202_2145)))
in (let alt_configs = (let _202_2165 = (let _202_2164 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _202_2149 = (let _202_2148 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _202_2147 = (FStar_ST.read FStar_Options.max_ifuel)
in (_202_2148, _202_2147)))
in (_202_2149)::[])
end else begin
[]
end
in (let _202_2163 = (let _202_2162 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _202_2152 = (let _202_2151 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _202_2150 = (FStar_ST.read FStar_Options.max_ifuel)
in (_202_2151, _202_2150)))
in (_202_2152)::[])
end else begin
[]
end
in (let _202_2161 = (let _202_2160 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _202_2155 = (let _202_2154 = (FStar_ST.read FStar_Options.max_fuel)
in (let _202_2153 = (FStar_ST.read FStar_Options.max_ifuel)
in (_202_2154, _202_2153)))
in (_202_2155)::[])
end else begin
[]
end
in (let _202_2159 = (let _202_2158 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _202_2157 = (let _202_2156 = (FStar_ST.read FStar_Options.min_fuel)
in (_202_2156, 1))
in (_202_2157)::[])
end else begin
[]
end
in (_202_2158)::[])
in (_202_2160)::_202_2159))
in (_202_2162)::_202_2161))
in (_202_2164)::_202_2163))
in (FStar_List.flatten _202_2165))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _100_3057 -> begin
errs
end)
in (let _100_3059 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _202_2172 = (FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range tcenv))
in (let _202_2171 = (let _202_2168 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _202_2168 FStar_Util.string_of_int))
in (let _202_2170 = (let _202_2169 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _202_2169 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _202_2172 _202_2171 _202_2170))))
end else begin
()
end
in (FStar_TypeChecker_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun p errs _100_22 -> (match (_100_22) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _202_2183 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _202_2183 (cb mi p [])))
end
| _100_3071 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _202_2185 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _202_2185 (fun _100_3077 -> (match (_100_3077) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _100_3080 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _100_3083 p alt _100_3088 -> (match ((_100_3083, _100_3088)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _202_2192 = (FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range tcenv))
in (let _202_2191 = (FStar_Util.string_of_int prev_fuel)
in (let _202_2190 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _202_2192 _202_2191 _202_2190))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _202_2193 = (with_fuel p initial_config)
in (FStar_SMTEncoding_Z3.ask fresh labels _202_2193 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let _100_3093 = (let _202_2199 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _202_2199 q))
in (match (_100_3093) with
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
in (let _100_3094 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _100_3097 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1893 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (let env = (get_env tcenv)
in (let _100_3101 = (push "query")
in (let _100_3108 = (encode_formula_with_labels q env)
in (match (_100_3108) with
| (f, _100_3105, _100_3107) -> begin
(let _100_3109 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _100_3113) -> begin
true
end
| _100_3117 -> begin
false
end))
end)))))

# 1902 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1916 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\encode.fs"

let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _100_3118 -> ()); FStar_TypeChecker_Env.push = (fun _100_3120 -> ()); FStar_TypeChecker_Env.pop = (fun _100_3122 -> ()); FStar_TypeChecker_Env.mark = (fun _100_3124 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _100_3126 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _100_3128 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _100_3130 _100_3132 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _100_3134 _100_3136 -> ()); FStar_TypeChecker_Env.solve = (fun _100_3138 _100_3140 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _100_3142 _100_3144 -> false); FStar_TypeChecker_Env.finish = (fun _100_3146 -> ()); FStar_TypeChecker_Env.refresh = (fun _100_3147 -> ())}





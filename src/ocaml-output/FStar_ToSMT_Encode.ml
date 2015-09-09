
let add_fuel = (fun x tl -> (match ((FStar_ST.read FStar_Options.unthrottle_inductives)) with
| true -> begin
tl
end
| false -> begin
(x)::tl
end))

let withenv = (fun c _53_40 -> (match (_53_40) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (FStar_List.filter (fun _53_1 -> (match (_53_1) with
| (FStar_Util.Inl (_53_44), _53_47) -> begin
false
end
| _53_50 -> begin
true
end)) args))

let escape = (fun s -> (FStar_Util.replace_char s '\'' '_'))

let escape_null_name = (fun a -> (match ((a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText = "_")) with
| true -> begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText a.FStar_Absyn_Syntax.realname.FStar_Absyn_Syntax.idText)
end
| false -> begin
a.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText
end))

let mk_typ_projector_name = (fun lid a -> (let _119_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _119_14)))

let mk_term_projector_name = (fun lid a -> (let a = (let _119_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _119_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _119_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _119_20))))

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _53_62 -> (match (()) with
| () -> begin
(let _119_30 = (let _119_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _119_29 lid.FStar_Absyn_Syntax.str))
in (FStar_All.failwith _119_30))
end))
in (let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _119_31 = (FStar_Absyn_Util.compress_typ t)
in _119_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_66) -> begin
(match (((i < 0) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| false -> begin
(let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(mk_typ_projector_name lid a.FStar_Absyn_Syntax.v)
end
| FStar_Util.Inr (x) -> begin
(mk_term_projector_name lid x.FStar_Absyn_Syntax.v)
end))
end)
end
| _53_75 -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun lid i -> (let _119_37 = (let _119_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str _119_36))
in (FStar_All.pipe_left escape _119_37)))

let mk_typ_projector = (fun lid a -> (let _119_43 = (let _119_42 = (mk_typ_projector_name lid a)
in (_119_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _119_43)))

let mk_term_projector = (fun lid a -> (let _119_49 = (let _119_48 = (mk_term_projector_name lid a)
in (_119_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _119_49)))

let mk_term_projector_by_pos = (fun lid i -> (let _119_55 = (let _119_54 = (mk_term_projector_name_by_pos lid i)
in (_119_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _119_55)))

let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Absyn_Syntax.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.ident  ->  Prims.string; new_fvar : FStar_Absyn_Syntax.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _53_101 -> (match (()) with
| () -> begin
(let _119_159 = (FStar_Util.smap_create 100)
in (let _119_158 = (FStar_Util.smap_create 100)
in (_119_159, _119_158)))
end))
in (let scopes = (let _119_161 = (let _119_160 = (new_scope ())
in (_119_160)::[])
in (FStar_Util.mk_ref _119_161))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _119_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _119_165 (fun _53_109 -> (match (_53_109) with
| (names, _53_108) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_53_112) -> begin
(let _53_114 = (FStar_Util.incr ctr)
in (let _119_167 = (let _119_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _119_166))
in (Prims.strcat (Prims.strcat y "__") _119_167)))
end)
in (let top_scope = (let _119_169 = (let _119_168 = (FStar_ST.read scopes)
in (FStar_List.hd _119_168))
in (FStar_All.pipe_left Prims.fst _119_169))
in (let _53_118 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _119_175 = (let _119_174 = (FStar_All.pipe_left mk_unique pp.FStar_Absyn_Syntax.idText)
in (Prims.strcat _119_174 "__"))
in (Prims.strcat _119_175 rn.FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Absyn_Syntax.str))
in (let next_id = (fun _53_126 -> (match (()) with
| () -> begin
(let _53_127 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _119_183 = (let _119_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _119_182))
in (FStar_Util.format2 "%s_%s" pfx _119_183)))
in (let string_const = (fun s -> (match ((let _119_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _119_187 (fun _53_136 -> (match (_53_136) with
| (_53_134, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _119_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _119_188))
in (let top_scope = (let _119_190 = (let _119_189 = (FStar_ST.read scopes)
in (FStar_List.hd _119_189))
in (FStar_All.pipe_left Prims.snd _119_190))
in (let _53_143 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _53_146 -> (match (()) with
| () -> begin
(let _119_195 = (let _119_194 = (new_scope ())
in (let _119_193 = (FStar_ST.read scopes)
in (_119_194)::_119_193))
in (FStar_ST.op_Colon_Equals scopes _119_195))
end))
in (let pop = (fun _53_148 -> (match (()) with
| () -> begin
(let _119_199 = (let _119_198 = (FStar_ST.read scopes)
in (FStar_List.tl _119_198))
in (FStar_ST.op_Colon_Equals scopes _119_199))
end))
in (let mark = (fun _53_150 -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _53_152 -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _53_154 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _53_167 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (let _53_172 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _53_175 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun x -> (let _119_215 = (let _119_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _119_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_119_214, _119_213)))
in (FStar_Absyn_Util.mkbvd _119_215)))

type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term)
| Binding_tvar of (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term)
| Binding_fvar of (FStar_Absyn_Syntax.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option)
| Binding_ftvar of (FStar_Absyn_Syntax.lident * Prims.string * FStar_ToSMT_Term.term Prims.option)

let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_tvar = (fun _discr_ -> (match (_discr_) with
| Binding_tvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_ftvar = (fun _discr_ -> (match (_discr_) with
| Binding_ftvar (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_53_180) -> begin
_53_180
end))

let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_53_183) -> begin
_53_183
end))

let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_53_186) -> begin
_53_186
end))

let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_53_189) -> begin
_53_189
end))

let binder_of_eithervar = (fun v -> (v, None))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

let is_Mkenv_t = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))

let print_env = (fun e -> (let _119_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _53_2 -> (match (_53_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _53_214) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _119_301 (FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

let caption_t = (fun env t -> (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _119_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_119_311))
end
| false -> begin
None
end))

let fresh_fvar = (fun x s -> (let xsym = (varops.fresh x)
in (let _119_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _119_316))))

let gen_term_var = (fun env x -> (let ysym = (let _119_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _119_321))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _53_233 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _53_233.tcenv; warn = _53_233.warn; cache = _53_233.cache; nolabels = _53_233.nolabels; use_zfuel_name = _53_233.use_zfuel_name; encode_non_total_function_typ = _53_233.encode_non_total_function_typ})))))

let new_term_constant = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _53_239 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _53_239.depth; tcenv = _53_239.tcenv; warn = _53_239.warn; cache = _53_239.cache; nolabels = _53_239.nolabels; use_zfuel_name = _53_239.use_zfuel_name; encode_non_total_function_typ = _53_239.encode_non_total_function_typ})))))

let push_term_var = (fun env x t -> (let _53_244 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _53_244.depth; tcenv = _53_244.tcenv; warn = _53_244.warn; cache = _53_244.cache; nolabels = _53_244.nolabels; use_zfuel_name = _53_244.use_zfuel_name; encode_non_total_function_typ = _53_244.encode_non_total_function_typ}))

let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _53_3 -> (match (_53_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _53_254 -> begin
None
end)))) with
| None -> begin
(let _119_336 = (let _119_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _119_335))
in (FStar_All.failwith _119_336))
end
| Some (b, t) -> begin
t
end))

let gen_typ_var = (fun env x -> (let ysym = (let _119_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _119_341))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _53_264 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _53_264.tcenv; warn = _53_264.warn; cache = _53_264.cache; nolabels = _53_264.nolabels; use_zfuel_name = _53_264.use_zfuel_name; encode_non_total_function_typ = _53_264.encode_non_total_function_typ})))))

let new_typ_constant = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _53_270 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _53_270.depth; tcenv = _53_270.tcenv; warn = _53_270.warn; cache = _53_270.cache; nolabels = _53_270.nolabels; use_zfuel_name = _53_270.use_zfuel_name; encode_non_total_function_typ = _53_270.encode_non_total_function_typ})))))

let push_typ_var = (fun env x t -> (let _53_275 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _53_275.depth; tcenv = _53_275.tcenv; warn = _53_275.warn; cache = _53_275.cache; nolabels = _53_275.nolabels; use_zfuel_name = _53_275.use_zfuel_name; encode_non_total_function_typ = _53_275.encode_non_total_function_typ}))

let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _53_4 -> (match (_53_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _53_285 -> begin
None
end)))) with
| None -> begin
(let _119_356 = (let _119_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _119_355))
in (FStar_All.failwith _119_356))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _119_367 = (let _53_295 = env
in (let _119_366 = (let _119_365 = (let _119_364 = (let _119_363 = (let _119_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _119_361 -> Some (_119_361)) _119_362))
in (x, fname, _119_363, None))
in Binding_fvar (_119_364))
in (_119_365)::env.bindings)
in {bindings = _119_366; depth = _53_295.depth; tcenv = _53_295.tcenv; warn = _53_295.warn; cache = _53_295.cache; nolabels = _53_295.nolabels; use_zfuel_name = _53_295.use_zfuel_name; encode_non_total_function_typ = _53_295.encode_non_total_function_typ}))
in (fname, ftok, _119_367)))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _53_5 -> (match (_53_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _53_307 -> begin
None
end))))

let lookup_lid = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _119_378 = (let _119_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _119_377))
in (FStar_All.failwith _119_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun env x fname ftok -> (let _53_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _53_317.depth; tcenv = _53_317.tcenv; warn = _53_317.warn; cache = _53_317.cache; nolabels = _53_317.nolabels; use_zfuel_name = _53_317.use_zfuel_name; encode_non_total_function_typ = _53_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun env x f -> (let _53_326 = (lookup_lid env x)
in (match (_53_326) with
| (t1, t2, _53_325) -> begin
(let t3 = (let _119_395 = (let _119_394 = (let _119_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_119_393)::[])
in (f, _119_394))
in (FStar_ToSMT_Term.mkApp _119_395))
in (let _53_328 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _53_328.depth; tcenv = _53_328.tcenv; warn = _53_328.warn; cache = _53_328.cache; nolabels = _53_328.nolabels; use_zfuel_name = _53_328.use_zfuel_name; encode_non_total_function_typ = _53_328.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun env a -> (let _53_335 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_335) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _53_339 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_53_343, fuel::[]) -> begin
(match ((let _119_399 = (let _119_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _119_398 Prims.fst))
in (FStar_Util.starts_with _119_399 "fuel"))) with
| true -> begin
(let _119_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _119_400 fuel))
end
| false -> begin
t
end)
end
| _53_349 -> begin
t
end)
end
| _53_351 -> begin
(let _119_402 = (let _119_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _119_401))
in (FStar_All.failwith _119_402))
end)
end)
end)))

let lookup_free_var_name = (fun env a -> (let _53_359 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_359) with
| (x, _53_356, _53_358) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _53_365 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_365) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _53_369; FStar_ToSMT_Term.freevars = _53_367}) when env.use_zfuel_name -> begin
(g, zf)
end
| _53_377 -> begin
(match (sym) with
| None -> begin
(FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _53_387 -> begin
(FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _119_417 = (let _53_392 = env
in (let _119_416 = (let _119_415 = (let _119_414 = (let _119_413 = (let _119_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _119_411 -> Some (_119_411)) _119_412))
in (x, fname, _119_413))
in Binding_ftvar (_119_414))
in (_119_415)::env.bindings)
in {bindings = _119_416; depth = _53_392.depth; tcenv = _53_392.tcenv; warn = _53_392.warn; cache = _53_392.cache; nolabels = _53_392.nolabels; use_zfuel_name = _53_392.use_zfuel_name; encode_non_total_function_typ = _53_392.encode_non_total_function_typ}))
in (fname, ftok, _119_417)))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _53_6 -> (match (_53_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _53_403 -> begin
None
end)))) with
| None -> begin
(let _119_424 = (let _119_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _119_423))
in (FStar_All.failwith _119_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun env x fname ftok -> (let _53_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _53_411.depth; tcenv = _53_411.tcenv; warn = _53_411.warn; cache = _53_411.cache; nolabels = _53_411.nolabels; use_zfuel_name = _53_411.use_zfuel_name; encode_non_total_function_typ = _53_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun env a -> (match ((let _119_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _119_435 Prims.snd))) with
| None -> begin
(let _119_437 = (let _119_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _119_436))
in (FStar_All.failwith _119_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> (let _119_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _119_440 Prims.fst)))

let tok_of_name = (fun env nm -> (FStar_Util.find_map env.bindings (fun _53_7 -> (match (_53_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _53_436 -> begin
None
end))))

let mkForall_fuel' = (fun n _53_441 -> (match (_53_441) with
| (pats, vars, body) -> begin
(let fallback = (fun _53_443 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in (match ((FStar_ST.read FStar_Options.unthrottle_inductives)) with
| true -> begin
(fallback ())
end
| false -> begin
(let _53_446 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_446) with
| (fsym, fterm) -> begin
(let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _53_456 -> begin
p
end)))))
in (let pats = (add_fuel pats)
in (let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, guard::body'::[]) -> begin
(let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _119_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _119_453))
end
| _53_469 -> begin
(let _119_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _119_454 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp (guard, body')))
end
| _53_472 -> begin
body
end)
in (let vars = ((fsym, FStar_ToSMT_Term.Fuel_sort))::vars
in (FStar_ToSMT_Term.mkForall (pats, vars, body))))))
end))
end))
end))

let mkForall_fuel = (mkForall_fuel' 1)

let head_normal = (fun env t -> (let t = (FStar_Absyn_Util.unmeta_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (FStar_Absyn_Syntax.Typ_const (v)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (v); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _119_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _119_460 FStar_Option.isNone))
end
| _53_510 -> begin
false
end)))

let whnf = (fun env t -> (match ((head_normal env t)) with
| true -> begin
t
end
| false -> begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end))

let whnf_e = (fun env e -> (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))

let norm_t = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env.tcenv t))

let norm_k = (fun env k -> (FStar_Tc_Normalize.normalize_kind env.tcenv k))

let trivial_post = (fun t -> (let _119_482 = (let _119_481 = (let _119_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_119_479)::[])
in (let _119_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_119_481, _119_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _119_482 None t.FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _119_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _119_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _119_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _119_490))
end
| _53_527 -> begin
(let _119_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _119_491))
end)) e)))

let mk_ApplyE_args = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyET out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))

let mk_ApplyT = (fun t vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _119_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _119_504))
end
| _53_542 -> begin
(let _119_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _119_505))
end)) t)))

let mk_ApplyT_args = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))

let is_app = (fun _53_8 -> (match (_53_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _53_561 -> begin
false
end))

let is_eta = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.FStar_ToSMT_Term.tm, xs)) with
| (FStar_ToSMT_Term.App (app, f::{FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _53_572; FStar_ToSMT_Term.freevars = _53_570}::[]), x::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _53_590) -> begin
(match ((((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _53_597 -> begin
false
end)) args vars))) with
| true -> begin
(tok_of_name env f)
end
| false -> begin
None
end)
end
| (_53_599, []) -> begin
(let fvs = (FStar_ToSMT_Term.free_variables t)
in (match ((FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars))))))) with
| true -> begin
Some (t)
end
| false -> begin
None
end))
end
| _53_605 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

type label =
(FStar_ToSMT_Term.fv * Prims.string * FStar_Range.range)

type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t); guard : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term; projections : FStar_ToSMT_Term.term  ->  (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.term) Prims.list}

let is_Mkpattern = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))

exception Let_rec_unencodeable

let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable -> begin
true
end
| _ -> begin
false
end))

let encode_const = (fun _53_9 -> (match (_53_9) with
| FStar_Absyn_Syntax.Const_unit -> begin
FStar_ToSMT_Term.mk_Term_unit
end
| FStar_Absyn_Syntax.Const_bool (true) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
end
| FStar_Absyn_Syntax.Const_bool (false) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkFalse)
end
| FStar_Absyn_Syntax.Const_char (c) -> begin
(let _119_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _119_561))
end
| FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _119_562 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_ToSMT_Term.boxInt _119_562))
end
| FStar_Absyn_Syntax.Const_int (i) -> begin
(let _119_563 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _119_563))
end
| FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _119_567 = (let _119_566 = (let _119_565 = (let _119_564 = (FStar_ToSMT_Term.mkInteger32 i)
in (FStar_ToSMT_Term.boxInt _119_564))
in (_119_565)::[])
in ("FStar.Int32.Int32", _119_566))
in (FStar_ToSMT_Term.mkApp _119_567))
end
| FStar_Absyn_Syntax.Const_string (bytes, _53_627) -> begin
(let _119_568 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _119_568))
end
| c -> begin
(let _119_570 = (let _119_569 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _119_569))
in (FStar_All.failwith _119_570))
end))

let as_function_typ = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_53_638) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_53_641) -> begin
(let _119_579 = (FStar_Absyn_Util.unrefine t)
in (aux true _119_579))
end
| _53_644 -> begin
(match (norm) with
| true -> begin
(let _119_580 = (whnf env t)
in (aux false _119_580))
end
| false -> begin
(let _119_583 = (let _119_582 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _119_581 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _119_582 _119_581)))
in (FStar_All.failwith _119_583))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun k env -> (match ((let _119_619 = (FStar_Absyn_Util.compress_kind k)
in _119_619.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_53_649, k0) -> begin
(let _53_653 = (match ((FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _119_621 = (FStar_Absyn_Print.kind_to_string k)
in (let _119_620 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _119_621 _119_620)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _53_657) -> begin
(let _119_623 = (let _119_622 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _119_622))
in (_119_623, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(let tsym = (let _119_624 = (varops.fresh "t")
in (_119_624, FStar_ToSMT_Term.Type_sort))
in (let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (let _53_672 = (encode_binders None bs env)
in (match (_53_672) with
| (vars, guards, env', decls, _53_671) -> begin
(let app = (mk_ApplyT t vars)
in (let _53_676 = (encode_knd kbody env' app)
in (match (_53_676) with
| (kbody, decls') -> begin
(let rec aux = (fun app vars guards -> (match ((vars, guards)) with
| ([], []) -> begin
kbody
end
| (x::vars, g::guards) -> begin
(let app = (mk_ApplyT app ((x)::[]))
in (let body = (aux app vars guards)
in (let body = (match (vars) with
| [] -> begin
body
end
| _53_695 -> begin
(let _119_633 = (let _119_632 = (let _119_631 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _119_631))
in (_119_632, body))
in (FStar_ToSMT_Term.mkAnd _119_633))
end)
in (let _119_635 = (let _119_634 = (FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _119_634))
in (FStar_ToSMT_Term.mkForall _119_635)))))
end
| _53_698 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _119_637 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _119_637 (FStar_List.filter (fun _53_703 -> (match (_53_703) with
| (x, _53_702) -> begin
(x <> (Prims.fst tsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _53_709) -> begin
(let _119_640 = (let _119_639 = (let _119_638 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _119_638))
in (FStar_ToSMT_Term.mkApp _119_639))
in (_119_640, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _119_641 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_119_641))
end
| false -> begin
None
end)
in (let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _119_643 = (let _119_642 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _119_642))
in (FStar_ToSMT_Term.mkApp _119_643))
in (let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _119_652 = (let _119_651 = (let _119_650 = (let _119_649 = (let _119_648 = (let _119_647 = (let _119_646 = (let _119_645 = (let _119_644 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _119_644))
in (_119_645, k_interp))
in (FStar_ToSMT_Term.mkAnd _119_646))
in (t_has_k, _119_647))
in (FStar_ToSMT_Term.mkIff _119_648))
in ((t_has_k)::[], (tsym)::cvars, _119_649))
in (FStar_ToSMT_Term.mkForall _119_650))
in (_119_651, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_119_652))
in (let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _53_721 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _53_724 -> begin
(let _119_654 = (let _119_653 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _119_653))
in (FStar_All.failwith _119_654))
end))
and encode_knd = (fun k env t -> (let _53_730 = (encode_knd_term k env)
in (match (_53_730) with
| (k, decls) -> begin
(let _119_658 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_119_658, decls))
end)))
and encode_binders = (fun fuel_opt bs env -> (let _53_734 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _119_662 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.fprint1 "Encoding binders %s\n" _119_662))
end
| false -> begin
()
end)
in (let _53_784 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_741 b -> (match (_53_741) with
| (vars, guards, env, decls, names) -> begin
(let _53_778 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_744}) -> begin
(let a = (unmangle a)
in (let _53_753 = (gen_typ_var env a)
in (match (_53_753) with
| (aasym, aa, env') -> begin
(let _53_754 = (match ((FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _119_666 = (FStar_Absyn_Print.strBvd a)
in (let _119_665 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _119_666 aasym _119_665)))
end
| false -> begin
()
end)
in (let _53_758 = (encode_knd k env aa)
in (match (_53_758) with
| (guard_a_k, decls') -> begin
((aasym, FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', FStar_Util.Inl (a))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _53_760}) -> begin
(let x = (unmangle x)
in (let _53_769 = (gen_term_var env x)
in (match (_53_769) with
| (xxsym, xx, env') -> begin
(let _53_772 = (let _119_667 = (norm_t env t)
in (encode_typ_pred fuel_opt _119_667 env xx))
in (match (_53_772) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', FStar_Util.Inr (x))
end))
end)))
end)
in (match (_53_778) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_53_784) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_typ_pred = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _53_792 = (encode_typ_term t env)
in (match (_53_792) with
| (t, decls) -> begin
(let _119_672 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_119_672, decls))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _53_800 = (encode_typ_term t env)
in (match (_53_800) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _119_677 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_119_677, decls))
end
| Some (f) -> begin
(let _119_678 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_119_678, decls))
end)
end))))
and encode_typ_term = (fun t env -> (let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _119_681 = (lookup_typ_var env a)
in (_119_681, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _119_682 = (lookup_free_tvar env fv)
in (_119_682, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
(match (((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _53_821 = (encode_binders None binders env)
in (match (_53_821) with
| (vars, guards, env', decls, _53_820) -> begin
(let fsym = (let _119_683 = (varops.fresh "f")
in (_119_683, FStar_ToSMT_Term.Term_sort))
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _53_827 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_53_827) with
| (pre_opt, res_t) -> begin
(let _53_830 = (encode_typ_pred None res_t env' app)
in (match (_53_830) with
| (res_pred, decls') -> begin
(let _53_839 = (match (pre_opt) with
| None -> begin
(let _119_684 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_684, decls))
end
| Some (pre) -> begin
(let _53_836 = (encode_formula pre env')
in (match (_53_836) with
| (guard, decls0) -> begin
(let _119_685 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_119_685, (FStar_List.append decls decls0)))
end))
end)
in (match (_53_839) with
| (guards, guard_decls) -> begin
(let t_interp = (let _119_687 = (let _119_686 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _119_686))
in (FStar_ToSMT_Term.mkForall _119_687))
in (let cvars = (let _119_689 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _119_689 (FStar_List.filter (fun _53_844 -> (match (_53_844) with
| (x, _53_843) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _53_850) -> begin
(let _119_692 = (let _119_691 = (let _119_690 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _119_690))
in (FStar_ToSMT_Term.mkApp _119_691))
in (_119_692, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _119_693 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_119_693))
end
| false -> begin
None
end)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _119_695 = (let _119_694 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _119_694))
in (FStar_ToSMT_Term.mkApp _119_695))
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _119_697 = (let _119_696 = (FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_119_696, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_119_697))
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _119_704 = (let _119_703 = (let _119_702 = (let _119_701 = (let _119_700 = (let _119_699 = (let _119_698 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _119_698))
in (f_has_t, _119_699))
in (FStar_ToSMT_Term.mkImp _119_700))
in ((f_has_t)::[], (fsym)::cvars, _119_701))
in (mkForall_fuel _119_702))
in (_119_703, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_119_704))
in (let t_interp = (let _119_708 = (let _119_707 = (let _119_706 = (let _119_705 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in ((f_has_t_z)::[], (fsym)::cvars, _119_705))
in (FStar_ToSMT_Term.mkForall _119_706))
in (_119_707, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_119_708))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _53_866 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end
| false -> begin
(let tsym = (varops.fresh "Non_total_Typ_fun")
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, [], FStar_ToSMT_Term.Type_sort, None))
in (let t = (FStar_ToSMT_Term.mkApp (tsym, []))
in (let t_kinding = (let _119_710 = (let _119_709 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_119_709, None))
in FStar_ToSMT_Term.Assume (_119_710))
in (let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _119_717 = (let _119_716 = (let _119_715 = (let _119_714 = (let _119_713 = (let _119_712 = (let _119_711 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _119_711))
in (f_has_t, _119_712))
in (FStar_ToSMT_Term.mkImp _119_713))
in ((f_has_t)::[], (fsym)::[], _119_714))
in (mkForall_fuel _119_715))
in (_119_716, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_119_717))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end)
end
| FStar_Absyn_Syntax.Typ_refine (_53_877) -> begin
(let _53_896 = (match ((FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _53_886; FStar_Absyn_Syntax.pos = _53_884; FStar_Absyn_Syntax.fvs = _53_882; FStar_Absyn_Syntax.uvs = _53_880} -> begin
(x, f)
end
| _53_893 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_896) with
| (x, f) -> begin
(let _53_899 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_53_899) with
| (base_t, decls) -> begin
(let _53_903 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_53_903) with
| (x, xtm, env') -> begin
(let _53_906 = (encode_formula f env')
in (match (_53_906) with
| (refinement, decls') -> begin
(let _53_909 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_909) with
| (fsym, fterm) -> begin
(let encoding = (let _119_719 = (let _119_718 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_119_718, refinement))
in (FStar_ToSMT_Term.mkAnd _119_719))
in (let cvars = (let _119_721 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _119_721 (FStar_List.filter (fun _53_914 -> (match (_53_914) with
| (y, _53_913) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_921, _53_923) -> begin
(let _119_724 = (let _119_723 = (let _119_722 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _119_722))
in (FStar_ToSMT_Term.mkApp _119_723))
in (_119_724, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _119_726 = (let _119_725 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _119_725))
in (FStar_ToSMT_Term.mkApp _119_726))
in (let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _119_728 = (let _119_727 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (ffv)::(xfv)::cvars, _119_727))
in (FStar_ToSMT_Term.mkForall _119_728))
in (let t_decls = (let _119_735 = (let _119_734 = (let _119_733 = (let _119_732 = (let _119_731 = (let _119_730 = (let _119_729 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_119_729))
in (assumption, _119_730))
in FStar_ToSMT_Term.Assume (_119_731))
in (_119_732)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_119_733)
in (tdecl)::_119_734)
in (FStar_List.append (FStar_List.append decls decls') _119_735))
in (let _53_936 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _119_736 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _119_736))
in (let _53_945 = (encode_knd k env ttm)
in (match (_53_945) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let is_full_app = (fun _53_952 -> (match (()) with
| () -> begin
(let kk = (FStar_Tc_Recheck.recompute_kind head)
in (let _53_957 = (FStar_Absyn_Util.kind_formals kk)
in (match (_53_957) with
| (formals, _53_956) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _53_964 = (encode_args args env)
in (match (_53_964) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _53_970 = (encode_args args env)
in (match (_53_970) with
| (args, decls) -> begin
(match ((is_full_app ())) with
| true -> begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _119_741 = (let _119_740 = (FStar_List.map (fun _53_10 -> (match (_53_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _119_740))
in (FStar_ToSMT_Term.mkApp _119_741))
in (t, decls)))
end
| false -> begin
(let head = (lookup_free_tvar env fv)
in (let t = (mk_ApplyT_args head args)
in (t, decls)))
end)
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _119_742 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _119_742))
in (let _53_986 = (encode_knd k env ttm)
in (match (_53_986) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _53_989 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(let _53_1001 = (encode_binders None bs env)
in (match (_53_1001) with
| (vars, guards, env, decls, _53_1000) -> begin
(let _53_1004 = (encode_typ_term body env)
in (match (_53_1004) with
| (body, decls') -> begin
(let key_body = (let _119_746 = (let _119_745 = (let _119_744 = (let _119_743 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_743, body))
in (FStar_ToSMT_Term.mkImp _119_744))
in ([], vars, _119_745))
in (FStar_ToSMT_Term.mkForall _119_746))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1010, _53_1012) -> begin
(let _119_749 = (let _119_748 = (let _119_747 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _119_747))
in (FStar_ToSMT_Term.mkApp _119_748))
in (_119_749, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
(head, [])
end
| None -> begin
(let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tsym = (varops.fresh "Typ_lam")
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _119_751 = (let _119_750 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _119_750))
in (FStar_ToSMT_Term.mkApp _119_751))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _119_758 = (let _119_757 = (let _119_756 = (let _119_755 = (let _119_754 = (let _119_753 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _119_752 = (FStar_ToSMT_Term.mkEq (app, body))
in (_119_753, _119_752)))
in (FStar_ToSMT_Term.mkImp _119_754))
in ((app)::[], (FStar_List.append vars cvars), _119_755))
in (FStar_ToSMT_Term.mkForall _119_756))
in (_119_757, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_119_758))
in (let kinding = (let _53_1027 = (let _119_759 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _119_759 env t))
in (match (_53_1027) with
| (ktm, decls'') -> begin
(let _119_763 = (let _119_762 = (let _119_761 = (let _119_760 = (FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_119_760, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_119_761))
in (_119_762)::[])
in (FStar_List.append decls'' _119_763))
end))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _53_1030 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _53_1034) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_53_1038) -> begin
(let _119_764 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _119_764 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _119_769 = (let _119_768 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _119_767 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _119_766 = (FStar_Absyn_Print.typ_to_string t0)
in (let _119_765 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _119_768 _119_767 _119_766 _119_765)))))
in (FStar_All.failwith _119_769))
end)))
and encode_exp = (fun e env -> (let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_53_1049) -> begin
(let _119_772 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _119_772 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _53_1056) -> begin
(let _119_773 = (lookup_free_var env v)
in (_119_773, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _119_774 = (encode_const c)
in (_119_774, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _53_1064) -> begin
(let _53_1067 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _53_1071)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _53_1077) -> begin
(let e = (let _119_775 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _119_775))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fallback = (fun _53_1086 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _119_778 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_119_778, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _53_1090 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _119_779 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _119_779))) with
| true -> begin
(fallback ())
end
| false -> begin
(let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let nformals = (FStar_List.length bs')
in (match (((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c))) with
| true -> begin
(let _53_1102 = (FStar_Util.first_N nformals bs)
in (match (_53_1102) with
| (bs0, rest) -> begin
(let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _53_1106 -> begin
(FStar_All.failwith "Impossible")
end)
in (let e = (let _119_781 = (let _119_780 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _119_780))
in (FStar_Absyn_Syntax.mk_Exp_abs _119_781 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end
| false -> begin
(let _53_1115 = (encode_binders None bs env)
in (match (_53_1115) with
| (vars, guards, envbody, decls, _53_1114) -> begin
(let _53_1118 = (encode_exp body envbody)
in (match (_53_1118) with
| (body, decls') -> begin
(let key_body = (let _119_785 = (let _119_784 = (let _119_783 = (let _119_782 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_782, body))
in (FStar_ToSMT_Term.mkImp _119_783))
in ([], vars, _119_784))
in (FStar_ToSMT_Term.mkForall _119_785))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1124, _53_1126) -> begin
(let _119_788 = (let _119_787 = (let _119_786 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _119_786))
in (FStar_ToSMT_Term.mkApp _119_787))
in (_119_788, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let fsym = (varops.fresh "Exp_abs")
in (let fdecl = FStar_ToSMT_Term.DeclFun ((fsym, cvar_sorts, FStar_ToSMT_Term.Term_sort, None))
in (let f = (let _119_790 = (let _119_789 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _119_789))
in (FStar_ToSMT_Term.mkApp _119_790))
in (let app = (mk_ApplyE f vars)
in (let _53_1140 = (encode_typ_pred None tfun env f)
in (match (_53_1140) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _119_792 = (let _119_791 = (FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_119_791, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_119_792))
in (let interp_f = (let _119_799 = (let _119_798 = (let _119_797 = (let _119_796 = (let _119_795 = (let _119_794 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _119_793 = (FStar_ToSMT_Term.mkEq (app, body))
in (_119_794, _119_793)))
in (FStar_ToSMT_Term.mkImp _119_795))
in ((app)::[], (FStar_List.append vars cvars), _119_796))
in (FStar_ToSMT_Term.mkForall _119_797))
in (_119_798, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_119_799))
in (let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _53_1144 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end))
end
| _53_1147 -> begin
(FStar_All.failwith "Impossible")
end))
end)
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _53_1158); FStar_Absyn_Syntax.tk = _53_1155; FStar_Absyn_Syntax.pos = _53_1153; FStar_Absyn_Syntax.fvs = _53_1151; FStar_Absyn_Syntax.uvs = _53_1149}, (FStar_Util.Inl (_53_1173), _53_1176)::(FStar_Util.Inr (v1), _53_1170)::(FStar_Util.Inr (v2), _53_1165)::[]) when (FStar_Absyn_Syntax.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(let _53_1183 = (encode_exp v1 env)
in (match (_53_1183) with
| (v1, decls1) -> begin
(let _53_1186 = (encode_exp v2 env)
in (match (_53_1186) with
| (v2, decls2) -> begin
(let _119_800 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_119_800, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_53_1196); FStar_Absyn_Syntax.tk = _53_1194; FStar_Absyn_Syntax.pos = _53_1192; FStar_Absyn_Syntax.fvs = _53_1190; FStar_Absyn_Syntax.uvs = _53_1188}, _53_1200) -> begin
(let _119_801 = (whnf_e env e)
in (encode_exp _119_801 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(let _53_1209 = (encode_args args_e env)
in (match (_53_1209) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _53_1214 = (encode_exp head env)
in (match (_53_1214) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(let _53_1223 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_53_1223) with
| (formals, rest) -> begin
(let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _119_804 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _119_804 (FStar_Absyn_Util.subst_typ subst)))
in (let _53_1228 = (encode_typ_pred None ty env app_tm)
in (match (_53_1228) with
| (has_type, decls'') -> begin
(let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _119_806 = (let _119_805 = (FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_119_805, None))
in FStar_ToSMT_Term.Assume (_119_806))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _53_1235 = (lookup_free_var_sym env fv)
in (match (_53_1235) with
| (fname, fuel_args) -> begin
(let tm = (let _119_812 = (let _119_811 = (let _119_810 = (FStar_List.map (fun _53_11 -> (match (_53_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _119_810))
in (fname, _119_811))
in (FStar_ToSMT_Term.mkApp' _119_812))
in (tm, decls))
end)))
in (let head = (FStar_Absyn_Util.compress_exp head)
in (let _53_1242 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186")))) with
| true -> begin
(let _119_814 = (FStar_Absyn_Print.exp_to_string head)
in (let _119_813 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _119_814 _119_813)))
end
| false -> begin
()
end)
in (let head_type = (let _119_817 = (let _119_816 = (let _119_815 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _119_815))
in (whnf env _119_816))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _119_817))
in (let _53_1245 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _119_820 = (FStar_Absyn_Print.exp_to_string head)
in (let _119_819 = (FStar_Absyn_Print.tag_of_exp head)
in (let _119_818 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _119_820 _119_819 _119_818))))
end
| false -> begin
()
end)
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _119_824 = (let _119_823 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _119_822 = (FStar_Absyn_Print.exp_to_string e0)
in (let _119_821 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _119_823 _119_822 _119_821))))
in (FStar_All.failwith _119_824))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _53_1254) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _53_1258 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some ((formals, c))))
end
| false -> begin
(encode_partial_app None)
end)
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_53_1267); FStar_Absyn_Syntax.lbtyp = _53_1265; FStar_Absyn_Syntax.lbeff = _53_1263; FStar_Absyn_Syntax.lbdef = _53_1261}::[]), _53_1273) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _53_1279; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _53_1291 = (encode_exp e1 env)
in (match (_53_1291) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _53_1295 = (encode_exp e2 env')
in (match (_53_1295) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_53_1297) -> begin
(let _53_1299 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = FStar_ToSMT_Term.DeclFun ((e, [], FStar_ToSMT_Term.Term_sort, None))
in (let _119_825 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_119_825, (decl_e)::[])))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _53_1309 = (encode_exp e env)
in (match (_53_1309) with
| (scr, decls) -> begin
(let _53_1349 = (FStar_List.fold_right (fun _53_1313 _53_1316 -> (match ((_53_1313, _53_1316)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _53_1320 _53_1323 -> (match ((_53_1320, _53_1323)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _53_1329 -> (match (_53_1329) with
| (x, t) -> begin
(match (x) with
| FStar_Util.Inl (a) -> begin
(push_typ_var env a.FStar_Absyn_Syntax.v t)
end
| FStar_Util.Inr (x) -> begin
(push_term_var env x.FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _53_1343 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _53_1340 = (encode_exp w env)
in (match (_53_1340) with
| (w, decls2) -> begin
(let _119_836 = (let _119_835 = (let _119_834 = (let _119_833 = (let _119_832 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _119_832))
in (FStar_ToSMT_Term.mkEq _119_833))
in (guard, _119_834))
in (FStar_ToSMT_Term.mkAnd _119_835))
in (_119_836, decls2))
end))
end)
in (match (_53_1343) with
| (guard, decls2) -> begin
(let _53_1346 = (encode_exp br env)
in (match (_53_1346) with
| (br, decls3) -> begin
(let _119_837 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_119_837, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_53_1349) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_53_1351) -> begin
(let _119_840 = (let _119_839 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _119_838 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _119_839 _119_838)))
in (FStar_All.failwith _119_840))
end))))
and encode_pat = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _53_1358 -> begin
(let _119_843 = (encode_one_pat env pat)
in (_119_843)::[])
end))
and encode_one_pat = (fun env pat -> (let _53_1361 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _119_846 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.fprint1 "Encoding pattern %s\n" _119_846))
end
| false -> begin
()
end)
in (let _53_1365 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_53_1365) with
| (vars, pat_exp_or_typ) -> begin
(let _53_1386 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _53_1368 v -> (match (_53_1368) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(let _53_1376 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_53_1376) with
| (aa, _53_1374, env) -> begin
(env, ((v, (aa, FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| FStar_Util.Inr (x) -> begin
(let _53_1383 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_53_1383) with
| (xx, _53_1381, env) -> begin
(env, ((v, (xx, FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_53_1386) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_1391) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _119_854 = (let _119_853 = (encode_const c)
in (scrutinee, _119_853))
in (FStar_ToSMT_Term.mkEq _119_854))
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1415, args) -> begin
(let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1424 -> (match (_53_1424) with
| (arg, _53_1423) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _119_857 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _119_857)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_1431) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((FStar_Util.Inr (x), scrutinee))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((FStar_Util.Inl (a), scrutinee))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_53_1448) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1452, args) -> begin
(let _119_865 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1460 -> (match (_53_1460) with
| (arg, _53_1459) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _119_864 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _119_864)))
end))))
in (FStar_All.pipe_right _119_865 FStar_List.flatten))
end))
in (let pat_term = (fun _53_1463 -> (match (()) with
| () -> begin
(match (pat_exp_or_typ) with
| FStar_Util.Inl (t) -> begin
(encode_typ_term t env)
end
| FStar_Util.Inr (e) -> begin
(encode_exp e env)
end)
end))
in (let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args = (fun l env -> (let _53_1493 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _53_1473 x -> (match (_53_1473) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _53_1478) -> begin
(let _53_1482 = (encode_typ_term t env)
in (match (_53_1482) with
| (t, decls') -> begin
((FStar_Util.Inl (t))::tms, (FStar_List.append decls decls'))
end))
end
| (FStar_Util.Inr (e), _53_1486) -> begin
(let _53_1490 = (encode_exp e env)
in (match (_53_1490) with
| (t, decls') -> begin
((FStar_Util.Inr (t))::tms, (FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_53_1493) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula = (fun phi env -> (let _53_1499 = (encode_formula_with_labels phi env)
in (match (_53_1499) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _53_1502 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun induction_on t env -> (let v_or_t_pat = (fun p -> (match ((let _119_879 = (FStar_Absyn_Util.unmeta_exp p)
in _119_879.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (_53_1509, (FStar_Util.Inl (_53_1516), _53_1519)::(FStar_Util.Inr (e), _53_1513)::[]) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app (_53_1525, (FStar_Util.Inl (t), _53_1529)::[]) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _53_1535 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun p -> (match ((let _119_882 = (FStar_Absyn_Util.unmeta_exp p)
in _119_882.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (_53_1539, _53_1551::(FStar_Util.Inr (hd), _53_1548)::(FStar_Util.Inr (tl), _53_1543)::[]) -> begin
(let _119_884 = (v_or_t_pat hd)
in (let _119_883 = (lemma_pats tl)
in (_119_884)::_119_883))
end
| _53_1556 -> begin
[]
end))
in (let _53_1595 = (match ((let _119_885 = (FStar_Absyn_Util.compress_typ t)
in _119_885.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _53_1565; FStar_Absyn_Syntax.pos = _53_1563; FStar_Absyn_Syntax.fvs = _53_1561; FStar_Absyn_Syntax.uvs = _53_1559}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _53_1584)::(FStar_Util.Inl (post), _53_1579)::(FStar_Util.Inr (pats), _53_1574)::[] -> begin
(let _119_886 = (lemma_pats pats)
in (binders, pre, post, _119_886))
end
| _53_1588 -> begin
(FStar_All.failwith "impos")
end)
end
| _53_1590 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_53_1595) with
| (binders, pre, post, patterns) -> begin
(let _53_1602 = (encode_binders None binders env)
in (match (_53_1602) with
| (vars, guards, env, decls, _53_1601) -> begin
(let _53_1618 = (let _119_888 = (FStar_All.pipe_right patterns (FStar_List.map (fun _53_12 -> (match (_53_12) with
| (FStar_Util.Inl (t), _53_1607) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _53_1612) -> begin
(encode_exp e (let _53_1614 = env
in {bindings = _53_1614.bindings; depth = _53_1614.depth; tcenv = _53_1614.tcenv; warn = _53_1614.warn; cache = _53_1614.cache; nolabels = _53_1614.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1614.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _119_888 FStar_List.unzip))
in (match (_53_1618) with
| (pats, decls') -> begin
(let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
(let _119_890 = (let _119_889 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _119_889 e))
in (_119_890)::pats)
end
| _53_1626 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(let _119_895 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_119_895)::pats)
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _119_897 = (let _119_896 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _119_896 tl))
in (aux _119_897 vars))
end
| _53_1637 -> begin
pats
end))
in (let _119_898 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _119_898 vars)))
end)
end)
in (let env = (let _53_1639 = env
in {bindings = _53_1639.bindings; depth = _53_1639.depth; tcenv = _53_1639.tcenv; warn = _53_1639.warn; cache = _53_1639.cache; nolabels = true; use_zfuel_name = _53_1639.use_zfuel_name; encode_non_total_function_typ = _53_1639.encode_non_total_function_typ})
in (let _53_1644 = (let _119_899 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _119_899 env))
in (match (_53_1644) with
| (pre, decls'') -> begin
(let _53_1647 = (let _119_900 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _119_900 env))
in (match (_53_1647) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _119_905 = (let _119_904 = (let _119_903 = (let _119_902 = (let _119_901 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_119_901, post))
in (FStar_ToSMT_Term.mkImp _119_902))
in (pats, vars, _119_903))
in (FStar_ToSMT_Term.mkForall _119_904))
in (_119_905, decls)))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun phi env -> (let enc = (fun f -> (fun l -> (let _53_1668 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(let _53_1660 = (encode_typ_term t env)
in (match (_53_1660) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(let _53_1665 = (encode_exp e env)
in (match (_53_1665) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_53_1668) with
| (decls, args) -> begin
(let _119_923 = (f args)
in (_119_923, [], decls))
end))))
in (let enc_prop_c = (fun f -> (fun l -> (let _53_1688 = (FStar_List.fold_right (fun t _53_1676 -> (match (_53_1676) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(let _53_1682 = (encode_formula_with_labels t env)
in (match (_53_1682) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _53_1684 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_53_1688) with
| (phis, labs, decls) -> begin
(let _119_939 = (f phis)
in (_119_939, labs, decls))
end))))
in (let const_op = (fun f _53_1691 -> (f, [], []))
in (let un_op = (fun f l -> (let _119_953 = (FStar_List.hd l)
in (FStar_All.pipe_left f _119_953)))
in (let bin_op = (fun f _53_13 -> (match (_53_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _53_1702 -> begin
(FStar_All.failwith "Impossible")
end))
in (let eq_op = (fun _53_14 -> (match (_53_14) with
| _53_1710::_53_1708::e1::e2::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _53_15 -> (match (_53_15) with
| (FStar_Util.Inl (lhs), _53_1723)::(FStar_Util.Inl (rhs), _53_1718)::[] -> begin
(let _53_1729 = (encode_formula_with_labels rhs env)
in (match (_53_1729) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_1732) -> begin
(l1, labs1, decls1)
end
| _53_1736 -> begin
(let _53_1740 = (encode_formula_with_labels lhs env)
in (match (_53_1740) with
| (l2, labs2, decls2) -> begin
(let _119_967 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_119_967, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _53_1742 -> begin
(FStar_All.failwith "impossible")
end))
in (let mk_ite = (fun _53_16 -> (match (_53_16) with
| (FStar_Util.Inl (guard), _53_1758)::(FStar_Util.Inl (_then), _53_1753)::(FStar_Util.Inl (_else), _53_1748)::[] -> begin
(let _53_1764 = (encode_formula_with_labels guard env)
in (match (_53_1764) with
| (g, labs1, decls1) -> begin
(let _53_1768 = (encode_formula_with_labels _then env)
in (match (_53_1768) with
| (t, labs2, decls2) -> begin
(let _53_1772 = (encode_formula_with_labels _else env)
in (match (_53_1772) with
| (e, labs3, decls3) -> begin
(let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _53_1775 -> begin
(FStar_All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _119_979 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _119_979)))
in (let connectives = (let _119_1040 = (let _119_988 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _119_988))
in (let _119_1039 = (let _119_1038 = (let _119_994 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _119_994))
in (let _119_1037 = (let _119_1036 = (let _119_1035 = (let _119_1003 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _119_1003))
in (let _119_1034 = (let _119_1033 = (let _119_1032 = (let _119_1012 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _119_1012))
in (let _119_1031 = (let _119_1030 = (let _119_1018 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _119_1018))
in (_119_1030)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_119_1032)::_119_1031))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_119_1033)
in (_119_1035)::_119_1034))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_119_1036)
in (_119_1038)::_119_1037))
in (_119_1040)::_119_1039))
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(let _53_1793 = (encode_formula_with_labels phi' env)
in (match (_53_1793) with
| (phi, labs, decls) -> begin
(match (env.nolabels) with
| true -> begin
(phi, [], decls)
end
| false -> begin
(let lvar = (let _119_1043 = (varops.fresh "label")
in (_119_1043, FStar_ToSMT_Term.Bool_sort))
in (let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end)
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1804; FStar_Absyn_Syntax.pos = _53_1802; FStar_Absyn_Syntax.fvs = _53_1800; FStar_Absyn_Syntax.uvs = _53_1798}, _53_1819::(FStar_Util.Inr (l), _53_1816)::(FStar_Util.Inl (phi), _53_1811)::[]) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
(match ((FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let _53_1825 = (encode_exp l env)
in (match (_53_1825) with
| (e, decls) -> begin
(let _53_1828 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_53_1828) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end
| false -> begin
(FStar_ToSMT_Term.mkTrue, [], [])
end)
end
| _53_1830 -> begin
(let _53_1833 = (encode_typ_term phi env)
in (match (_53_1833) with
| (tt, decls) -> begin
(let _119_1044 = (FStar_ToSMT_Term.mk_Valid tt)
in (_119_1044, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _53_1845 = (encode_binders None bs env)
in (match (_53_1845) with
| (vars, guards, env, decls, _53_1844) -> begin
(let _53_1861 = (let _119_1054 = (FStar_All.pipe_right ps (FStar_List.map (fun _53_17 -> (match (_53_17) with
| (FStar_Util.Inl (t), _53_1850) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _53_1855) -> begin
(encode_exp e (let _53_1857 = env
in {bindings = _53_1857.bindings; depth = _53_1857.depth; tcenv = _53_1857.tcenv; warn = _53_1857.warn; cache = _53_1857.cache; nolabels = _53_1857.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1857.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _119_1054 FStar_List.unzip))
in (match (_53_1861) with
| (pats, decls') -> begin
(let _53_1865 = (encode_formula_with_labels body env)
in (match (_53_1865) with
| (body, labs, decls'') -> begin
(let _119_1055 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _119_1055, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _53_1866 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _119_1056 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.fprint1 ">>>> Destructing as formula ... %s\n" _119_1056))
end
| false -> begin
()
end)
in (let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _53_1878 -> (match (_53_1878) with
| (l, _53_1877) -> begin
(FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_53_1881, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(let _53_1891 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _119_1073 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.fprint1 ">>>> Got QALL [%s]\n" _119_1073))
end
| false -> begin
()
end)
in (let _53_1899 = (encode_q_body env vars pats body)
in (match (_53_1899) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _119_1076 = (let _119_1075 = (let _119_1074 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _119_1074))
in (FStar_ToSMT_Term.mkForall _119_1075))
in (_119_1076, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(let _53_1912 = (encode_q_body env vars pats body)
in (match (_53_1912) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _119_1079 = (let _119_1078 = (let _119_1077 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _119_1077))
in (FStar_ToSMT_Term.mkExists _119_1078))
in (_119_1079, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : FStar_Absyn_Syntax.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Absyn_Syntax.lident  ->  Prims.bool}

let is_Mkprims_t = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))

let prims = (let _53_1918 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_53_1918) with
| (asym, a) -> begin
(let _53_1921 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_1921) with
| (xsym, x) -> begin
(let _53_1924 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_53_1924) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (FStar_ToSMT_Term.DefineFun ((x, vars, FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body -> (fun x -> (let t1 = (let _119_1122 = (let _119_1121 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _119_1121))
in (FStar_ToSMT_Term.mkApp _119_1122))
in (let vname_decl = (let _119_1124 = (let _119_1123 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _119_1123, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_119_1124))
in (let _119_1130 = (let _119_1129 = (let _119_1128 = (let _119_1127 = (let _119_1126 = (let _119_1125 = (FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _119_1125))
in (FStar_ToSMT_Term.mkForall _119_1126))
in (_119_1127, None))
in FStar_ToSMT_Term.Assume (_119_1128))
in (_119_1129)::[])
in (vname_decl)::_119_1130)))))
in (let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _119_1290 = (let _119_1139 = (let _119_1138 = (let _119_1137 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1137))
in (quant axy _119_1138))
in (FStar_Absyn_Const.op_Eq, _119_1139))
in (let _119_1289 = (let _119_1288 = (let _119_1146 = (let _119_1145 = (let _119_1144 = (let _119_1143 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _119_1143))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1144))
in (quant axy _119_1145))
in (FStar_Absyn_Const.op_notEq, _119_1146))
in (let _119_1287 = (let _119_1286 = (let _119_1155 = (let _119_1154 = (let _119_1153 = (let _119_1152 = (let _119_1151 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1150 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1151, _119_1150)))
in (FStar_ToSMT_Term.mkLT _119_1152))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1153))
in (quant xy _119_1154))
in (FStar_Absyn_Const.op_LT, _119_1155))
in (let _119_1285 = (let _119_1284 = (let _119_1164 = (let _119_1163 = (let _119_1162 = (let _119_1161 = (let _119_1160 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1159 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1160, _119_1159)))
in (FStar_ToSMT_Term.mkLTE _119_1161))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1162))
in (quant xy _119_1163))
in (FStar_Absyn_Const.op_LTE, _119_1164))
in (let _119_1283 = (let _119_1282 = (let _119_1173 = (let _119_1172 = (let _119_1171 = (let _119_1170 = (let _119_1169 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1168 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1169, _119_1168)))
in (FStar_ToSMT_Term.mkGT _119_1170))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1171))
in (quant xy _119_1172))
in (FStar_Absyn_Const.op_GT, _119_1173))
in (let _119_1281 = (let _119_1280 = (let _119_1182 = (let _119_1181 = (let _119_1180 = (let _119_1179 = (let _119_1178 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1177 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1178, _119_1177)))
in (FStar_ToSMT_Term.mkGTE _119_1179))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1180))
in (quant xy _119_1181))
in (FStar_Absyn_Const.op_GTE, _119_1182))
in (let _119_1279 = (let _119_1278 = (let _119_1191 = (let _119_1190 = (let _119_1189 = (let _119_1188 = (let _119_1187 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1186 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1187, _119_1186)))
in (FStar_ToSMT_Term.mkSub _119_1188))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1189))
in (quant xy _119_1190))
in (FStar_Absyn_Const.op_Subtraction, _119_1191))
in (let _119_1277 = (let _119_1276 = (let _119_1198 = (let _119_1197 = (let _119_1196 = (let _119_1195 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _119_1195))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1196))
in (quant qx _119_1197))
in (FStar_Absyn_Const.op_Minus, _119_1198))
in (let _119_1275 = (let _119_1274 = (let _119_1207 = (let _119_1206 = (let _119_1205 = (let _119_1204 = (let _119_1203 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1202 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1203, _119_1202)))
in (FStar_ToSMT_Term.mkAdd _119_1204))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1205))
in (quant xy _119_1206))
in (FStar_Absyn_Const.op_Addition, _119_1207))
in (let _119_1273 = (let _119_1272 = (let _119_1216 = (let _119_1215 = (let _119_1214 = (let _119_1213 = (let _119_1212 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1211 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1212, _119_1211)))
in (FStar_ToSMT_Term.mkMul _119_1213))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1214))
in (quant xy _119_1215))
in (FStar_Absyn_Const.op_Multiply, _119_1216))
in (let _119_1271 = (let _119_1270 = (let _119_1225 = (let _119_1224 = (let _119_1223 = (let _119_1222 = (let _119_1221 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1220 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1221, _119_1220)))
in (FStar_ToSMT_Term.mkDiv _119_1222))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1223))
in (quant xy _119_1224))
in (FStar_Absyn_Const.op_Division, _119_1225))
in (let _119_1269 = (let _119_1268 = (let _119_1234 = (let _119_1233 = (let _119_1232 = (let _119_1231 = (let _119_1230 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1229 = (FStar_ToSMT_Term.unboxInt y)
in (_119_1230, _119_1229)))
in (FStar_ToSMT_Term.mkMod _119_1231))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _119_1232))
in (quant xy _119_1233))
in (FStar_Absyn_Const.op_Modulus, _119_1234))
in (let _119_1267 = (let _119_1266 = (let _119_1243 = (let _119_1242 = (let _119_1241 = (let _119_1240 = (let _119_1239 = (FStar_ToSMT_Term.unboxBool x)
in (let _119_1238 = (FStar_ToSMT_Term.unboxBool y)
in (_119_1239, _119_1238)))
in (FStar_ToSMT_Term.mkAnd _119_1240))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1241))
in (quant xy _119_1242))
in (FStar_Absyn_Const.op_And, _119_1243))
in (let _119_1265 = (let _119_1264 = (let _119_1252 = (let _119_1251 = (let _119_1250 = (let _119_1249 = (let _119_1248 = (FStar_ToSMT_Term.unboxBool x)
in (let _119_1247 = (FStar_ToSMT_Term.unboxBool y)
in (_119_1248, _119_1247)))
in (FStar_ToSMT_Term.mkOr _119_1249))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1250))
in (quant xy _119_1251))
in (FStar_Absyn_Const.op_Or, _119_1252))
in (let _119_1263 = (let _119_1262 = (let _119_1259 = (let _119_1258 = (let _119_1257 = (let _119_1256 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _119_1256))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_1257))
in (quant qx _119_1258))
in (FStar_Absyn_Const.op_Negation, _119_1259))
in (_119_1262)::[])
in (_119_1264)::_119_1263))
in (_119_1266)::_119_1265))
in (_119_1268)::_119_1267))
in (_119_1270)::_119_1269))
in (_119_1272)::_119_1271))
in (_119_1274)::_119_1273))
in (_119_1276)::_119_1275))
in (_119_1278)::_119_1277))
in (_119_1280)::_119_1279))
in (_119_1282)::_119_1281))
in (_119_1284)::_119_1283))
in (_119_1286)::_119_1285))
in (_119_1288)::_119_1287))
in (_119_1290)::_119_1289))
in (let mk = (fun l v -> (let _119_1322 = (FStar_All.pipe_right prims (FStar_List.filter (fun _53_1944 -> (match (_53_1944) with
| (l', _53_1943) -> begin
(FStar_Absyn_Syntax.lid_equals l l')
end))))
in (FStar_All.pipe_right _119_1322 (FStar_List.collect (fun _53_1948 -> (match (_53_1948) with
| (_53_1946, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _53_1954 -> (match (_53_1954) with
| (l', _53_1953) -> begin
(FStar_Absyn_Syntax.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

let primitive_type_axioms = (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let mk_unit = (fun _53_1960 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _119_1354 = (let _119_1345 = (let _119_1344 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_119_1344, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_119_1345))
in (let _119_1353 = (let _119_1352 = (let _119_1351 = (let _119_1350 = (let _119_1349 = (let _119_1348 = (let _119_1347 = (let _119_1346 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _119_1346))
in (FStar_ToSMT_Term.mkImp _119_1347))
in ((typing_pred)::[], (xx)::[], _119_1348))
in (mkForall_fuel _119_1349))
in (_119_1350, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_119_1351))
in (_119_1352)::[])
in (_119_1354)::_119_1353))))
in (let mk_bool = (fun _53_1965 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _119_1374 = (let _119_1364 = (let _119_1363 = (let _119_1362 = (let _119_1361 = (let _119_1360 = (let _119_1359 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _119_1359))
in (FStar_ToSMT_Term.mkImp _119_1360))
in ((typing_pred)::[], (xx)::[], _119_1361))
in (mkForall_fuel _119_1362))
in (_119_1363, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_119_1364))
in (let _119_1373 = (let _119_1372 = (let _119_1371 = (let _119_1370 = (let _119_1369 = (let _119_1368 = (let _119_1365 = (FStar_ToSMT_Term.boxBool b)
in (_119_1365)::[])
in (let _119_1367 = (let _119_1366 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _119_1366 tt))
in (_119_1368, (bb)::[], _119_1367)))
in (FStar_ToSMT_Term.mkForall _119_1369))
in (_119_1370, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_119_1371))
in (_119_1372)::[])
in (_119_1374)::_119_1373))))))
in (let mk_int = (fun _53_1972 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _119_1386 = (let _119_1385 = (let _119_1384 = (let _119_1383 = (let _119_1382 = (let _119_1381 = (FStar_ToSMT_Term.boxInt a)
in (let _119_1380 = (let _119_1379 = (FStar_ToSMT_Term.boxInt b)
in (_119_1379)::[])
in (_119_1381)::_119_1380))
in (tt)::_119_1382)
in (tt)::_119_1383)
in ("Prims.Precedes", _119_1384))
in (FStar_ToSMT_Term.mkApp _119_1385))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _119_1386))
in (let precedes_y_x = (let _119_1387 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _119_1387))
in (let _119_1428 = (let _119_1393 = (let _119_1392 = (let _119_1391 = (let _119_1390 = (let _119_1389 = (let _119_1388 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _119_1388))
in (FStar_ToSMT_Term.mkImp _119_1389))
in ((typing_pred)::[], (xx)::[], _119_1390))
in (mkForall_fuel _119_1391))
in (_119_1392, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_119_1393))
in (let _119_1427 = (let _119_1426 = (let _119_1400 = (let _119_1399 = (let _119_1398 = (let _119_1397 = (let _119_1394 = (FStar_ToSMT_Term.boxInt b)
in (_119_1394)::[])
in (let _119_1396 = (let _119_1395 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _119_1395 tt))
in (_119_1397, (bb)::[], _119_1396)))
in (FStar_ToSMT_Term.mkForall _119_1398))
in (_119_1399, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_119_1400))
in (let _119_1425 = (let _119_1424 = (let _119_1423 = (let _119_1422 = (let _119_1421 = (let _119_1420 = (let _119_1419 = (let _119_1418 = (let _119_1417 = (let _119_1416 = (let _119_1415 = (let _119_1414 = (let _119_1403 = (let _119_1402 = (FStar_ToSMT_Term.unboxInt x)
in (let _119_1401 = (FStar_ToSMT_Term.mkInteger' 0)
in (_119_1402, _119_1401)))
in (FStar_ToSMT_Term.mkGT _119_1403))
in (let _119_1413 = (let _119_1412 = (let _119_1406 = (let _119_1405 = (FStar_ToSMT_Term.unboxInt y)
in (let _119_1404 = (FStar_ToSMT_Term.mkInteger' 0)
in (_119_1405, _119_1404)))
in (FStar_ToSMT_Term.mkGTE _119_1406))
in (let _119_1411 = (let _119_1410 = (let _119_1409 = (let _119_1408 = (FStar_ToSMT_Term.unboxInt y)
in (let _119_1407 = (FStar_ToSMT_Term.unboxInt x)
in (_119_1408, _119_1407)))
in (FStar_ToSMT_Term.mkLT _119_1409))
in (_119_1410)::[])
in (_119_1412)::_119_1411))
in (_119_1414)::_119_1413))
in (typing_pred_y)::_119_1415)
in (typing_pred)::_119_1416)
in (FStar_ToSMT_Term.mk_and_l _119_1417))
in (_119_1418, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _119_1419))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _119_1420))
in (mkForall_fuel _119_1421))
in (_119_1422, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_119_1423))
in (_119_1424)::[])
in (_119_1426)::_119_1425))
in (_119_1428)::_119_1427)))))))))))
in (let mk_int_alias = (fun _53_1984 tt -> (let _119_1437 = (let _119_1436 = (let _119_1435 = (let _119_1434 = (let _119_1433 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Absyn_Syntax.str, []))
in (tt, _119_1433))
in (FStar_ToSMT_Term.mkEq _119_1434))
in (_119_1435, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_119_1436))
in (_119_1437)::[]))
in (let mk_str = (fun _53_1988 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.String_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _119_1457 = (let _119_1447 = (let _119_1446 = (let _119_1445 = (let _119_1444 = (let _119_1443 = (let _119_1442 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _119_1442))
in (FStar_ToSMT_Term.mkImp _119_1443))
in ((typing_pred)::[], (xx)::[], _119_1444))
in (mkForall_fuel _119_1445))
in (_119_1446, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_119_1447))
in (let _119_1456 = (let _119_1455 = (let _119_1454 = (let _119_1453 = (let _119_1452 = (let _119_1451 = (let _119_1448 = (FStar_ToSMT_Term.boxString b)
in (_119_1448)::[])
in (let _119_1450 = (let _119_1449 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _119_1449 tt))
in (_119_1451, (bb)::[], _119_1450)))
in (FStar_ToSMT_Term.mkForall _119_1452))
in (_119_1453, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_119_1454))
in (_119_1455)::[])
in (_119_1457)::_119_1456))))))
in (let mk_ref = (fun reft_name _53_1996 -> (let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let refa = (let _119_1464 = (let _119_1463 = (let _119_1462 = (FStar_ToSMT_Term.mkFreeV aa)
in (_119_1462)::[])
in (reft_name, _119_1463))
in (FStar_ToSMT_Term.mkApp _119_1464))
in (let refb = (let _119_1467 = (let _119_1466 = (let _119_1465 = (FStar_ToSMT_Term.mkFreeV bb)
in (_119_1465)::[])
in (reft_name, _119_1466))
in (FStar_ToSMT_Term.mkApp _119_1467))
in (let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _119_1486 = (let _119_1473 = (let _119_1472 = (let _119_1471 = (let _119_1470 = (let _119_1469 = (let _119_1468 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _119_1468))
in (FStar_ToSMT_Term.mkImp _119_1469))
in ((typing_pred)::[], (xx)::(aa)::[], _119_1470))
in (mkForall_fuel _119_1471))
in (_119_1472, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_119_1473))
in (let _119_1485 = (let _119_1484 = (let _119_1483 = (let _119_1482 = (let _119_1481 = (let _119_1480 = (let _119_1479 = (let _119_1478 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _119_1477 = (let _119_1476 = (let _119_1475 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _119_1474 = (FStar_ToSMT_Term.mkFreeV bb)
in (_119_1475, _119_1474)))
in (FStar_ToSMT_Term.mkEq _119_1476))
in (_119_1478, _119_1477)))
in (FStar_ToSMT_Term.mkImp _119_1479))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _119_1480))
in (mkForall_fuel' 2 _119_1481))
in (_119_1482, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_119_1483))
in (_119_1484)::[])
in (_119_1486)::_119_1485))))))))))
in (let mk_false_interp = (fun _53_2006 false_tm -> (let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _119_1493 = (let _119_1492 = (let _119_1491 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_119_1491, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_119_1492))
in (_119_1493)::[])))
in (let mk_and_interp = (fun conj _53_2012 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1500 = (let _119_1499 = (let _119_1498 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_119_1498)::[])
in ("Valid", _119_1499))
in (FStar_ToSMT_Term.mkApp _119_1500))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _119_1507 = (let _119_1506 = (let _119_1505 = (let _119_1504 = (let _119_1503 = (let _119_1502 = (let _119_1501 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_119_1501, valid))
in (FStar_ToSMT_Term.mkIff _119_1502))
in ((valid)::[], (aa)::(bb)::[], _119_1503))
in (FStar_ToSMT_Term.mkForall _119_1504))
in (_119_1505, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_119_1506))
in (_119_1507)::[])))))))))
in (let mk_or_interp = (fun disj _53_2023 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1514 = (let _119_1513 = (let _119_1512 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_119_1512)::[])
in ("Valid", _119_1513))
in (FStar_ToSMT_Term.mkApp _119_1514))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _119_1521 = (let _119_1520 = (let _119_1519 = (let _119_1518 = (let _119_1517 = (let _119_1516 = (let _119_1515 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_119_1515, valid))
in (FStar_ToSMT_Term.mkIff _119_1516))
in ((valid)::[], (aa)::(bb)::[], _119_1517))
in (FStar_ToSMT_Term.mkForall _119_1518))
in (_119_1519, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_119_1520))
in (_119_1521)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _119_1528 = (let _119_1527 = (let _119_1526 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_119_1526)::[])
in ("Valid", _119_1527))
in (FStar_ToSMT_Term.mkApp _119_1528))
in (let _119_1535 = (let _119_1534 = (let _119_1533 = (let _119_1532 = (let _119_1531 = (let _119_1530 = (let _119_1529 = (FStar_ToSMT_Term.mkEq (x, y))
in (_119_1529, valid))
in (FStar_ToSMT_Term.mkIff _119_1530))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _119_1531))
in (FStar_ToSMT_Term.mkForall _119_1532))
in (_119_1533, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_119_1534))
in (_119_1535)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1542 = (let _119_1541 = (let _119_1540 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_119_1540)::[])
in ("Valid", _119_1541))
in (FStar_ToSMT_Term.mkApp _119_1542))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _119_1549 = (let _119_1548 = (let _119_1547 = (let _119_1546 = (let _119_1545 = (let _119_1544 = (let _119_1543 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_119_1543, valid))
in (FStar_ToSMT_Term.mkIff _119_1544))
in ((valid)::[], (aa)::(bb)::[], _119_1545))
in (FStar_ToSMT_Term.mkForall _119_1546))
in (_119_1547, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_119_1548))
in (_119_1549)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1556 = (let _119_1555 = (let _119_1554 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_119_1554)::[])
in ("Valid", _119_1555))
in (FStar_ToSMT_Term.mkApp _119_1556))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _119_1563 = (let _119_1562 = (let _119_1561 = (let _119_1560 = (let _119_1559 = (let _119_1558 = (let _119_1557 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_119_1557, valid))
in (FStar_ToSMT_Term.mkIff _119_1558))
in ((valid)::[], (aa)::(bb)::[], _119_1559))
in (FStar_ToSMT_Term.mkForall _119_1560))
in (_119_1561, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_119_1562))
in (_119_1563)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _119_1570 = (let _119_1569 = (let _119_1568 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_119_1568)::[])
in ("Valid", _119_1569))
in (FStar_ToSMT_Term.mkApp _119_1570))
in (let valid_b_x = (let _119_1573 = (let _119_1572 = (let _119_1571 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_119_1571)::[])
in ("Valid", _119_1572))
in (FStar_ToSMT_Term.mkApp _119_1573))
in (let _119_1586 = (let _119_1585 = (let _119_1584 = (let _119_1583 = (let _119_1582 = (let _119_1581 = (let _119_1580 = (let _119_1579 = (let _119_1578 = (let _119_1574 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_119_1574)::[])
in (let _119_1577 = (let _119_1576 = (let _119_1575 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_119_1575, valid_b_x))
in (FStar_ToSMT_Term.mkImp _119_1576))
in (_119_1578, (xx)::[], _119_1577)))
in (FStar_ToSMT_Term.mkForall _119_1579))
in (_119_1580, valid))
in (FStar_ToSMT_Term.mkIff _119_1581))
in ((valid)::[], (aa)::(bb)::[], _119_1582))
in (FStar_ToSMT_Term.mkForall _119_1583))
in (_119_1584, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_119_1585))
in (_119_1586)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _119_1593 = (let _119_1592 = (let _119_1591 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_119_1591)::[])
in ("Valid", _119_1592))
in (FStar_ToSMT_Term.mkApp _119_1593))
in (let valid_b_x = (let _119_1596 = (let _119_1595 = (let _119_1594 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_119_1594)::[])
in ("Valid", _119_1595))
in (FStar_ToSMT_Term.mkApp _119_1596))
in (let _119_1609 = (let _119_1608 = (let _119_1607 = (let _119_1606 = (let _119_1605 = (let _119_1604 = (let _119_1603 = (let _119_1602 = (let _119_1601 = (let _119_1597 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_119_1597)::[])
in (let _119_1600 = (let _119_1599 = (let _119_1598 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_119_1598, valid_b_x))
in (FStar_ToSMT_Term.mkImp _119_1599))
in (_119_1601, (xx)::[], _119_1600)))
in (FStar_ToSMT_Term.mkExists _119_1602))
in (_119_1603, valid))
in (FStar_ToSMT_Term.mkIff _119_1604))
in ((valid)::[], (aa)::(bb)::[], _119_1605))
in (FStar_ToSMT_Term.mkForall _119_1606))
in (_119_1607, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_119_1608))
in (_119_1609)::[]))))))))))
in (let mk_foralltyp_interp = (fun for_all tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1616 = (let _119_1615 = (let _119_1614 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_119_1614)::[])
in ("Valid", _119_1615))
in (FStar_ToSMT_Term.mkApp _119_1616))
in (let valid_a_b = (let _119_1619 = (let _119_1618 = (let _119_1617 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_119_1617)::[])
in ("Valid", _119_1618))
in (FStar_ToSMT_Term.mkApp _119_1619))
in (let _119_1632 = (let _119_1631 = (let _119_1630 = (let _119_1629 = (let _119_1628 = (let _119_1627 = (let _119_1626 = (let _119_1625 = (let _119_1624 = (let _119_1620 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_119_1620)::[])
in (let _119_1623 = (let _119_1622 = (let _119_1621 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_119_1621, valid_a_b))
in (FStar_ToSMT_Term.mkImp _119_1622))
in (_119_1624, (bb)::[], _119_1623)))
in (FStar_ToSMT_Term.mkForall _119_1625))
in (_119_1626, valid))
in (FStar_ToSMT_Term.mkIff _119_1627))
in ((valid)::[], (kk)::(aa)::[], _119_1628))
in (FStar_ToSMT_Term.mkForall _119_1629))
in (_119_1630, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_119_1631))
in (_119_1632)::[]))))))))))
in (let mk_existstyp_interp = (fun for_some tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _119_1639 = (let _119_1638 = (let _119_1637 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_119_1637)::[])
in ("Valid", _119_1638))
in (FStar_ToSMT_Term.mkApp _119_1639))
in (let valid_a_b = (let _119_1642 = (let _119_1641 = (let _119_1640 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_119_1640)::[])
in ("Valid", _119_1641))
in (FStar_ToSMT_Term.mkApp _119_1642))
in (let _119_1655 = (let _119_1654 = (let _119_1653 = (let _119_1652 = (let _119_1651 = (let _119_1650 = (let _119_1649 = (let _119_1648 = (let _119_1647 = (let _119_1643 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_119_1643)::[])
in (let _119_1646 = (let _119_1645 = (let _119_1644 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_119_1644, valid_a_b))
in (FStar_ToSMT_Term.mkImp _119_1645))
in (_119_1647, (bb)::[], _119_1646)))
in (FStar_ToSMT_Term.mkExists _119_1648))
in (_119_1649, valid))
in (FStar_ToSMT_Term.mkIff _119_1650))
in ((valid)::[], (kk)::(aa)::[], _119_1651))
in (FStar_ToSMT_Term.mkForall _119_1652))
in (_119_1653, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_119_1654))
in (_119_1655)::[]))))))))))
in (let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.char_lid, mk_int_alias))::((FStar_Absyn_Const.uint8_lid, mk_int_alias))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _53_2116 -> (match (_53_2116) with
| (l, _53_2115) -> begin
(FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_53_2119, f) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun env se -> (let _53_2125 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _119_1798 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.fprint1 ">>>>Encoding [%s]\n") _119_1798))
end
| false -> begin
()
end)
in (let nm = (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Absyn_Syntax.str
end)
in (let _53_2133 = (encode_sigelt' env se)
in (match (_53_2133) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _119_1801 = (let _119_1800 = (let _119_1799 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_119_1799))
in (_119_1800)::[])
in (_119_1801, e))
end
| _53_2136 -> begin
(let _119_1808 = (let _119_1807 = (let _119_1803 = (let _119_1802 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_119_1802))
in (_119_1803)::g)
in (let _119_1806 = (let _119_1805 = (let _119_1804 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_119_1804))
in (_119_1805)::[])
in (FStar_List.append _119_1807 _119_1806)))
in (_119_1808, e))
end)
end)))))
and encode_sigelt' = (fun env se -> (let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.all_")))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_53_2142, _53_2144, _53_2146, _53_2148, FStar_Absyn_Syntax.Effect::[], _53_2152) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2157, _53_2159, _53_2161, _53_2163, _53_2165) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2170, _53_2172, _53_2174, _53_2176, _53_2178) when (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(let _53_2184 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2184) with
| (tname, ttok, env) -> begin
(let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _119_1813 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (FStar_ToSMT_Term.mk_Valid _119_1813))
in (let decls = (let _119_1821 = (let _119_1820 = (let _119_1819 = (let _119_1818 = (let _119_1817 = (let _119_1816 = (let _119_1815 = (let _119_1814 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _119_1814))
in (FStar_ToSMT_Term.mkEq _119_1815))
in ((valid_b2t_x)::[], (xx)::[], _119_1816))
in (FStar_ToSMT_Term.mkForall _119_1817))
in (_119_1818, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_119_1819))
in (_119_1820)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_119_1821)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _53_2192, t, tags, _53_2196) -> begin
(let _53_2202 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2202) with
| (tname, ttok, env) -> begin
(let _53_2211 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _53_2208 -> begin
(tps, t)
end)
in (match (_53_2211) with
| (tps, t) -> begin
(let _53_2218 = (encode_binders None tps env)
in (match (_53_2218) with
| (vars, guards, env', binder_decls, _53_2217) -> begin
(let tok_app = (let _119_1822 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _119_1822 vars))
in (let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _119_1824 = (let _119_1823 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _119_1823))
in (FStar_ToSMT_Term.mkApp _119_1824))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _53_2224 -> begin
(let _119_1826 = (let _119_1825 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _119_1825))
in (_119_1826)::[])
end)
in (let decls = (let _119_1837 = (let _119_1830 = (let _119_1829 = (let _119_1828 = (let _119_1827 = (FStar_List.map Prims.snd vars)
in (tname, _119_1827, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_119_1828))
in (_119_1829)::(tok_decl)::[])
in (FStar_List.append _119_1830 fresh_tok))
in (let _119_1836 = (let _119_1835 = (let _119_1834 = (let _119_1833 = (let _119_1832 = (let _119_1831 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _119_1831))
in (FStar_ToSMT_Term.mkForall _119_1832))
in (_119_1833, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_119_1834))
in (_119_1835)::[])
in (FStar_List.append _119_1837 _119_1836)))
in (let t = (whnf env t)
in (let _53_2236 = (match ((FStar_All.pipe_right tags (FStar_Util.for_some (fun _53_18 -> (match (_53_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _53_2231 -> begin
false
end))))) with
| true -> begin
(let _119_1840 = (FStar_ToSMT_Term.mk_Valid app)
in (let _119_1839 = (encode_formula t env')
in (_119_1840, _119_1839)))
end
| false -> begin
(let _119_1841 = (encode_typ_term t env')
in (app, _119_1841))
end)
in (match (_53_2236) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _119_1848 = (let _119_1847 = (let _119_1846 = (let _119_1845 = (let _119_1844 = (let _119_1843 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _119_1842 = (FStar_ToSMT_Term.mkEq (def, body))
in (_119_1843, _119_1842)))
in (FStar_ToSMT_Term.mkImp _119_1844))
in ((def)::[], vars, _119_1845))
in (FStar_ToSMT_Term.mkForall _119_1846))
in (_119_1847, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_119_1848))
in (let kindingAx = (let _53_2240 = (let _119_1849 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _119_1849 env' app))
in (match (_53_2240) with
| (k, decls) -> begin
(let _119_1857 = (let _119_1856 = (let _119_1855 = (let _119_1854 = (let _119_1853 = (let _119_1852 = (let _119_1851 = (let _119_1850 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_1850, k))
in (FStar_ToSMT_Term.mkImp _119_1851))
in ((app)::[], vars, _119_1852))
in (FStar_ToSMT_Term.mkForall _119_1853))
in (_119_1854, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_119_1855))
in (_119_1856)::[])
in (FStar_List.append decls _119_1857))
end))
in (let g = (let _119_1858 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _119_1858))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _53_2247) -> begin
(let tt = (whnf env t)
in (let _53_2253 = (encode_free_var env lid t tt quals)
in (match (_53_2253) with
| (decls, env) -> begin
(match (((FStar_Absyn_Util.is_smt_lemma t) && ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface))) with
| true -> begin
(let _119_1860 = (let _119_1859 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _119_1859))
in (_119_1860, env))
end
| false -> begin
(decls, env)
end)
end)))
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _53_2257, _53_2259) -> begin
(let _53_2264 = (encode_formula f env)
in (match (_53_2264) with
| (f, decls) -> begin
(let g = (let _119_1865 = (let _119_1864 = (let _119_1863 = (let _119_1862 = (let _119_1861 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _119_1861))
in Some (_119_1862))
in (f, _119_1863))
in FStar_ToSMT_Term.Assume (_119_1864))
in (_119_1865)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2270, datas, quals, _53_2274) when (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(let _53_2280 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2280) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _53_2283, _53_2285, _53_2287, _53_2289, _53_2291, _53_2293) when ((FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.FStar_Absyn_Syntax.str
in (let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _119_1867 = (let _119_1866 = (primitive_type_axioms t tname tsym)
in (decl)::_119_1866)
in (_119_1867, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2303, datas, quals, _53_2307) -> begin
(let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_19 -> (match (_53_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _53_2314 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(let _53_2324 = c
in (match (_53_2324) with
| (name, args, _53_2321, _53_2323) -> begin
(let _119_1873 = (let _119_1872 = (let _119_1871 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _119_1871, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_119_1872))
in (_119_1873)::[])
end))
end
| false -> begin
(FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun tapp vars -> (match ((((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _119_1879 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _119_1879 FStar_Option.isNone))))))) with
| true -> begin
[]
end
| false -> begin
(let _53_2331 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2331) with
| (xxsym, xx) -> begin
(let _53_2374 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _53_2334 l -> (match (_53_2334) with
| (out, decls) -> begin
(let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _53_2344 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_53_2344) with
| (args, res) -> begin
(let indices = (match ((let _119_1882 = (FStar_Absyn_Util.compress_typ res)
in _119_1882.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_53_2346, indices) -> begin
indices
end
| _53_2351 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _119_1887 = (let _119_1886 = (let _119_1885 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_119_1885, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _119_1886))
in (push_typ_var env a.FStar_Absyn_Syntax.v _119_1887))
end
| FStar_Util.Inr (x) -> begin
(let _119_1890 = (let _119_1889 = (let _119_1888 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_119_1888, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _119_1889))
in (push_term_var env x.FStar_Absyn_Syntax.v _119_1890))
end)) env))
in (let _53_2362 = (encode_args indices env)
in (match (_53_2362) with
| (indices, decls') -> begin
(let _53_2363 = (match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(FStar_All.failwith "Impossible")
end
| false -> begin
()
end)
in (let eqs = (let _119_1897 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _119_1894 = (let _119_1893 = (FStar_ToSMT_Term.mkFreeV v)
in (_119_1893, a))
in (FStar_ToSMT_Term.mkEq _119_1894))
end
| FStar_Util.Inr (a) -> begin
(let _119_1896 = (let _119_1895 = (FStar_ToSMT_Term.mkFreeV v)
in (_119_1895, a))
in (FStar_ToSMT_Term.mkEq _119_1896))
end)) vars indices)
in (FStar_All.pipe_right _119_1897 FStar_ToSMT_Term.mk_and_l))
in (let _119_1902 = (let _119_1901 = (let _119_1900 = (let _119_1899 = (let _119_1898 = (mk_data_tester env l xx)
in (_119_1898, eqs))
in (FStar_ToSMT_Term.mkAnd _119_1899))
in (out, _119_1900))
in (FStar_ToSMT_Term.mkOr _119_1901))
in (_119_1902, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_53_2374) with
| (data_ax, decls) -> begin
(let _53_2377 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2377) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _119_1903 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _119_1903 xx tapp))
in (let _119_1910 = (let _119_1909 = (let _119_1908 = (let _119_1907 = (let _119_1906 = (let _119_1905 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _119_1904 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _119_1905, _119_1904)))
in (FStar_ToSMT_Term.mkForall _119_1906))
in (_119_1907, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_119_1908))
in (_119_1909)::[])
in (FStar_List.append decls _119_1910)))
end))
end))
end))
end))
in (let k = (FStar_Absyn_Util.close_kind tps k)
in (let _53_2389 = (match ((let _119_1911 = (FStar_Absyn_Util.compress_kind k)
in _119_1911.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _53_2385 -> begin
(false, [], k)
end)
in (match (_53_2389) with
| (is_kind_arrow, formals, res) -> begin
(let _53_2396 = (encode_binders None formals env)
in (match (_53_2396) with
| (vars, guards, env', binder_decls, _53_2395) -> begin
(let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _53_20 -> (match (_53_20) with
| FStar_Absyn_Syntax.Projector (_53_2402) -> begin
true
end
| _53_2405 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(let rec projectee = (fun i _53_21 -> (match (_53_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_53_2420) -> begin
(projectee (i + 1) tl)
end
| FStar_Util.Inr (x) -> begin
(match ((x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Absyn_Syntax.idText = "projectee")) with
| true -> begin
i
end
| false -> begin
(projectee (i + 1) tl)
end)
end)
end))
in (let projectee_pos = (projectee 0 formals)
in (let _53_2435 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_53_2426, xx::suffix) -> begin
(xx, suffix)
end
| _53_2432 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_2435) with
| (xx, suffix) -> begin
(let dproj_app = (let _119_1925 = (let _119_1924 = (let _119_1923 = (mk_typ_projector_name d a)
in (let _119_1922 = (let _119_1921 = (FStar_ToSMT_Term.mkFreeV xx)
in (_119_1921)::[])
in (_119_1923, _119_1922)))
in (FStar_ToSMT_Term.mkApp _119_1924))
in (mk_ApplyT _119_1925 suffix))
in (let _119_1930 = (let _119_1929 = (let _119_1928 = (let _119_1927 = (let _119_1926 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _119_1926))
in (FStar_ToSMT_Term.mkForall _119_1927))
in (_119_1928, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_119_1929))
in (_119_1930)::[]))
end))))
end
| _53_2438 -> begin
[]
end))
in (let pretype_axioms = (fun tapp vars -> (let _53_2444 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2444) with
| (xxsym, xx) -> begin
(let _53_2447 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2447) with
| (ffsym, ff) -> begin
(let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _119_1943 = (let _119_1942 = (let _119_1941 = (let _119_1940 = (let _119_1939 = (let _119_1938 = (let _119_1937 = (let _119_1936 = (let _119_1935 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _119_1935))
in (FStar_ToSMT_Term.mkEq _119_1936))
in (xx_has_type, _119_1937))
in (FStar_ToSMT_Term.mkImp _119_1938))
in ((xx_has_type)::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _119_1939))
in (FStar_ToSMT_Term.mkForall _119_1940))
in (_119_1941, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_119_1942))
in (_119_1943)::[]))
end))
end)))
in (let _53_2452 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2452) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _119_1945 = (let _119_1944 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _119_1944))
in (FStar_ToSMT_Term.mkApp _119_1945))
in (let _53_2477 = (let tname_decl = (let _119_1949 = (let _119_1948 = (FStar_All.pipe_right vars (FStar_List.map (fun _53_2458 -> (match (_53_2458) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _119_1947 = (varops.next_id ())
in (tname, _119_1948, FStar_ToSMT_Term.Type_sort, _119_1947)))
in (constructor_or_logic_type_decl _119_1949))
in (let _53_2474 = (match (vars) with
| [] -> begin
(let _119_1953 = (let _119_1952 = (let _119_1951 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _119_1950 -> Some (_119_1950)) _119_1951))
in (push_free_tvar env t tname _119_1952))
in ([], _119_1953))
end
| _53_2462 -> begin
(let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _119_1954 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _119_1954))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match (((not (is_logical)) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_22 -> (match (_53_22) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _53_2469 -> begin
false
end)))))) with
| true -> begin
((ttok_app)::[])::((tapp)::[])::[]
end
| false -> begin
((ttok_app)::[])::[]
end)
in (let name_tok_corr = (let _119_1959 = (let _119_1958 = (let _119_1957 = (let _119_1956 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _119_1956))
in (FStar_ToSMT_Term.mkForall' _119_1957))
in (_119_1958, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_119_1959))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_53_2474) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_53_2477) with
| (decls, env) -> begin
(let kindingAx = (let _53_2480 = (encode_knd res env' tapp)
in (match (_53_2480) with
| (k, decls) -> begin
(let karr = (match (is_kind_arrow) with
| true -> begin
(let _119_1963 = (let _119_1962 = (let _119_1961 = (let _119_1960 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _119_1960))
in (_119_1961, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_119_1962))
in (_119_1963)::[])
end
| false -> begin
[]
end)
in (let _119_1969 = (let _119_1968 = (let _119_1967 = (let _119_1966 = (let _119_1965 = (let _119_1964 = (FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _119_1964))
in (FStar_ToSMT_Term.mkForall _119_1965))
in (_119_1966, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_119_1967))
in (_119_1968)::[])
in (FStar_List.append (FStar_List.append decls karr) _119_1969)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _119_1970 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _119_1970))
end
| false -> begin
(let _119_1977 = (let _119_1975 = (let _119_1973 = (let _119_1971 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _119_1971))
in (let _119_1972 = (inversion_axioms tapp vars)
in (FStar_List.append _119_1973 _119_1972)))
in (let _119_1974 = (projection_axioms tapp vars)
in (FStar_List.append _119_1975 _119_1974)))
in (let _119_1976 = (pretype_axioms tapp vars)
in (FStar_List.append _119_1977 _119_1976)))
end)
in (let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _53_2487, _53_2489, _53_2491, _53_2493, _53_2495) when (FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, _53_2501, quals, _53_2504, drange) -> begin
(let _53_2511 = (new_term_constant_and_tok_from_lid env d)
in (match (_53_2511) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _53_2520 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_53_2520) with
| (formals, t_res) -> begin
(let _53_2523 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2523) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _53_2530 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2530) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _53_23 -> (match (_53_23) with
| FStar_Util.Inl (a) -> begin
(let _119_1979 = (mk_typ_projector_name d a)
in (_119_1979, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _119_1980 = (mk_term_projector_name d x)
in (_119_1980, FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _119_1982 = (let _119_1981 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _119_1981))
in (FStar_All.pipe_right _119_1982 FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _53_2544 = (encode_typ_pred None t env ddtok_tm)
in (match (_53_2544) with
| (tok_typing, decls3) -> begin
(let _53_2551 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2551) with
| (vars', guards', env'', decls_formals, _53_2550) -> begin
(let _53_2556 = (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_53_2556) with
| (ty_pred', decls_pred) -> begin
(let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _53_2560 -> begin
(let _119_1984 = (let _119_1983 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _119_1983))
in (_119_1984)::[])
end)
in (let encode_elim = (fun _53_2563 -> (match (()) with
| () -> begin
(let _53_2566 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_53_2566) with
| (head, args) -> begin
(match ((let _119_1987 = (FStar_Absyn_Util.compress_typ head)
in _119_1987.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _53_2572 = (encode_args args env')
in (match (_53_2572) with
| (encoded_args, arg_decls) -> begin
(let _53_2596 = (FStar_List.fold_left (fun _53_2576 arg -> (match (_53_2576) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(let _53_2584 = (let _119_1990 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _119_1990))
in (match (_53_2584) with
| (_53_2581, tv, env) -> begin
(let _119_1992 = (let _119_1991 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_119_1991)::eqns)
in (env, (tv)::arg_vars, _119_1992))
end))
end
| FStar_Util.Inr (varg) -> begin
(let _53_2591 = (let _119_1993 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _119_1993))
in (match (_53_2591) with
| (_53_2588, xv, env) -> begin
(let _119_1995 = (let _119_1994 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_119_1994)::eqns)
in (env, (xv)::arg_vars, _119_1995))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_53_2596) with
| (_53_2593, arg_vars, eqns) -> begin
(let arg_vars = (FStar_List.rev arg_vars)
in (let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _119_2002 = (let _119_2001 = (let _119_2000 = (let _119_1999 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _119_1998 = (let _119_1997 = (let _119_1996 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _119_1996))
in (FStar_ToSMT_Term.mkImp _119_1997))
in ((ty_pred)::[], _119_1999, _119_1998)))
in (FStar_ToSMT_Term.mkForall _119_2000))
in (_119_2001, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_119_2002))
in (let subterm_ordering = (match ((FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _119_2003 = (varops.fresh "x")
in (_119_2003, FStar_ToSMT_Term.Term_sort))
in (let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _119_2012 = (let _119_2011 = (let _119_2010 = (let _119_2009 = (let _119_2004 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_119_2004)::[])
in (let _119_2008 = (let _119_2007 = (let _119_2006 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _119_2005 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_119_2006, _119_2005)))
in (FStar_ToSMT_Term.mkImp _119_2007))
in (_119_2009, (x)::[], _119_2008)))
in (FStar_ToSMT_Term.mkForall _119_2010))
in (_119_2011, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_119_2012))))
end
| false -> begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _119_2015 = (let _119_2014 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _119_2014 dapp))
in (_119_2015)::[])
end
| _53_2611 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _119_2022 = (let _119_2021 = (let _119_2020 = (let _119_2019 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _119_2018 = (let _119_2017 = (let _119_2016 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _119_2016))
in (FStar_ToSMT_Term.mkImp _119_2017))
in ((ty_pred)::[], _119_2019, _119_2018)))
in (FStar_ToSMT_Term.mkForall _119_2020))
in (_119_2021, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_119_2022)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _53_2615 -> begin
(let _53_2616 = (let _119_2025 = (let _119_2024 = (FStar_Absyn_Print.sli d)
in (let _119_2023 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _119_2024 _119_2023)))
in (FStar_Tc_Errors.warn drange _119_2025))
in ([], []))
end)
end))
end))
in (let _53_2620 = (encode_elim ())
in (match (_53_2620) with
| (decls2, elim) -> begin
(let g = (let _119_2050 = (let _119_2049 = (let _119_2034 = (let _119_2033 = (let _119_2032 = (let _119_2031 = (let _119_2030 = (let _119_2029 = (let _119_2028 = (let _119_2027 = (let _119_2026 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _119_2026))
in Some (_119_2027))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _119_2028))
in FStar_ToSMT_Term.DeclFun (_119_2029))
in (_119_2030)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _119_2031))
in (FStar_List.append _119_2032 proxy_fresh))
in (FStar_List.append _119_2033 decls_formals))
in (FStar_List.append _119_2034 decls_pred))
in (let _119_2048 = (let _119_2047 = (let _119_2046 = (let _119_2038 = (let _119_2037 = (let _119_2036 = (let _119_2035 = (FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _119_2035))
in (FStar_ToSMT_Term.mkForall _119_2036))
in (_119_2037, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_119_2038))
in (let _119_2045 = (let _119_2044 = (let _119_2043 = (let _119_2042 = (let _119_2041 = (let _119_2040 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _119_2039 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _119_2040, _119_2039)))
in (FStar_ToSMT_Term.mkForall _119_2041))
in (_119_2042, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_119_2043))
in (_119_2044)::[])
in (_119_2046)::_119_2045))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_119_2047)
in (FStar_List.append _119_2049 _119_2048)))
in (FStar_List.append _119_2050 elim))
in ((FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _53_2624, _53_2626, _53_2628) -> begin
(let _53_2633 = (encode_signature env ses)
in (match (_53_2633) with
| (g, env) -> begin
(let _53_2645 = (FStar_All.pipe_right g (FStar_List.partition (fun _53_24 -> (match (_53_24) with
| FStar_ToSMT_Term.Assume (_53_2636, Some ("inversion axiom")) -> begin
false
end
| _53_2642 -> begin
true
end))))
in (match (_53_2645) with
| (g', inversions) -> begin
(let _53_2654 = (FStar_All.pipe_right g' (FStar_List.partition (fun _53_25 -> (match (_53_25) with
| FStar_ToSMT_Term.DeclFun (_53_2648) -> begin
true
end
| _53_2651 -> begin
false
end))))
in (match (_53_2654) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_53_2656, _53_2658, _53_2660, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_26 -> (match (_53_26) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _53_2672 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _53_2677, _53_2679, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (FStar_List.length binders)
in (let _53_2691 = (FStar_Util.first_N nbinders formals)
in (match (_53_2691) with
| (formals, extra_formals) -> begin
(let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _119_2065 = (let _119_2064 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _119_2064))
in FStar_Util.Inl (_119_2065))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _119_2067 = (let _119_2066 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _119_2066))
in FStar_Util.Inr (_119_2067))
end
| _53_2705 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _119_2068 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _119_2068 FStar_Absyn_Util.name_binders))
in (let body = (let _119_2074 = (let _119_2070 = (let _119_2069 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _119_2069))
in (body, _119_2070))
in (let _119_2073 = (let _119_2072 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _119_2071 -> Some (_119_2071)) _119_2072))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _119_2074 _119_2073 body.FStar_Absyn_Syntax.pos)))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (let destruct_bound_function = (fun flid t_norm e -> (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_ascribed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (binders, body); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _, _)) | (FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let nformals = (FStar_List.length formals)
in (let nbinders = (FStar_List.length binders)
in (let tres = (FStar_Absyn_Util.comp_result c)
in (match (((nformals < nbinders) && (FStar_Absyn_Util.is_total_comp c))) with
| true -> begin
(let _53_2743 = (FStar_Util.first_N nformals binders)
in (match (_53_2743) with
| (bs0, rest) -> begin
(let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _53_2747 -> begin
(FStar_All.failwith "impossible")
end)
in (let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end
| false -> begin
(match ((nformals > nbinders)) with
| true -> begin
(let _53_2752 = (eta_expand binders formals body tres)
in (match (_53_2752) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end
| false -> begin
(binders, body, formals, tres)
end)
end))))
end
| _53_2754 -> begin
(let _119_2083 = (let _119_2082 = (FStar_Absyn_Print.exp_to_string e)
in (let _119_2081 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Absyn_Syntax.str _119_2082 _119_2081)))
in (FStar_All.failwith _119_2083))
end)
end
| _53_2756 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let tres = (FStar_Absyn_Util.comp_result c)
in (let _53_2764 = (eta_expand [] formals e tres)
in (match (_53_2764) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _53_2766 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _53_2768 -> (match (()) with
| () -> begin
(match ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_27 -> (match (_53_27) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _53_2779 -> begin
false
end))))) with
| true -> begin
([], env)
end
| false -> begin
(match ((FStar_All.pipe_right bindings (FStar_Util.for_some (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) with
| true -> begin
(let _119_2089 = (FStar_All.pipe_right bindings (FStar_List.collect (fun lb -> (match ((FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _119_2088 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _119_2088 lb.FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(Prims.raise Let_rec_unencodeable)
end))))
in (_119_2089, env))
end
| false -> begin
(let _53_2799 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _53_2786 lb -> (match (_53_2786) with
| (toks, typs, decls, env) -> begin
(let _53_2788 = (match ((FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| false -> begin
()
end)
in (let t_norm = (let _119_2092 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _119_2092 FStar_Absyn_Util.compress_typ))
in (let _53_2794 = (let _119_2093 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _119_2093 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_53_2794) with
| (tok, decl, env) -> begin
(let _119_2096 = (let _119_2095 = (let _119_2094 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_119_2094, tok))
in (_119_2095)::toks)
in (_119_2096, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_53_2799) with
| (toks, typs, decls, env) -> begin
(let toks = (FStar_List.rev toks)
in (let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (let typs = (FStar_List.rev typs)
in (match (((FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_28 -> (match (_53_28) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _53_2806 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _119_2099 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _119_2099)))))))) with
| true -> begin
(decls, env)
end
| false -> begin
(match ((not (is_rec))) with
| true -> begin
(match ((bindings, typs, toks)) with
| ({FStar_Absyn_Syntax.lbname = _53_2814; FStar_Absyn_Syntax.lbtyp = _53_2812; FStar_Absyn_Syntax.lbeff = _53_2810; FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _53_2830 = (destruct_bound_function flid t_norm e)
in (match (_53_2830) with
| (binders, body, formals, tres) -> begin
(let _53_2837 = (encode_binders None binders env)
in (match (_53_2837) with
| (vars, guards, env', binder_decls, _53_2836) -> begin
(let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _53_2840 -> begin
(let _119_2101 = (let _119_2100 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _119_2100))
in (FStar_ToSMT_Term.mkApp _119_2101))
end)
in (let _53_2844 = (encode_exp body env')
in (match (_53_2844) with
| (body, decls2) -> begin
(let eqn = (let _119_2110 = (let _119_2109 = (let _119_2106 = (let _119_2105 = (let _119_2104 = (let _119_2103 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _119_2102 = (FStar_ToSMT_Term.mkEq (app, body))
in (_119_2103, _119_2102)))
in (FStar_ToSMT_Term.mkImp _119_2104))
in ((app)::[], vars, _119_2105))
in (FStar_ToSMT_Term.mkForall _119_2106))
in (let _119_2108 = (let _119_2107 = (FStar_Util.format1 "Equation for %s" flid.FStar_Absyn_Syntax.str)
in Some (_119_2107))
in (_119_2109, _119_2108)))
in FStar_ToSMT_Term.Assume (_119_2110))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _53_2847 -> begin
(FStar_All.failwith "Impossible")
end)
end
| false -> begin
(let fuel = (let _119_2111 = (varops.fresh "fuel")
in (_119_2111, FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _53_2864 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _53_2853 _53_2858 -> (match ((_53_2853, _53_2858)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _119_2116 = (let _119_2115 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _119_2114 -> Some (_119_2114)) _119_2115))
in (push_free_var env flid gtok _119_2116))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_53_2864) with
| (gtoks, env) -> begin
(let gtoks = (FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _53_2873 t_norm _53_2882 -> (match ((_53_2873, _53_2882)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _53_2881; FStar_Absyn_Syntax.lbtyp = _53_2879; FStar_Absyn_Syntax.lbeff = _53_2877; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _53_2887 = (destruct_bound_function flid t_norm e)
in (match (_53_2887) with
| (binders, body, formals, tres) -> begin
(let _53_2894 = (encode_binders None binders env)
in (match (_53_2894) with
| (vars, guards, env', binder_decls, _53_2893) -> begin
(let decl_g = (let _119_2127 = (let _119_2126 = (let _119_2125 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_119_2125)
in (g, _119_2126, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_119_2127))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _119_2130 = (let _119_2129 = (let _119_2128 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_119_2128)::vars_tm)
in (g, _119_2129))
in (FStar_ToSMT_Term.mkApp _119_2130))
in (let gmax = (let _119_2133 = (let _119_2132 = (let _119_2131 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_119_2131)::vars_tm)
in (g, _119_2132))
in (FStar_ToSMT_Term.mkApp _119_2133))
in (let _53_2904 = (encode_exp body env')
in (match (_53_2904) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _119_2142 = (let _119_2141 = (let _119_2138 = (let _119_2137 = (let _119_2136 = (let _119_2135 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _119_2134 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_119_2135, _119_2134)))
in (FStar_ToSMT_Term.mkImp _119_2136))
in ((gsapp)::[], (fuel)::vars, _119_2137))
in (FStar_ToSMT_Term.mkForall _119_2138))
in (let _119_2140 = (let _119_2139 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Absyn_Syntax.str)
in Some (_119_2139))
in (_119_2141, _119_2140)))
in FStar_ToSMT_Term.Assume (_119_2142))
in (let eqn_f = (let _119_2146 = (let _119_2145 = (let _119_2144 = (let _119_2143 = (FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _119_2143))
in (FStar_ToSMT_Term.mkForall _119_2144))
in (_119_2145, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_119_2146))
in (let eqn_g' = (let _119_2155 = (let _119_2154 = (let _119_2153 = (let _119_2152 = (let _119_2151 = (let _119_2150 = (let _119_2149 = (let _119_2148 = (let _119_2147 = (FStar_ToSMT_Term.n_fuel 0)
in (_119_2147)::vars_tm)
in (g, _119_2148))
in (FStar_ToSMT_Term.mkApp _119_2149))
in (gsapp, _119_2150))
in (FStar_ToSMT_Term.mkEq _119_2151))
in ((gsapp)::[], (fuel)::vars, _119_2152))
in (FStar_ToSMT_Term.mkForall _119_2153))
in (_119_2154, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_119_2155))
in (let _53_2927 = (let _53_2914 = (encode_binders None formals env0)
in (match (_53_2914) with
| (vars, v_guards, env, binder_decls, _53_2913) -> begin
(let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _119_2156 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _119_2156 ((fuel)::vars)))
in (let _119_2160 = (let _119_2159 = (let _119_2158 = (let _119_2157 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _119_2157))
in (FStar_ToSMT_Term.mkForall _119_2158))
in (_119_2159, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_119_2160)))
in (let _53_2924 = (let _53_2921 = (encode_typ_pred None tres env gapp)
in (match (_53_2921) with
| (g_typing, d3) -> begin
(let _119_2168 = (let _119_2167 = (let _119_2166 = (let _119_2165 = (let _119_2164 = (let _119_2163 = (let _119_2162 = (let _119_2161 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_119_2161, g_typing))
in (FStar_ToSMT_Term.mkImp _119_2162))
in ((gapp)::[], (fuel)::vars, _119_2163))
in (FStar_ToSMT_Term.mkForall _119_2164))
in (_119_2165, None))
in FStar_ToSMT_Term.Assume (_119_2166))
in (_119_2167)::[])
in (d3, _119_2168))
end))
in (match (_53_2924) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_53_2927) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _53_2943 = (let _119_2171 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _53_2931 _53_2935 -> (match ((_53_2931, _53_2935)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _53_2939 = (encode_one_binding env0 gtok ty bs)
in (match (_53_2939) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _119_2171))
in (match (_53_2943) with
| (decls, eqns, env0) -> begin
(let _53_2952 = (let _119_2173 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _119_2173 (FStar_List.partition (fun _53_29 -> (match (_53_29) with
| FStar_ToSMT_Term.DeclFun (_53_2946) -> begin
true
end
| _53_2949 -> begin
false
end)))))
in (match (_53_2952) with
| (prefix_decls, rest) -> begin
(let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end)
end))))
end))
end)
end)
end)) (fun _53_2767 -> (match (_53_2767) with
| Let_rec_unencodeable -> begin
(let msg = (let _119_2176 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _119_2176 (FStar_String.concat " and ")))
in (let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _53_2979 = (encode_free_var env x t t_norm [])
in (match (_53_2979) with
| (decls, env) -> begin
(let _53_2984 = (lookup_lid env x)
in (match (_53_2984) with
| (n, x', _53_2983) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _53_2988) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun env lid t -> (let _53_2996 = (encode_function_type_as_formula None t env)
in (match (_53_2996) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun env lid tt t_norm quals -> (match (((let _119_2189 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _119_2189)) || (FStar_Absyn_Util.is_lemma t_norm))) with
| true -> begin
(let _53_3005 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3005) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_3008) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _53_30 -> (match (_53_30) with
| (FStar_Util.Inl (_53_3013), _53_3016) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3019 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _53_3021 -> begin
[]
end)
in (let d = FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (let dd = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end
| false -> begin
(match ((prims.is lid)) with
| true -> begin
(let vname = (varops.new_fvar lid)
in (let definition = (prims.mk lid vname)
in (let env = (push_free_var env lid vname None)
in (definition, env))))
end
| false -> begin
(let encode_non_total_function_typ = (lid.FStar_Absyn_Syntax.nsstr <> "Prims")
in (let _53_3038 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _119_2191 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _119_2191))
end
| false -> begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end)
end
| None -> begin
([], (None, t_norm))
end)
in (match (_53_3038) with
| (formals, (pre_opt, res_t)) -> begin
(let _53_3042 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3042) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _53_3045 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _53_31 -> (match (_53_31) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _53_3061 = (FStar_Util.prefix vars)
in (match (_53_3061) with
| (_53_3056, (xxsym, _53_3059)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _119_2208 = (let _119_2207 = (let _119_2206 = (let _119_2205 = (let _119_2204 = (let _119_2203 = (let _119_2202 = (let _119_2201 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Absyn_Syntax.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _119_2201))
in (vapp, _119_2202))
in (FStar_ToSMT_Term.mkEq _119_2203))
in ((vapp)::[], vars, _119_2204))
in (FStar_ToSMT_Term.mkForall _119_2205))
in (_119_2206, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_119_2207))
in (_119_2208)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(let _53_3074 = (FStar_Util.prefix vars)
in (match (_53_3074) with
| (_53_3069, (xxsym, _53_3072)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _119_2210 = (let _119_2209 = (mk_term_projector_name d f)
in (_119_2209, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _119_2210))
in (let _119_2215 = (let _119_2214 = (let _119_2213 = (let _119_2212 = (let _119_2211 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in ((vapp)::[], vars, _119_2211))
in (FStar_ToSMT_Term.mkForall _119_2212))
in (_119_2213, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_119_2214))
in (_119_2215)::[])))
end))
end
| _53_3078 -> begin
[]
end)))))
in (let _53_3085 = (encode_binders None formals env)
in (match (_53_3085) with
| (vars, guards, env', decls1, _53_3084) -> begin
(let _53_3094 = (match (pre_opt) with
| None -> begin
(let _119_2216 = (FStar_ToSMT_Term.mk_and_l guards)
in (_119_2216, decls1))
end
| Some (p) -> begin
(let _53_3091 = (encode_formula p env')
in (match (_53_3091) with
| (g, ds) -> begin
(let _119_2217 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_119_2217, (FStar_List.append decls1 ds)))
end))
end)
in (match (_53_3094) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _119_2219 = (let _119_2218 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _119_2218))
in (FStar_ToSMT_Term.mkApp _119_2219))
in (let _53_3125 = (let vname_decl = (let _119_2222 = (let _119_2221 = (FStar_All.pipe_right formals (FStar_List.map (fun _53_32 -> (match (_53_32) with
| (FStar_Util.Inl (_53_3099), _53_3102) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3105 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _119_2221, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_119_2222))
in (let _53_3112 = (let env = (let _53_3107 = env
in {bindings = _53_3107.bindings; depth = _53_3107.depth; tcenv = _53_3107.tcenv; warn = _53_3107.warn; cache = _53_3107.cache; nolabels = _53_3107.nolabels; use_zfuel_name = _53_3107.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((not ((head_normal env tt)))) with
| true -> begin
(encode_typ_pred None tt env vtok_tm)
end
| false -> begin
(encode_typ_pred None t_norm env vtok_tm)
end))
in (match (_53_3112) with
| (tok_typing, decls2) -> begin
(let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _53_3122 = (match (formals) with
| [] -> begin
(let _119_2226 = (let _119_2225 = (let _119_2224 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _119_2223 -> Some (_119_2223)) _119_2224))
in (push_free_var env lid vname _119_2225))
in ((FStar_List.append decls2 ((tok_typing)::[])), _119_2226))
end
| _53_3116 -> begin
(let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _119_2227 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _119_2227))
in (let name_tok_corr = (let _119_2231 = (let _119_2230 = (let _119_2229 = (let _119_2228 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _119_2228))
in (FStar_ToSMT_Term.mkForall _119_2229))
in (_119_2230, None))
in FStar_ToSMT_Term.Assume (_119_2231))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_53_3122) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_53_3125) with
| (decls2, env) -> begin
(let _53_3133 = (let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (let _53_3129 = (encode_typ_term res_t env')
in (match (_53_3129) with
| (encoded_res_t, decls) -> begin
(let _119_2232 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _119_2232, decls))
end)))
in (match (_53_3133) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _119_2236 = (let _119_2235 = (let _119_2234 = (let _119_2233 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _119_2233))
in (FStar_ToSMT_Term.mkForall _119_2234))
in (_119_2235, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_119_2236))
in (let g = (let _119_2238 = (let _119_2237 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_119_2237)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _119_2238))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end)
end))
and encode_signature = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _53_3140 se -> (match (_53_3140) with
| (g, env) -> begin
(let _53_3144 = (encode_sigelt env se)
in (match (_53_3144) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun env bindings -> (let encode_binding = (fun b _53_3151 -> (match (_53_3151) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(let _53_3159 = (new_term_constant env x)
in (match (_53_3159) with
| (xxsym, xx, env') -> begin
(let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _53_3161 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _119_2253 = (FStar_Absyn_Print.strBvd x)
in (let _119_2252 = (FStar_Absyn_Print.typ_to_string t0)
in (let _119_2251 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.fprint3 "Normalized %s : %s to %s\n" _119_2253 _119_2252 _119_2251))))
end
| false -> begin
()
end)
in (let _53_3165 = (encode_typ_pred None t1 env xx)
in (match (_53_3165) with
| (t, decls') -> begin
(let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _119_2257 = (let _119_2256 = (FStar_Absyn_Print.strBvd x)
in (let _119_2255 = (FStar_Absyn_Print.typ_to_string t0)
in (let _119_2254 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _119_2256 _119_2255 _119_2254))))
in Some (_119_2257))
end
| false -> begin
None
end)
in (let g = (FStar_List.append (FStar_List.append ((FStar_ToSMT_Term.DeclFun ((xxsym, [], FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let _53_3175 = (new_typ_constant env a)
in (match (_53_3175) with
| (aasym, aa, env') -> begin
(let _53_3178 = (encode_knd k env aa)
in (match (_53_3178) with
| (k, decls') -> begin
(let g = (let _119_2263 = (let _119_2262 = (let _119_2261 = (let _119_2260 = (let _119_2259 = (let _119_2258 = (FStar_Absyn_Print.strBvd a)
in Some (_119_2258))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _119_2259))
in FStar_ToSMT_Term.DeclFun (_119_2260))
in (_119_2261)::[])
in (FStar_List.append _119_2262 decls'))
in (FStar_List.append _119_2263 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(let t_norm = (whnf env t)
in (let _53_3187 = (encode_free_var env x t t_norm [])
in (match (_53_3187) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(let _53_3192 = (encode_sigelt env se)
in (match (_53_3192) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _53_3199 -> (match (_53_3199) with
| (l, _53_3196, _53_3198) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _53_3206 -> (match (_53_3206) with
| (l, _53_3203, _53_3205) -> begin
(let _119_2271 = (FStar_All.pipe_left (fun _119_2267 -> FStar_ToSMT_Term.Echo (_119_2267)) (Prims.fst l))
in (let _119_2270 = (let _119_2269 = (let _119_2268 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_119_2268))
in (_119_2269)::[])
in (_119_2271)::_119_2270))
end))))
in (prefix, suffix))))

let last_env = (FStar_Util.mk_ref [])

let init_env = (fun tcenv -> (let _119_2276 = (let _119_2275 = (let _119_2274 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _119_2274; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_119_2275)::[])
in (FStar_ST.op_Colon_Equals last_env _119_2276)))

let get_env = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_53_3212 -> begin
(let _53_3215 = e
in {bindings = _53_3215.bindings; depth = _53_3215.depth; tcenv = tcenv; warn = _53_3215.warn; cache = _53_3215.cache; nolabels = _53_3215.nolabels; use_zfuel_name = _53_3215.use_zfuel_name; encode_non_total_function_typ = _53_3215.encode_non_total_function_typ})
end))

let set_env = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _53_3221::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun _53_3223 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (FStar_Util.smap_copy hd.cache)
in (let top = (let _53_3229 = hd
in {bindings = _53_3229.bindings; depth = _53_3229.depth; tcenv = _53_3229.tcenv; warn = _53_3229.warn; cache = refs; nolabels = _53_3229.nolabels; use_zfuel_name = _53_3229.use_zfuel_name; encode_non_total_function_typ = _53_3229.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env = (fun _53_3232 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _53_3236::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env = (fun _53_3238 -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun _53_3239 -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun _53_3240 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_53_3243::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _53_3248 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let init = (fun tcenv -> (let _53_3250 = (init_env tcenv)
in (let _53_3252 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun msg -> (let _53_3255 = (push_env ())
in (let _53_3257 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))

let pop = (fun msg -> (let _53_3260 = (let _119_2297 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _119_2297))
in (let _53_3262 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))

let mark = (fun msg -> (let _53_3265 = (mark_env ())
in (let _53_3267 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun msg -> (let _53_3270 = (reset_mark_env ())
in (let _53_3272 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _53_3275 = (commit_mark_env ())
in (let _53_3277 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun tcenv se -> (let caption = (fun decls -> (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _119_2311 = (let _119_2310 = (let _119_2309 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _119_2309))
in FStar_ToSMT_Term.Caption (_119_2310))
in (_119_2311)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _53_3286 = (encode_sigelt env se)
in (match (_53_3286) with
| (decls, env) -> begin
(let _53_3287 = (set_env env)
in (let _119_2312 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _119_2312)))
end)))))

let encode_modul = (fun tcenv modul -> (let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)
in (let _53_3292 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(let _119_2317 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.fprint2 "Encoding externals for %s ... %s exports\n" name _119_2317))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _53_3299 = (encode_signature (let _53_3295 = env
in {bindings = _53_3295.bindings; depth = _53_3295.depth; tcenv = _53_3295.tcenv; warn = false; cache = _53_3295.cache; nolabels = _53_3295.nolabels; use_zfuel_name = _53_3295.use_zfuel_name; encode_non_total_function_typ = _53_3295.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_53_3299) with
| (decls, env) -> begin
(let caption = (fun decls -> (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _53_3305 = (set_env (let _53_3303 = env
in {bindings = _53_3303.bindings; depth = _53_3303.depth; tcenv = _53_3303.tcenv; warn = true; cache = _53_3303.cache; nolabels = _53_3303.nolabels; use_zfuel_name = _53_3303.use_zfuel_name; encode_non_total_function_typ = _53_3303.encode_non_total_function_typ}))
in (let _53_3307 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(FStar_Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun tcenv q -> (let _53_3312 = (let _119_2326 = (let _119_2325 = (let _119_2324 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _119_2324))
in (FStar_Util.format1 "Starting query at %s" _119_2325))
in (push _119_2326))
in (let pop = (fun _53_3315 -> (match (()) with
| () -> begin
(let _119_2331 = (let _119_2330 = (let _119_2329 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _119_2329))
in (FStar_Util.format1 "Ending query at %s" _119_2330))
in (pop _119_2331))
end))
in (let _53_3345 = (let env = (get_env tcenv)
in (let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _53_3328 = (let _119_2335 = (FStar_List.filter (fun _53_33 -> (match (_53_33) with
| FStar_Tc_Env.Binding_sig (_53_3322) -> begin
false
end
| _53_3325 -> begin
true
end)) bindings)
in (encode_env_bindings env _119_2335))
in (match (_53_3328) with
| (env_decls, env) -> begin
(let _53_3329 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(let _119_2336 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.fprint1 "Encoding query formula: %s\n" _119_2336))
end
| false -> begin
()
end)
in (let _53_3334 = (encode_formula_with_labels q env)
in (match (_53_3334) with
| (phi, labels, qdecls) -> begin
(let _53_3337 = (encode_labels labels)
in (match (_53_3337) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _119_2338 = (let _119_2337 = (FStar_ToSMT_Term.mkNot phi)
in (_119_2337, Some ("query")))
in FStar_ToSMT_Term.Assume (_119_2338))
in (let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_53_3345) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _53_3352); FStar_ToSMT_Term.hash = _53_3349; FStar_ToSMT_Term.freevars = _53_3347}, _53_3357) -> begin
(let _53_3360 = (pop ())
in ())
end
| _53_3363 when tcenv.FStar_Tc_Env.admit -> begin
(let _53_3364 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _53_3368) -> begin
(let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (let _53_3372 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _53_3378 -> (match (_53_3378) with
| (n, i) -> begin
(let _119_2361 = (let _119_2360 = (let _119_2345 = (let _119_2344 = (FStar_Util.string_of_int n)
in (let _119_2343 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _119_2344 _119_2343)))
in FStar_ToSMT_Term.Caption (_119_2345))
in (let _119_2359 = (let _119_2358 = (let _119_2350 = (let _119_2349 = (let _119_2348 = (let _119_2347 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _119_2346 = (FStar_ToSMT_Term.n_fuel n)
in (_119_2347, _119_2346)))
in (FStar_ToSMT_Term.mkEq _119_2348))
in (_119_2349, None))
in FStar_ToSMT_Term.Assume (_119_2350))
in (let _119_2357 = (let _119_2356 = (let _119_2355 = (let _119_2354 = (let _119_2353 = (let _119_2352 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _119_2351 = (FStar_ToSMT_Term.n_fuel i)
in (_119_2352, _119_2351)))
in (FStar_ToSMT_Term.mkEq _119_2353))
in (_119_2354, None))
in FStar_ToSMT_Term.Assume (_119_2355))
in (_119_2356)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_119_2358)::_119_2357))
in (_119_2360)::_119_2359))
in (FStar_List.append _119_2361 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _119_2365 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _119_2364 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_119_2365, _119_2364)))
in (let alt_configs = (let _119_2384 = (let _119_2383 = (match (((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) with
| true -> begin
(let _119_2368 = (let _119_2367 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _119_2366 = (FStar_ST.read FStar_Options.max_ifuel)
in (_119_2367, _119_2366)))
in (_119_2368)::[])
end
| false -> begin
[]
end)
in (let _119_2382 = (let _119_2381 = (match ((((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel))) with
| true -> begin
(let _119_2371 = (let _119_2370 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _119_2369 = (FStar_ST.read FStar_Options.max_ifuel)
in (_119_2370, _119_2369)))
in (_119_2371)::[])
end
| false -> begin
[]
end)
in (let _119_2380 = (let _119_2379 = (match ((((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)))) with
| true -> begin
(let _119_2374 = (let _119_2373 = (FStar_ST.read FStar_Options.max_fuel)
in (let _119_2372 = (FStar_ST.read FStar_Options.max_ifuel)
in (_119_2373, _119_2372)))
in (_119_2374)::[])
end
| false -> begin
[]
end)
in (let _119_2378 = (let _119_2377 = (match (((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel))) with
| true -> begin
(let _119_2376 = (let _119_2375 = (FStar_ST.read FStar_Options.min_fuel)
in (_119_2375, 1))
in (_119_2376)::[])
end
| false -> begin
[]
end)
in (_119_2377)::[])
in (_119_2379)::_119_2378))
in (_119_2381)::_119_2380))
in (_119_2383)::_119_2382))
in (FStar_List.flatten _119_2384))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _53_3387 -> begin
errs
end)
in (let _53_3389 = (match ((FStar_ST.read FStar_Options.print_fuels)) with
| true -> begin
(let _119_2392 = (let _119_2387 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _119_2387))
in (let _119_2391 = (let _119_2388 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _119_2388 FStar_Util.string_of_int))
in (let _119_2390 = (let _119_2389 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _119_2389 FStar_Util.string_of_int))
in (FStar_Util.fprint3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _119_2392 _119_2391 _119_2390))))
end
| false -> begin
()
end)
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun p errs _53_34 -> (match (_53_34) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _119_2403 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _119_2403 (cb mi p [])))
end
| _53_3401 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _119_2405 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _119_2405 (fun _53_3407 -> (match (_53_3407) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _53_3410 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _53_3413 p alt _53_3418 -> (match ((_53_3413, _53_3418)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
(match (ok) with
| true -> begin
(match ((FStar_ST.read FStar_Options.print_fuels)) with
| true -> begin
(let _119_2413 = (let _119_2410 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _119_2410))
in (let _119_2412 = (FStar_Util.string_of_int prev_fuel)
in (let _119_2411 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.fprint3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _119_2413 _119_2412 _119_2411))))
end
| false -> begin
()
end)
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _119_2414 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _119_2414 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> (match (((FStar_ST.read FStar_Options.split_cases) > 0)) with
| true -> begin
(let _53_3423 = (let _119_2420 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _119_2420 q))
in (match (_53_3423) with
| (b, cb) -> begin
(match (b) with
| true -> begin
(FStar_ToSMT_SplitQueryCases.handle_query cb check)
end
| false -> begin
(check q)
end)
end))
end
| false -> begin
(check q)
end))
in (let _53_3424 = (match ((FStar_ST.read FStar_Options.admit_smt_queries)) with
| true -> begin
()
end
| false -> begin
(process_query qry)
end)
in (pop ())))))))
end)
end)))))

let is_trivial = (fun tcenv q -> (let env = (get_env tcenv)
in (let _53_3429 = (push "query")
in (let _53_3436 = (encode_formula_with_labels q env)
in (match (_53_3436) with
| (f, _53_3433, _53_3435) -> begin
(let _53_3437 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_3441) -> begin
true
end
| _53_3445 -> begin
false
end))
end)))))

let solver = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}

let dummy = {FStar_Tc_Env.init = (fun _53_3446 -> ()); FStar_Tc_Env.push = (fun _53_3448 -> ()); FStar_Tc_Env.pop = (fun _53_3450 -> ()); FStar_Tc_Env.mark = (fun _53_3452 -> ()); FStar_Tc_Env.reset_mark = (fun _53_3454 -> ()); FStar_Tc_Env.commit_mark = (fun _53_3456 -> ()); FStar_Tc_Env.encode_modul = (fun _53_3458 _53_3460 -> ()); FStar_Tc_Env.encode_sig = (fun _53_3462 _53_3464 -> ()); FStar_Tc_Env.solve = (fun _53_3466 _53_3468 -> ()); FStar_Tc_Env.is_trivial = (fun _53_3470 _53_3472 -> false); FStar_Tc_Env.finish = (fun _53_3474 -> ()); FStar_Tc_Env.refresh = (fun _53_3475 -> ())}





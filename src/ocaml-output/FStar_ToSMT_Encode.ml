
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

let mk_typ_projector_name = (fun lid a -> (let _122_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _122_14)))

let mk_term_projector_name = (fun lid a -> (let a = (let _122_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _122_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _122_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _122_20))))

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _53_62 -> (match (()) with
| () -> begin
(let _122_30 = (let _122_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _122_29 lid.FStar_Absyn_Syntax.str))
in (FStar_All.failwith _122_30))
end))
in (let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _122_31 = (FStar_Absyn_Util.compress_typ t)
in _122_31.FStar_Absyn_Syntax.n)) with
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

let mk_term_projector_name_by_pos = (fun lid i -> (let _122_37 = (let _122_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str _122_36))
in (FStar_All.pipe_left escape _122_37)))

let mk_typ_projector = (fun lid a -> (let _122_43 = (let _122_42 = (mk_typ_projector_name lid a)
in (_122_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _122_43)))

let mk_term_projector = (fun lid a -> (let _122_49 = (let _122_48 = (mk_term_projector_name lid a)
in (_122_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _122_49)))

let mk_term_projector_by_pos = (fun lid i -> (let _122_55 = (let _122_54 = (mk_term_projector_name_by_pos lid i)
in (_122_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _122_55)))

let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Absyn_Syntax.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.ident  ->  Prims.string; new_fvar : FStar_Absyn_Syntax.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _53_101 -> (match (()) with
| () -> begin
(let _122_159 = (FStar_Util.smap_create 100)
in (let _122_158 = (FStar_Util.smap_create 100)
in (_122_159, _122_158)))
end))
in (let scopes = (let _122_161 = (let _122_160 = (new_scope ())
in (_122_160)::[])
in (FStar_Util.mk_ref _122_161))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _122_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _122_165 (fun _53_109 -> (match (_53_109) with
| (names, _53_108) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_53_112) -> begin
(let _53_114 = (FStar_Util.incr ctr)
in (let _122_167 = (let _122_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _122_166))
in (Prims.strcat (Prims.strcat y "__") _122_167)))
end)
in (let top_scope = (let _122_169 = (let _122_168 = (FStar_ST.read scopes)
in (FStar_List.hd _122_168))
in (FStar_All.pipe_left Prims.fst _122_169))
in (let _53_118 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _122_175 = (let _122_174 = (FStar_All.pipe_left mk_unique pp.FStar_Absyn_Syntax.idText)
in (Prims.strcat _122_174 "__"))
in (Prims.strcat _122_175 rn.FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Absyn_Syntax.str))
in (let next_id = (fun _53_126 -> (match (()) with
| () -> begin
(let _53_127 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _122_183 = (let _122_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _122_182))
in (FStar_Util.format2 "%s_%s" pfx _122_183)))
in (let string_const = (fun s -> (match ((let _122_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _122_187 (fun _53_136 -> (match (_53_136) with
| (_53_134, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _122_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _122_188))
in (let top_scope = (let _122_190 = (let _122_189 = (FStar_ST.read scopes)
in (FStar_List.hd _122_189))
in (FStar_All.pipe_left Prims.snd _122_190))
in (let _53_143 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _53_146 -> (match (()) with
| () -> begin
(let _122_195 = (let _122_194 = (new_scope ())
in (let _122_193 = (FStar_ST.read scopes)
in (_122_194)::_122_193))
in (FStar_ST.op_Colon_Equals scopes _122_195))
end))
in (let pop = (fun _53_148 -> (match (()) with
| () -> begin
(let _122_199 = (let _122_198 = (FStar_ST.read scopes)
in (FStar_List.tl _122_198))
in (FStar_ST.op_Colon_Equals scopes _122_199))
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

let unmangle = (fun x -> (let _122_215 = (let _122_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _122_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_122_214, _122_213)))
in (FStar_Absyn_Util.mkbvd _122_215)))

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

let print_env = (fun e -> (let _122_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _53_2 -> (match (_53_2) with
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
in (FStar_All.pipe_right _122_301 (FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

let caption_t = (fun env t -> (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _122_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_122_311))
end
| false -> begin
None
end))

let fresh_fvar = (fun x s -> (let xsym = (varops.fresh x)
in (let _122_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _122_316))))

let gen_term_var = (fun env x -> (let ysym = (let _122_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _122_321))
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
(let _122_336 = (let _122_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _122_335))
in (FStar_All.failwith _122_336))
end
| Some (b, t) -> begin
t
end))

let gen_typ_var = (fun env x -> (let ysym = (let _122_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _122_341))
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
(let _122_356 = (let _122_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _122_355))
in (FStar_All.failwith _122_356))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _122_367 = (let _53_295 = env
in (let _122_366 = (let _122_365 = (let _122_364 = (let _122_363 = (let _122_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _122_361 -> Some (_122_361)) _122_362))
in (x, fname, _122_363, None))
in Binding_fvar (_122_364))
in (_122_365)::env.bindings)
in {bindings = _122_366; depth = _53_295.depth; tcenv = _53_295.tcenv; warn = _53_295.warn; cache = _53_295.cache; nolabels = _53_295.nolabels; use_zfuel_name = _53_295.use_zfuel_name; encode_non_total_function_typ = _53_295.encode_non_total_function_typ}))
in (fname, ftok, _122_367)))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _53_5 -> (match (_53_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _53_307 -> begin
None
end))))

let lookup_lid = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _122_378 = (let _122_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _122_377))
in (FStar_All.failwith _122_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun env x fname ftok -> (let _53_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _53_317.depth; tcenv = _53_317.tcenv; warn = _53_317.warn; cache = _53_317.cache; nolabels = _53_317.nolabels; use_zfuel_name = _53_317.use_zfuel_name; encode_non_total_function_typ = _53_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun env x f -> (let _53_326 = (lookup_lid env x)
in (match (_53_326) with
| (t1, t2, _53_325) -> begin
(let t3 = (let _122_395 = (let _122_394 = (let _122_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_122_393)::[])
in (f, _122_394))
in (FStar_ToSMT_Term.mkApp _122_395))
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
(match ((let _122_399 = (let _122_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _122_398 Prims.fst))
in (FStar_Util.starts_with _122_399 "fuel"))) with
| true -> begin
(let _122_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _122_400 fuel))
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
(let _122_402 = (let _122_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _122_401))
in (FStar_All.failwith _122_402))
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
in (let _122_417 = (let _53_392 = env
in (let _122_416 = (let _122_415 = (let _122_414 = (let _122_413 = (let _122_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _122_411 -> Some (_122_411)) _122_412))
in (x, fname, _122_413))
in Binding_ftvar (_122_414))
in (_122_415)::env.bindings)
in {bindings = _122_416; depth = _53_392.depth; tcenv = _53_392.tcenv; warn = _53_392.warn; cache = _53_392.cache; nolabels = _53_392.nolabels; use_zfuel_name = _53_392.use_zfuel_name; encode_non_total_function_typ = _53_392.encode_non_total_function_typ}))
in (fname, ftok, _122_417)))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _53_6 -> (match (_53_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _53_403 -> begin
None
end)))) with
| None -> begin
(let _122_424 = (let _122_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _122_423))
in (FStar_All.failwith _122_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun env x fname ftok -> (let _53_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _53_411.depth; tcenv = _53_411.tcenv; warn = _53_411.warn; cache = _53_411.cache; nolabels = _53_411.nolabels; use_zfuel_name = _53_411.use_zfuel_name; encode_non_total_function_typ = _53_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun env a -> (match ((let _122_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _122_435 Prims.snd))) with
| None -> begin
(let _122_437 = (let _122_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _122_436))
in (FStar_All.failwith _122_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> (let _122_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _122_440 Prims.fst)))

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
(let _122_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _122_453))
end
| _53_469 -> begin
(let _122_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _122_454 FStar_List.hd))
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
(let _122_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _122_460 FStar_Option.isNone))
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

let trivial_post = (fun t -> (let _122_482 = (let _122_481 = (let _122_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_122_479)::[])
in (let _122_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_122_481, _122_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _122_482 None t.FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _122_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _122_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _122_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _122_490))
end
| _53_527 -> begin
(let _122_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _122_491))
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
(let _122_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _122_504))
end
| _53_542 -> begin
(let _122_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _122_505))
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
(let _122_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _122_561))
end
| FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _122_562 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_ToSMT_Term.boxInt _122_562))
end
| FStar_Absyn_Syntax.Const_int (i) -> begin
(let _122_563 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _122_563))
end
| FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _122_567 = (let _122_566 = (let _122_565 = (let _122_564 = (FStar_ToSMT_Term.mkInteger32 i)
in (FStar_ToSMT_Term.boxInt _122_564))
in (_122_565)::[])
in ("FStar.Int32.Int32", _122_566))
in (FStar_ToSMT_Term.mkApp _122_567))
end
| FStar_Absyn_Syntax.Const_string (bytes, _53_627) -> begin
(let _122_568 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _122_568))
end
| c -> begin
(let _122_570 = (let _122_569 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _122_569))
in (FStar_All.failwith _122_570))
end))

let as_function_typ = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_53_638) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_53_641) -> begin
(let _122_579 = (FStar_Absyn_Util.unrefine t)
in (aux true _122_579))
end
| _53_644 -> begin
(match (norm) with
| true -> begin
(let _122_580 = (whnf env t)
in (aux false _122_580))
end
| false -> begin
(let _122_583 = (let _122_582 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _122_581 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _122_582 _122_581)))
in (FStar_All.failwith _122_583))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun k env -> (match ((let _122_620 = (FStar_Absyn_Util.compress_kind k)
in _122_620.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_53_649, k0) -> begin
(let _53_653 = (match ((FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _122_622 = (FStar_Absyn_Print.kind_to_string k)
in (let _122_621 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _122_622 _122_621)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _53_657) -> begin
(let _122_624 = (let _122_623 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _122_623))
in (_122_624, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(let tsym = (let _122_625 = (varops.fresh "t")
in (_122_625, FStar_ToSMT_Term.Type_sort))
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
(let _122_634 = (let _122_633 = (let _122_632 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _122_632))
in (_122_633, body))
in (FStar_ToSMT_Term.mkAnd _122_634))
end)
in (let _122_636 = (let _122_635 = (FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _122_635))
in (FStar_ToSMT_Term.mkForall _122_636)))))
end
| _53_698 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _122_638 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _122_638 (FStar_List.filter (fun _53_703 -> (match (_53_703) with
| (x, _53_702) -> begin
(x <> (Prims.fst tsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _53_709) -> begin
(let _122_641 = (let _122_640 = (let _122_639 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _122_639))
in (FStar_ToSMT_Term.mkApp _122_640))
in (_122_641, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _122_642 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_122_642))
end
| false -> begin
None
end)
in (let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _122_644 = (let _122_643 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _122_643))
in (FStar_ToSMT_Term.mkApp _122_644))
in (let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _122_653 = (let _122_652 = (let _122_651 = (let _122_650 = (let _122_649 = (let _122_648 = (let _122_647 = (let _122_646 = (let _122_645 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _122_645))
in (_122_646, k_interp))
in (FStar_ToSMT_Term.mkAnd _122_647))
in (t_has_k, _122_648))
in (FStar_ToSMT_Term.mkIff _122_649))
in ((t_has_k)::[], (tsym)::cvars, _122_650))
in (FStar_ToSMT_Term.mkForall _122_651))
in (_122_652, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_122_653))
in (let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _53_721 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _53_724 -> begin
(let _122_655 = (let _122_654 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _122_654))
in (FStar_All.failwith _122_655))
end))
and encode_knd = (fun k env t -> (let _53_730 = (encode_knd_term k env)
in (match (_53_730) with
| (k, decls) -> begin
(let _122_659 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_122_659, decls))
end)))
and encode_binders = (fun fuel_opt bs env -> (let _53_734 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _122_663 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.fprint1 "Encoding binders %s\n" _122_663))
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
(let _122_667 = (FStar_Absyn_Print.strBvd a)
in (let _122_666 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _122_667 aasym _122_666)))
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
(let _53_772 = (let _122_668 = (norm_t env t)
in (encode_typ_pred fuel_opt _122_668 env xx))
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
(let _122_673 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_122_673, decls))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _53_800 = (encode_typ_term t env)
in (match (_53_800) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _122_678 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_122_678, decls))
end
| Some (f) -> begin
(let _122_679 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_122_679, decls))
end)
end))))
and encode_typ_term = (fun t env -> (let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _122_682 = (lookup_typ_var env a)
in (_122_682, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _122_683 = (lookup_free_tvar env fv)
in (_122_683, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
(match (((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _53_821 = (encode_binders None binders env)
in (match (_53_821) with
| (vars, guards, env', decls, _53_820) -> begin
(let fsym = (let _122_684 = (varops.fresh "f")
in (_122_684, FStar_ToSMT_Term.Term_sort))
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
(let _122_685 = (FStar_ToSMT_Term.mk_and_l guards)
in (_122_685, decls))
end
| Some (pre) -> begin
(let _53_836 = (encode_formula pre env')
in (match (_53_836) with
| (guard, decls0) -> begin
(let _122_686 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_122_686, (FStar_List.append decls decls0)))
end))
end)
in (match (_53_839) with
| (guards, guard_decls) -> begin
(let t_interp = (let _122_688 = (let _122_687 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _122_687))
in (FStar_ToSMT_Term.mkForall _122_688))
in (let cvars = (let _122_690 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _122_690 (FStar_List.filter (fun _53_844 -> (match (_53_844) with
| (x, _53_843) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _53_850) -> begin
(let _122_693 = (let _122_692 = (let _122_691 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _122_691))
in (FStar_ToSMT_Term.mkApp _122_692))
in (_122_693, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _122_694 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_122_694))
end
| false -> begin
None
end)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _122_696 = (let _122_695 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _122_695))
in (FStar_ToSMT_Term.mkApp _122_696))
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _122_698 = (let _122_697 = (FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_122_697, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_122_698))
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _122_705 = (let _122_704 = (let _122_703 = (let _122_702 = (let _122_701 = (let _122_700 = (let _122_699 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _122_699))
in (f_has_t, _122_700))
in (FStar_ToSMT_Term.mkImp _122_701))
in ((f_has_t)::[], (fsym)::cvars, _122_702))
in (mkForall_fuel _122_703))
in (_122_704, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_122_705))
in (let t_interp = (let _122_709 = (let _122_708 = (let _122_707 = (let _122_706 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in ((f_has_t_z)::[], (fsym)::cvars, _122_706))
in (FStar_ToSMT_Term.mkForall _122_707))
in (_122_708, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_122_709))
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
in (let t_kinding = (let _122_711 = (let _122_710 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_122_710, None))
in FStar_ToSMT_Term.Assume (_122_711))
in (let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _122_718 = (let _122_717 = (let _122_716 = (let _122_715 = (let _122_714 = (let _122_713 = (let _122_712 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _122_712))
in (f_has_t, _122_713))
in (FStar_ToSMT_Term.mkImp _122_714))
in ((f_has_t)::[], (fsym)::[], _122_715))
in (mkForall_fuel _122_716))
in (_122_717, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_122_718))
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
(let encoding = (let _122_720 = (let _122_719 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_122_719, refinement))
in (FStar_ToSMT_Term.mkAnd _122_720))
in (let cvars = (let _122_722 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _122_722 (FStar_List.filter (fun _53_914 -> (match (_53_914) with
| (y, _53_913) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_921, _53_923) -> begin
(let _122_725 = (let _122_724 = (let _122_723 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _122_723))
in (FStar_ToSMT_Term.mkApp _122_724))
in (_122_725, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _122_727 = (let _122_726 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _122_726))
in (FStar_ToSMT_Term.mkApp _122_727))
in (let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _122_729 = (let _122_728 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (ffv)::(xfv)::cvars, _122_728))
in (FStar_ToSMT_Term.mkForall _122_729))
in (let t_decls = (let _122_736 = (let _122_735 = (let _122_734 = (let _122_733 = (let _122_732 = (let _122_731 = (let _122_730 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_122_730))
in (assumption, _122_731))
in FStar_ToSMT_Term.Assume (_122_732))
in (_122_733)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_122_734)
in (tdecl)::_122_735)
in (FStar_List.append (FStar_List.append decls decls') _122_736))
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
(let ttm = (let _122_737 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _122_737))
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
in (let t = (let _122_742 = (let _122_741 = (FStar_List.map (fun _53_10 -> (match (_53_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _122_741))
in (FStar_ToSMT_Term.mkApp _122_742))
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
(let ttm = (let _122_743 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _122_743))
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
(let key_body = (let _122_747 = (let _122_746 = (let _122_745 = (let _122_744 = (FStar_ToSMT_Term.mk_and_l guards)
in (_122_744, body))
in (FStar_ToSMT_Term.mkImp _122_745))
in ([], vars, _122_746))
in (FStar_ToSMT_Term.mkForall _122_747))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1010, _53_1012) -> begin
(let _122_750 = (let _122_749 = (let _122_748 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _122_748))
in (FStar_ToSMT_Term.mkApp _122_749))
in (_122_750, []))
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
in (let t = (let _122_752 = (let _122_751 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _122_751))
in (FStar_ToSMT_Term.mkApp _122_752))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _122_759 = (let _122_758 = (let _122_757 = (let _122_756 = (let _122_755 = (let _122_754 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _122_753 = (FStar_ToSMT_Term.mkEq (app, body))
in (_122_754, _122_753)))
in (FStar_ToSMT_Term.mkImp _122_755))
in ((app)::[], (FStar_List.append vars cvars), _122_756))
in (FStar_ToSMT_Term.mkForall _122_757))
in (_122_758, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_122_759))
in (let kinding = (let _53_1027 = (let _122_760 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _122_760 env t))
in (match (_53_1027) with
| (ktm, decls'') -> begin
(let _122_764 = (let _122_763 = (let _122_762 = (let _122_761 = (FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_122_761, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_122_762))
in (_122_763)::[])
in (FStar_List.append decls'' _122_764))
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
(let _122_765 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _122_765 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _122_770 = (let _122_769 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _122_768 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _122_767 = (FStar_Absyn_Print.typ_to_string t0)
in (let _122_766 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _122_769 _122_768 _122_767 _122_766)))))
in (FStar_All.failwith _122_770))
end)))
and encode_exp = (fun e env -> (let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_53_1049) -> begin
(let _122_773 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _122_773 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _53_1056) -> begin
(let _122_774 = (lookup_free_var env v)
in (_122_774, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _122_775 = (encode_const c)
in (_122_775, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _53_1064) -> begin
(let _53_1067 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _53_1071)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _53_1077) -> begin
(let e = (let _122_776 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _122_776))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fallback = (fun _53_1086 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _122_779 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_122_779, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _53_1090 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _122_780 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _122_780))) with
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
in (let e = (let _122_782 = (let _122_781 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _122_781))
in (FStar_Absyn_Syntax.mk_Exp_abs _122_782 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
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
(let key_body = (let _122_786 = (let _122_785 = (let _122_784 = (let _122_783 = (FStar_ToSMT_Term.mk_and_l guards)
in (_122_783, body))
in (FStar_ToSMT_Term.mkImp _122_784))
in ([], vars, _122_785))
in (FStar_ToSMT_Term.mkForall _122_786))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1124, _53_1126) -> begin
(let _122_789 = (let _122_788 = (let _122_787 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _122_787))
in (FStar_ToSMT_Term.mkApp _122_788))
in (_122_789, []))
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
in (let f = (let _122_791 = (let _122_790 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _122_790))
in (FStar_ToSMT_Term.mkApp _122_791))
in (let app = (mk_ApplyE f vars)
in (let _53_1140 = (encode_typ_pred None tfun env f)
in (match (_53_1140) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _122_793 = (let _122_792 = (FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_122_792, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_122_793))
in (let interp_f = (let _122_800 = (let _122_799 = (let _122_798 = (let _122_797 = (let _122_796 = (let _122_795 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _122_794 = (FStar_ToSMT_Term.mkEq (app, body))
in (_122_795, _122_794)))
in (FStar_ToSMT_Term.mkImp _122_796))
in ((app)::[], (FStar_List.append vars cvars), _122_797))
in (FStar_ToSMT_Term.mkForall _122_798))
in (_122_799, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_122_800))
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
(let _122_801 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_122_801, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_53_1196); FStar_Absyn_Syntax.tk = _53_1194; FStar_Absyn_Syntax.pos = _53_1192; FStar_Absyn_Syntax.fvs = _53_1190; FStar_Absyn_Syntax.uvs = _53_1188}, _53_1200) -> begin
(let _122_802 = (whnf_e env e)
in (encode_exp _122_802 env))
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
in (let ty = (let _122_805 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _122_805 (FStar_Absyn_Util.subst_typ subst)))
in (let _53_1228 = (encode_typ_pred None ty env app_tm)
in (match (_53_1228) with
| (has_type, decls'') -> begin
(let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _122_807 = (let _122_806 = (FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_122_806, None))
in FStar_ToSMT_Term.Assume (_122_807))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _53_1235 = (lookup_free_var_sym env fv)
in (match (_53_1235) with
| (fname, fuel_args) -> begin
(let tm = (let _122_813 = (let _122_812 = (let _122_811 = (FStar_List.map (fun _53_11 -> (match (_53_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _122_811))
in (fname, _122_812))
in (FStar_ToSMT_Term.mkApp' _122_813))
in (tm, decls))
end)))
in (let head = (FStar_Absyn_Util.compress_exp head)
in (let _53_1242 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186")))) with
| true -> begin
(let _122_815 = (FStar_Absyn_Print.exp_to_string head)
in (let _122_814 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _122_815 _122_814)))
end
| false -> begin
()
end)
in (let head_type = (let _122_818 = (let _122_817 = (let _122_816 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _122_816))
in (whnf env _122_817))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _122_818))
in (let _53_1245 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _122_821 = (FStar_Absyn_Print.exp_to_string head)
in (let _122_820 = (FStar_Absyn_Print.tag_of_exp head)
in (let _122_819 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _122_821 _122_820 _122_819))))
end
| false -> begin
()
end)
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _122_825 = (let _122_824 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _122_823 = (FStar_Absyn_Print.exp_to_string e0)
in (let _122_822 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _122_824 _122_823 _122_822))))
in (FStar_All.failwith _122_825))
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
in (let _122_826 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_122_826, (decl_e)::[])))))
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
(let _122_837 = (let _122_836 = (let _122_835 = (let _122_834 = (let _122_833 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _122_833))
in (FStar_ToSMT_Term.mkEq _122_834))
in (guard, _122_835))
in (FStar_ToSMT_Term.mkAnd _122_836))
in (_122_837, decls2))
end))
end)
in (match (_53_1343) with
| (guard, decls2) -> begin
(let _53_1346 = (encode_exp br env)
in (match (_53_1346) with
| (br, decls3) -> begin
(let _122_838 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_122_838, (FStar_List.append (FStar_List.append decls decls2) decls3)))
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
(let _122_841 = (let _122_840 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _122_839 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _122_840 _122_839)))
in (FStar_All.failwith _122_841))
end))))
and encode_pat = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _53_1358 -> begin
(let _122_844 = (encode_one_pat env pat)
in (_122_844)::[])
end))
and encode_one_pat = (fun env pat -> (let _53_1361 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _122_847 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.fprint1 "Encoding pattern %s\n" _122_847))
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
(let _122_855 = (let _122_854 = (encode_const c)
in (scrutinee, _122_854))
in (FStar_ToSMT_Term.mkEq _122_855))
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1415, args) -> begin
(let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1424 -> (match (_53_1424) with
| (arg, _53_1423) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _122_858 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _122_858)))
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
(let _122_866 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1460 -> (match (_53_1460) with
| (arg, _53_1459) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _122_865 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _122_865)))
end))))
in (FStar_All.pipe_right _122_866 FStar_List.flatten))
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
and encode_function_type_as_formula = (fun induction_on new_pats t env -> (let v_or_t_pat = (fun p -> (match ((let _122_881 = (FStar_Absyn_Util.unmeta_exp p)
in _122_881.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (_53_1510, (FStar_Util.Inl (_53_1517), _53_1520)::(FStar_Util.Inr (e), _53_1514)::[]) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app (_53_1526, (FStar_Util.Inl (t), _53_1530)::[]) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _53_1536 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun p -> (match ((let _122_884 = (FStar_Absyn_Util.unmeta_exp p)
in _122_884.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (_53_1540, _53_1552::(FStar_Util.Inr (hd), _53_1549)::(FStar_Util.Inr (tl), _53_1544)::[]) -> begin
(let _122_886 = (v_or_t_pat hd)
in (let _122_885 = (lemma_pats tl)
in (_122_886)::_122_885))
end
| _53_1557 -> begin
[]
end))
in (let _53_1600 = (match ((let _122_887 = (FStar_Absyn_Util.compress_typ t)
in _122_887.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _53_1566; FStar_Absyn_Syntax.pos = _53_1564; FStar_Absyn_Syntax.fvs = _53_1562; FStar_Absyn_Syntax.uvs = _53_1560}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _53_1585)::(FStar_Util.Inl (post), _53_1580)::(FStar_Util.Inr (pats), _53_1575)::[] -> begin
(let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _122_888 = (lemma_pats pats')
in (binders, pre, post, _122_888)))
end
| _53_1593 -> begin
(FStar_All.failwith "impos")
end)
end
| _53_1595 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_53_1600) with
| (binders, pre, post, patterns) -> begin
(let _53_1607 = (encode_binders None binders env)
in (match (_53_1607) with
| (vars, guards, env, decls, _53_1606) -> begin
(let _53_1623 = (let _122_890 = (FStar_All.pipe_right patterns (FStar_List.map (fun _53_12 -> (match (_53_12) with
| (FStar_Util.Inl (t), _53_1612) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _53_1617) -> begin
(encode_exp e (let _53_1619 = env
in {bindings = _53_1619.bindings; depth = _53_1619.depth; tcenv = _53_1619.tcenv; warn = _53_1619.warn; cache = _53_1619.cache; nolabels = _53_1619.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1619.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _122_890 FStar_List.unzip))
in (match (_53_1623) with
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
(let _122_892 = (let _122_891 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _122_891 e))
in (_122_892)::pats)
end
| _53_1631 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(let _122_897 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_122_897)::pats)
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _122_899 = (let _122_898 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _122_898 tl))
in (aux _122_899 vars))
end
| _53_1642 -> begin
pats
end))
in (let _122_900 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _122_900 vars)))
end)
end)
in (let env = (let _53_1644 = env
in {bindings = _53_1644.bindings; depth = _53_1644.depth; tcenv = _53_1644.tcenv; warn = _53_1644.warn; cache = _53_1644.cache; nolabels = true; use_zfuel_name = _53_1644.use_zfuel_name; encode_non_total_function_typ = _53_1644.encode_non_total_function_typ})
in (let _53_1649 = (let _122_901 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _122_901 env))
in (match (_53_1649) with
| (pre, decls'') -> begin
(let _53_1652 = (let _122_902 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _122_902 env))
in (match (_53_1652) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _122_907 = (let _122_906 = (let _122_905 = (let _122_904 = (let _122_903 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_122_903, post))
in (FStar_ToSMT_Term.mkImp _122_904))
in (pats, vars, _122_905))
in (FStar_ToSMT_Term.mkForall _122_906))
in (_122_907, decls)))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun phi env -> (let enc = (fun f -> (fun l -> (let _53_1673 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(let _53_1665 = (encode_typ_term t env)
in (match (_53_1665) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(let _53_1670 = (encode_exp e env)
in (match (_53_1670) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_53_1673) with
| (decls, args) -> begin
(let _122_925 = (f args)
in (_122_925, [], decls))
end))))
in (let enc_prop_c = (fun f -> (fun l -> (let _53_1693 = (FStar_List.fold_right (fun t _53_1681 -> (match (_53_1681) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(let _53_1687 = (encode_formula_with_labels t env)
in (match (_53_1687) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _53_1689 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_53_1693) with
| (phis, labs, decls) -> begin
(let _122_941 = (f phis)
in (_122_941, labs, decls))
end))))
in (let const_op = (fun f _53_1696 -> (f, [], []))
in (let un_op = (fun f l -> (let _122_955 = (FStar_List.hd l)
in (FStar_All.pipe_left f _122_955)))
in (let bin_op = (fun f _53_13 -> (match (_53_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _53_1707 -> begin
(FStar_All.failwith "Impossible")
end))
in (let eq_op = (fun _53_14 -> (match (_53_14) with
| _53_1715::_53_1713::e1::e2::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _53_15 -> (match (_53_15) with
| (FStar_Util.Inl (lhs), _53_1728)::(FStar_Util.Inl (rhs), _53_1723)::[] -> begin
(let _53_1734 = (encode_formula_with_labels rhs env)
in (match (_53_1734) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_1737) -> begin
(l1, labs1, decls1)
end
| _53_1741 -> begin
(let _53_1745 = (encode_formula_with_labels lhs env)
in (match (_53_1745) with
| (l2, labs2, decls2) -> begin
(let _122_969 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_122_969, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _53_1747 -> begin
(FStar_All.failwith "impossible")
end))
in (let mk_ite = (fun _53_16 -> (match (_53_16) with
| (FStar_Util.Inl (guard), _53_1763)::(FStar_Util.Inl (_then), _53_1758)::(FStar_Util.Inl (_else), _53_1753)::[] -> begin
(let _53_1769 = (encode_formula_with_labels guard env)
in (match (_53_1769) with
| (g, labs1, decls1) -> begin
(let _53_1773 = (encode_formula_with_labels _then env)
in (match (_53_1773) with
| (t, labs2, decls2) -> begin
(let _53_1777 = (encode_formula_with_labels _else env)
in (match (_53_1777) with
| (e, labs3, decls3) -> begin
(let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _53_1780 -> begin
(FStar_All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _122_981 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _122_981)))
in (let connectives = (let _122_1042 = (let _122_990 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _122_990))
in (let _122_1041 = (let _122_1040 = (let _122_996 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _122_996))
in (let _122_1039 = (let _122_1038 = (let _122_1037 = (let _122_1005 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _122_1005))
in (let _122_1036 = (let _122_1035 = (let _122_1034 = (let _122_1014 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _122_1014))
in (let _122_1033 = (let _122_1032 = (let _122_1020 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _122_1020))
in (_122_1032)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_122_1034)::_122_1033))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_122_1035)
in (_122_1037)::_122_1036))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_122_1038)
in (_122_1040)::_122_1039))
in (_122_1042)::_122_1041))
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(let _53_1798 = (encode_formula_with_labels phi' env)
in (match (_53_1798) with
| (phi, labs, decls) -> begin
(match (env.nolabels) with
| true -> begin
(phi, [], decls)
end
| false -> begin
(let lvar = (let _122_1045 = (varops.fresh "label")
in (_122_1045, FStar_ToSMT_Term.Bool_sort))
in (let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end)
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1809; FStar_Absyn_Syntax.pos = _53_1807; FStar_Absyn_Syntax.fvs = _53_1805; FStar_Absyn_Syntax.uvs = _53_1803}, _53_1824::(FStar_Util.Inr (l), _53_1821)::(FStar_Util.Inl (phi), _53_1816)::[]) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
(match ((FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let _53_1830 = (encode_exp l env)
in (match (_53_1830) with
| (e, decls) -> begin
(let _53_1833 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_53_1833) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end
| false -> begin
(FStar_ToSMT_Term.mkTrue, [], [])
end)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1841; FStar_Absyn_Syntax.pos = _53_1839; FStar_Absyn_Syntax.fvs = _53_1837; FStar_Absyn_Syntax.uvs = _53_1835}, _53_1853::(FStar_Util.Inl (phi), _53_1849)::tl) when (FStar_Absyn_Syntax.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
(match ((FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let pat = (match (tl) with
| [] -> begin
None
end
| (FStar_Util.Inr (pat), _53_1861)::[] -> begin
Some (pat)
end)
in (let _53_1867 = (encode_function_type_as_formula None pat phi env)
in (match (_53_1867) with
| (f, decls) -> begin
(f, [], decls)
end)))
end
| false -> begin
(FStar_ToSMT_Term.mkTrue, [], [])
end)
end
| _53_1869 -> begin
(let _53_1872 = (encode_typ_term phi env)
in (match (_53_1872) with
| (tt, decls) -> begin
(let _122_1046 = (FStar_ToSMT_Term.mk_Valid tt)
in (_122_1046, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _53_1884 = (encode_binders None bs env)
in (match (_53_1884) with
| (vars, guards, env, decls, _53_1883) -> begin
(let _53_1900 = (let _122_1056 = (FStar_All.pipe_right ps (FStar_List.map (fun _53_17 -> (match (_53_17) with
| (FStar_Util.Inl (t), _53_1889) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _53_1894) -> begin
(encode_exp e (let _53_1896 = env
in {bindings = _53_1896.bindings; depth = _53_1896.depth; tcenv = _53_1896.tcenv; warn = _53_1896.warn; cache = _53_1896.cache; nolabels = _53_1896.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1896.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _122_1056 FStar_List.unzip))
in (match (_53_1900) with
| (pats, decls') -> begin
(let _53_1904 = (encode_formula_with_labels body env)
in (match (_53_1904) with
| (body, labs, decls'') -> begin
(let _122_1057 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _122_1057, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _53_1905 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _122_1058 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.fprint1 ">>>> Destructing as formula ... %s\n" _122_1058))
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
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _53_1917 -> (match (_53_1917) with
| (l, _53_1916) -> begin
(FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_53_1920, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(let _53_1930 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _122_1075 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.fprint1 ">>>> Got QALL [%s]\n" _122_1075))
end
| false -> begin
()
end)
in (let _53_1938 = (encode_q_body env vars pats body)
in (match (_53_1938) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _122_1078 = (let _122_1077 = (let _122_1076 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _122_1076))
in (FStar_ToSMT_Term.mkForall _122_1077))
in (_122_1078, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(let _53_1951 = (encode_q_body env vars pats body)
in (match (_53_1951) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _122_1081 = (let _122_1080 = (let _122_1079 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _122_1079))
in (FStar_ToSMT_Term.mkExists _122_1080))
in (_122_1081, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : FStar_Absyn_Syntax.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Absyn_Syntax.lident  ->  Prims.bool}

let is_Mkprims_t = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))

let prims = (let _53_1957 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_53_1957) with
| (asym, a) -> begin
(let _53_1960 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_1960) with
| (xsym, x) -> begin
(let _53_1963 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_53_1963) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (FStar_ToSMT_Term.DefineFun ((x, vars, FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body -> (fun x -> (let t1 = (let _122_1124 = (let _122_1123 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _122_1123))
in (FStar_ToSMT_Term.mkApp _122_1124))
in (let vname_decl = (let _122_1126 = (let _122_1125 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _122_1125, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_122_1126))
in (let _122_1132 = (let _122_1131 = (let _122_1130 = (let _122_1129 = (let _122_1128 = (let _122_1127 = (FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _122_1127))
in (FStar_ToSMT_Term.mkForall _122_1128))
in (_122_1129, None))
in FStar_ToSMT_Term.Assume (_122_1130))
in (_122_1131)::[])
in (vname_decl)::_122_1132)))))
in (let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _122_1292 = (let _122_1141 = (let _122_1140 = (let _122_1139 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1139))
in (quant axy _122_1140))
in (FStar_Absyn_Const.op_Eq, _122_1141))
in (let _122_1291 = (let _122_1290 = (let _122_1148 = (let _122_1147 = (let _122_1146 = (let _122_1145 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _122_1145))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1146))
in (quant axy _122_1147))
in (FStar_Absyn_Const.op_notEq, _122_1148))
in (let _122_1289 = (let _122_1288 = (let _122_1157 = (let _122_1156 = (let _122_1155 = (let _122_1154 = (let _122_1153 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1152 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1153, _122_1152)))
in (FStar_ToSMT_Term.mkLT _122_1154))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1155))
in (quant xy _122_1156))
in (FStar_Absyn_Const.op_LT, _122_1157))
in (let _122_1287 = (let _122_1286 = (let _122_1166 = (let _122_1165 = (let _122_1164 = (let _122_1163 = (let _122_1162 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1161 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1162, _122_1161)))
in (FStar_ToSMT_Term.mkLTE _122_1163))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1164))
in (quant xy _122_1165))
in (FStar_Absyn_Const.op_LTE, _122_1166))
in (let _122_1285 = (let _122_1284 = (let _122_1175 = (let _122_1174 = (let _122_1173 = (let _122_1172 = (let _122_1171 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1170 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1171, _122_1170)))
in (FStar_ToSMT_Term.mkGT _122_1172))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1173))
in (quant xy _122_1174))
in (FStar_Absyn_Const.op_GT, _122_1175))
in (let _122_1283 = (let _122_1282 = (let _122_1184 = (let _122_1183 = (let _122_1182 = (let _122_1181 = (let _122_1180 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1179 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1180, _122_1179)))
in (FStar_ToSMT_Term.mkGTE _122_1181))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1182))
in (quant xy _122_1183))
in (FStar_Absyn_Const.op_GTE, _122_1184))
in (let _122_1281 = (let _122_1280 = (let _122_1193 = (let _122_1192 = (let _122_1191 = (let _122_1190 = (let _122_1189 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1188 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1189, _122_1188)))
in (FStar_ToSMT_Term.mkSub _122_1190))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _122_1191))
in (quant xy _122_1192))
in (FStar_Absyn_Const.op_Subtraction, _122_1193))
in (let _122_1279 = (let _122_1278 = (let _122_1200 = (let _122_1199 = (let _122_1198 = (let _122_1197 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _122_1197))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _122_1198))
in (quant qx _122_1199))
in (FStar_Absyn_Const.op_Minus, _122_1200))
in (let _122_1277 = (let _122_1276 = (let _122_1209 = (let _122_1208 = (let _122_1207 = (let _122_1206 = (let _122_1205 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1204 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1205, _122_1204)))
in (FStar_ToSMT_Term.mkAdd _122_1206))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _122_1207))
in (quant xy _122_1208))
in (FStar_Absyn_Const.op_Addition, _122_1209))
in (let _122_1275 = (let _122_1274 = (let _122_1218 = (let _122_1217 = (let _122_1216 = (let _122_1215 = (let _122_1214 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1213 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1214, _122_1213)))
in (FStar_ToSMT_Term.mkMul _122_1215))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _122_1216))
in (quant xy _122_1217))
in (FStar_Absyn_Const.op_Multiply, _122_1218))
in (let _122_1273 = (let _122_1272 = (let _122_1227 = (let _122_1226 = (let _122_1225 = (let _122_1224 = (let _122_1223 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1222 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1223, _122_1222)))
in (FStar_ToSMT_Term.mkDiv _122_1224))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _122_1225))
in (quant xy _122_1226))
in (FStar_Absyn_Const.op_Division, _122_1227))
in (let _122_1271 = (let _122_1270 = (let _122_1236 = (let _122_1235 = (let _122_1234 = (let _122_1233 = (let _122_1232 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1231 = (FStar_ToSMT_Term.unboxInt y)
in (_122_1232, _122_1231)))
in (FStar_ToSMT_Term.mkMod _122_1233))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _122_1234))
in (quant xy _122_1235))
in (FStar_Absyn_Const.op_Modulus, _122_1236))
in (let _122_1269 = (let _122_1268 = (let _122_1245 = (let _122_1244 = (let _122_1243 = (let _122_1242 = (let _122_1241 = (FStar_ToSMT_Term.unboxBool x)
in (let _122_1240 = (FStar_ToSMT_Term.unboxBool y)
in (_122_1241, _122_1240)))
in (FStar_ToSMT_Term.mkAnd _122_1242))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1243))
in (quant xy _122_1244))
in (FStar_Absyn_Const.op_And, _122_1245))
in (let _122_1267 = (let _122_1266 = (let _122_1254 = (let _122_1253 = (let _122_1252 = (let _122_1251 = (let _122_1250 = (FStar_ToSMT_Term.unboxBool x)
in (let _122_1249 = (FStar_ToSMT_Term.unboxBool y)
in (_122_1250, _122_1249)))
in (FStar_ToSMT_Term.mkOr _122_1251))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1252))
in (quant xy _122_1253))
in (FStar_Absyn_Const.op_Or, _122_1254))
in (let _122_1265 = (let _122_1264 = (let _122_1261 = (let _122_1260 = (let _122_1259 = (let _122_1258 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _122_1258))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_1259))
in (quant qx _122_1260))
in (FStar_Absyn_Const.op_Negation, _122_1261))
in (_122_1264)::[])
in (_122_1266)::_122_1265))
in (_122_1268)::_122_1267))
in (_122_1270)::_122_1269))
in (_122_1272)::_122_1271))
in (_122_1274)::_122_1273))
in (_122_1276)::_122_1275))
in (_122_1278)::_122_1277))
in (_122_1280)::_122_1279))
in (_122_1282)::_122_1281))
in (_122_1284)::_122_1283))
in (_122_1286)::_122_1285))
in (_122_1288)::_122_1287))
in (_122_1290)::_122_1289))
in (_122_1292)::_122_1291))
in (let mk = (fun l v -> (let _122_1324 = (FStar_All.pipe_right prims (FStar_List.filter (fun _53_1983 -> (match (_53_1983) with
| (l', _53_1982) -> begin
(FStar_Absyn_Syntax.lid_equals l l')
end))))
in (FStar_All.pipe_right _122_1324 (FStar_List.collect (fun _53_1987 -> (match (_53_1987) with
| (_53_1985, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _53_1993 -> (match (_53_1993) with
| (l', _53_1992) -> begin
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
in (let mk_unit = (fun _53_1999 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _122_1356 = (let _122_1347 = (let _122_1346 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_122_1346, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_122_1347))
in (let _122_1355 = (let _122_1354 = (let _122_1353 = (let _122_1352 = (let _122_1351 = (let _122_1350 = (let _122_1349 = (let _122_1348 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _122_1348))
in (FStar_ToSMT_Term.mkImp _122_1349))
in ((typing_pred)::[], (xx)::[], _122_1350))
in (mkForall_fuel _122_1351))
in (_122_1352, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_122_1353))
in (_122_1354)::[])
in (_122_1356)::_122_1355))))
in (let mk_bool = (fun _53_2004 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _122_1376 = (let _122_1366 = (let _122_1365 = (let _122_1364 = (let _122_1363 = (let _122_1362 = (let _122_1361 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _122_1361))
in (FStar_ToSMT_Term.mkImp _122_1362))
in ((typing_pred)::[], (xx)::[], _122_1363))
in (mkForall_fuel _122_1364))
in (_122_1365, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_122_1366))
in (let _122_1375 = (let _122_1374 = (let _122_1373 = (let _122_1372 = (let _122_1371 = (let _122_1370 = (let _122_1367 = (FStar_ToSMT_Term.boxBool b)
in (_122_1367)::[])
in (let _122_1369 = (let _122_1368 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _122_1368 tt))
in (_122_1370, (bb)::[], _122_1369)))
in (FStar_ToSMT_Term.mkForall _122_1371))
in (_122_1372, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_122_1373))
in (_122_1374)::[])
in (_122_1376)::_122_1375))))))
in (let mk_int = (fun _53_2011 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _122_1388 = (let _122_1387 = (let _122_1386 = (let _122_1385 = (let _122_1384 = (let _122_1383 = (FStar_ToSMT_Term.boxInt a)
in (let _122_1382 = (let _122_1381 = (FStar_ToSMT_Term.boxInt b)
in (_122_1381)::[])
in (_122_1383)::_122_1382))
in (tt)::_122_1384)
in (tt)::_122_1385)
in ("Prims.Precedes", _122_1386))
in (FStar_ToSMT_Term.mkApp _122_1387))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _122_1388))
in (let precedes_y_x = (let _122_1389 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _122_1389))
in (let _122_1430 = (let _122_1395 = (let _122_1394 = (let _122_1393 = (let _122_1392 = (let _122_1391 = (let _122_1390 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _122_1390))
in (FStar_ToSMT_Term.mkImp _122_1391))
in ((typing_pred)::[], (xx)::[], _122_1392))
in (mkForall_fuel _122_1393))
in (_122_1394, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_122_1395))
in (let _122_1429 = (let _122_1428 = (let _122_1402 = (let _122_1401 = (let _122_1400 = (let _122_1399 = (let _122_1396 = (FStar_ToSMT_Term.boxInt b)
in (_122_1396)::[])
in (let _122_1398 = (let _122_1397 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _122_1397 tt))
in (_122_1399, (bb)::[], _122_1398)))
in (FStar_ToSMT_Term.mkForall _122_1400))
in (_122_1401, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_122_1402))
in (let _122_1427 = (let _122_1426 = (let _122_1425 = (let _122_1424 = (let _122_1423 = (let _122_1422 = (let _122_1421 = (let _122_1420 = (let _122_1419 = (let _122_1418 = (let _122_1417 = (let _122_1416 = (let _122_1405 = (let _122_1404 = (FStar_ToSMT_Term.unboxInt x)
in (let _122_1403 = (FStar_ToSMT_Term.mkInteger' 0)
in (_122_1404, _122_1403)))
in (FStar_ToSMT_Term.mkGT _122_1405))
in (let _122_1415 = (let _122_1414 = (let _122_1408 = (let _122_1407 = (FStar_ToSMT_Term.unboxInt y)
in (let _122_1406 = (FStar_ToSMT_Term.mkInteger' 0)
in (_122_1407, _122_1406)))
in (FStar_ToSMT_Term.mkGTE _122_1408))
in (let _122_1413 = (let _122_1412 = (let _122_1411 = (let _122_1410 = (FStar_ToSMT_Term.unboxInt y)
in (let _122_1409 = (FStar_ToSMT_Term.unboxInt x)
in (_122_1410, _122_1409)))
in (FStar_ToSMT_Term.mkLT _122_1411))
in (_122_1412)::[])
in (_122_1414)::_122_1413))
in (_122_1416)::_122_1415))
in (typing_pred_y)::_122_1417)
in (typing_pred)::_122_1418)
in (FStar_ToSMT_Term.mk_and_l _122_1419))
in (_122_1420, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _122_1421))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _122_1422))
in (mkForall_fuel _122_1423))
in (_122_1424, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_122_1425))
in (_122_1426)::[])
in (_122_1428)::_122_1427))
in (_122_1430)::_122_1429)))))))))))
in (let mk_int_alias = (fun _53_2023 tt -> (let _122_1439 = (let _122_1438 = (let _122_1437 = (let _122_1436 = (let _122_1435 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Absyn_Syntax.str, []))
in (tt, _122_1435))
in (FStar_ToSMT_Term.mkEq _122_1436))
in (_122_1437, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_122_1438))
in (_122_1439)::[]))
in (let mk_str = (fun _53_2027 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.String_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _122_1459 = (let _122_1449 = (let _122_1448 = (let _122_1447 = (let _122_1446 = (let _122_1445 = (let _122_1444 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _122_1444))
in (FStar_ToSMT_Term.mkImp _122_1445))
in ((typing_pred)::[], (xx)::[], _122_1446))
in (mkForall_fuel _122_1447))
in (_122_1448, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_122_1449))
in (let _122_1458 = (let _122_1457 = (let _122_1456 = (let _122_1455 = (let _122_1454 = (let _122_1453 = (let _122_1450 = (FStar_ToSMT_Term.boxString b)
in (_122_1450)::[])
in (let _122_1452 = (let _122_1451 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _122_1451 tt))
in (_122_1453, (bb)::[], _122_1452)))
in (FStar_ToSMT_Term.mkForall _122_1454))
in (_122_1455, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_122_1456))
in (_122_1457)::[])
in (_122_1459)::_122_1458))))))
in (let mk_ref = (fun reft_name _53_2035 -> (let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let refa = (let _122_1466 = (let _122_1465 = (let _122_1464 = (FStar_ToSMT_Term.mkFreeV aa)
in (_122_1464)::[])
in (reft_name, _122_1465))
in (FStar_ToSMT_Term.mkApp _122_1466))
in (let refb = (let _122_1469 = (let _122_1468 = (let _122_1467 = (FStar_ToSMT_Term.mkFreeV bb)
in (_122_1467)::[])
in (reft_name, _122_1468))
in (FStar_ToSMT_Term.mkApp _122_1469))
in (let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _122_1488 = (let _122_1475 = (let _122_1474 = (let _122_1473 = (let _122_1472 = (let _122_1471 = (let _122_1470 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _122_1470))
in (FStar_ToSMT_Term.mkImp _122_1471))
in ((typing_pred)::[], (xx)::(aa)::[], _122_1472))
in (mkForall_fuel _122_1473))
in (_122_1474, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_122_1475))
in (let _122_1487 = (let _122_1486 = (let _122_1485 = (let _122_1484 = (let _122_1483 = (let _122_1482 = (let _122_1481 = (let _122_1480 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _122_1479 = (let _122_1478 = (let _122_1477 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _122_1476 = (FStar_ToSMT_Term.mkFreeV bb)
in (_122_1477, _122_1476)))
in (FStar_ToSMT_Term.mkEq _122_1478))
in (_122_1480, _122_1479)))
in (FStar_ToSMT_Term.mkImp _122_1481))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _122_1482))
in (mkForall_fuel' 2 _122_1483))
in (_122_1484, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_122_1485))
in (_122_1486)::[])
in (_122_1488)::_122_1487))))))))))
in (let mk_false_interp = (fun _53_2045 false_tm -> (let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _122_1495 = (let _122_1494 = (let _122_1493 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_122_1493, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_122_1494))
in (_122_1495)::[])))
in (let mk_and_interp = (fun conj _53_2051 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _122_1502 = (let _122_1501 = (let _122_1500 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_122_1500)::[])
in ("Valid", _122_1501))
in (FStar_ToSMT_Term.mkApp _122_1502))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _122_1509 = (let _122_1508 = (let _122_1507 = (let _122_1506 = (let _122_1505 = (let _122_1504 = (let _122_1503 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_122_1503, valid))
in (FStar_ToSMT_Term.mkIff _122_1504))
in ((valid)::[], (aa)::(bb)::[], _122_1505))
in (FStar_ToSMT_Term.mkForall _122_1506))
in (_122_1507, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_122_1508))
in (_122_1509)::[])))))))))
in (let mk_or_interp = (fun disj _53_2062 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _122_1516 = (let _122_1515 = (let _122_1514 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_122_1514)::[])
in ("Valid", _122_1515))
in (FStar_ToSMT_Term.mkApp _122_1516))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _122_1523 = (let _122_1522 = (let _122_1521 = (let _122_1520 = (let _122_1519 = (let _122_1518 = (let _122_1517 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_122_1517, valid))
in (FStar_ToSMT_Term.mkIff _122_1518))
in ((valid)::[], (aa)::(bb)::[], _122_1519))
in (FStar_ToSMT_Term.mkForall _122_1520))
in (_122_1521, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_122_1522))
in (_122_1523)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _122_1530 = (let _122_1529 = (let _122_1528 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_122_1528)::[])
in ("Valid", _122_1529))
in (FStar_ToSMT_Term.mkApp _122_1530))
in (let _122_1537 = (let _122_1536 = (let _122_1535 = (let _122_1534 = (let _122_1533 = (let _122_1532 = (let _122_1531 = (FStar_ToSMT_Term.mkEq (x, y))
in (_122_1531, valid))
in (FStar_ToSMT_Term.mkIff _122_1532))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _122_1533))
in (FStar_ToSMT_Term.mkForall _122_1534))
in (_122_1535, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_122_1536))
in (_122_1537)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _122_1544 = (let _122_1543 = (let _122_1542 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_122_1542)::[])
in ("Valid", _122_1543))
in (FStar_ToSMT_Term.mkApp _122_1544))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _122_1551 = (let _122_1550 = (let _122_1549 = (let _122_1548 = (let _122_1547 = (let _122_1546 = (let _122_1545 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_122_1545, valid))
in (FStar_ToSMT_Term.mkIff _122_1546))
in ((valid)::[], (aa)::(bb)::[], _122_1547))
in (FStar_ToSMT_Term.mkForall _122_1548))
in (_122_1549, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_122_1550))
in (_122_1551)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _122_1558 = (let _122_1557 = (let _122_1556 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_122_1556)::[])
in ("Valid", _122_1557))
in (FStar_ToSMT_Term.mkApp _122_1558))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _122_1565 = (let _122_1564 = (let _122_1563 = (let _122_1562 = (let _122_1561 = (let _122_1560 = (let _122_1559 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_122_1559, valid))
in (FStar_ToSMT_Term.mkIff _122_1560))
in ((valid)::[], (aa)::(bb)::[], _122_1561))
in (FStar_ToSMT_Term.mkForall _122_1562))
in (_122_1563, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_122_1564))
in (_122_1565)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _122_1572 = (let _122_1571 = (let _122_1570 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_122_1570)::[])
in ("Valid", _122_1571))
in (FStar_ToSMT_Term.mkApp _122_1572))
in (let valid_b_x = (let _122_1575 = (let _122_1574 = (let _122_1573 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_122_1573)::[])
in ("Valid", _122_1574))
in (FStar_ToSMT_Term.mkApp _122_1575))
in (let _122_1588 = (let _122_1587 = (let _122_1586 = (let _122_1585 = (let _122_1584 = (let _122_1583 = (let _122_1582 = (let _122_1581 = (let _122_1580 = (let _122_1576 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_122_1576)::[])
in (let _122_1579 = (let _122_1578 = (let _122_1577 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_122_1577, valid_b_x))
in (FStar_ToSMT_Term.mkImp _122_1578))
in (_122_1580, (xx)::[], _122_1579)))
in (FStar_ToSMT_Term.mkForall _122_1581))
in (_122_1582, valid))
in (FStar_ToSMT_Term.mkIff _122_1583))
in ((valid)::[], (aa)::(bb)::[], _122_1584))
in (FStar_ToSMT_Term.mkForall _122_1585))
in (_122_1586, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_122_1587))
in (_122_1588)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _122_1595 = (let _122_1594 = (let _122_1593 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_122_1593)::[])
in ("Valid", _122_1594))
in (FStar_ToSMT_Term.mkApp _122_1595))
in (let valid_b_x = (let _122_1598 = (let _122_1597 = (let _122_1596 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_122_1596)::[])
in ("Valid", _122_1597))
in (FStar_ToSMT_Term.mkApp _122_1598))
in (let _122_1611 = (let _122_1610 = (let _122_1609 = (let _122_1608 = (let _122_1607 = (let _122_1606 = (let _122_1605 = (let _122_1604 = (let _122_1603 = (let _122_1599 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_122_1599)::[])
in (let _122_1602 = (let _122_1601 = (let _122_1600 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_122_1600, valid_b_x))
in (FStar_ToSMT_Term.mkImp _122_1601))
in (_122_1603, (xx)::[], _122_1602)))
in (FStar_ToSMT_Term.mkExists _122_1604))
in (_122_1605, valid))
in (FStar_ToSMT_Term.mkIff _122_1606))
in ((valid)::[], (aa)::(bb)::[], _122_1607))
in (FStar_ToSMT_Term.mkForall _122_1608))
in (_122_1609, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_122_1610))
in (_122_1611)::[]))))))))))
in (let mk_foralltyp_interp = (fun for_all tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _122_1618 = (let _122_1617 = (let _122_1616 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_122_1616)::[])
in ("Valid", _122_1617))
in (FStar_ToSMT_Term.mkApp _122_1618))
in (let valid_a_b = (let _122_1621 = (let _122_1620 = (let _122_1619 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_122_1619)::[])
in ("Valid", _122_1620))
in (FStar_ToSMT_Term.mkApp _122_1621))
in (let _122_1634 = (let _122_1633 = (let _122_1632 = (let _122_1631 = (let _122_1630 = (let _122_1629 = (let _122_1628 = (let _122_1627 = (let _122_1626 = (let _122_1622 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_122_1622)::[])
in (let _122_1625 = (let _122_1624 = (let _122_1623 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_122_1623, valid_a_b))
in (FStar_ToSMT_Term.mkImp _122_1624))
in (_122_1626, (bb)::[], _122_1625)))
in (FStar_ToSMT_Term.mkForall _122_1627))
in (_122_1628, valid))
in (FStar_ToSMT_Term.mkIff _122_1629))
in ((valid)::[], (kk)::(aa)::[], _122_1630))
in (FStar_ToSMT_Term.mkForall _122_1631))
in (_122_1632, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_122_1633))
in (_122_1634)::[]))))))))))
in (let mk_existstyp_interp = (fun for_some tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _122_1641 = (let _122_1640 = (let _122_1639 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_122_1639)::[])
in ("Valid", _122_1640))
in (FStar_ToSMT_Term.mkApp _122_1641))
in (let valid_a_b = (let _122_1644 = (let _122_1643 = (let _122_1642 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_122_1642)::[])
in ("Valid", _122_1643))
in (FStar_ToSMT_Term.mkApp _122_1644))
in (let _122_1657 = (let _122_1656 = (let _122_1655 = (let _122_1654 = (let _122_1653 = (let _122_1652 = (let _122_1651 = (let _122_1650 = (let _122_1649 = (let _122_1645 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_122_1645)::[])
in (let _122_1648 = (let _122_1647 = (let _122_1646 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_122_1646, valid_a_b))
in (FStar_ToSMT_Term.mkImp _122_1647))
in (_122_1649, (bb)::[], _122_1648)))
in (FStar_ToSMT_Term.mkExists _122_1650))
in (_122_1651, valid))
in (FStar_ToSMT_Term.mkIff _122_1652))
in ((valid)::[], (kk)::(aa)::[], _122_1653))
in (FStar_ToSMT_Term.mkForall _122_1654))
in (_122_1655, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_122_1656))
in (_122_1657)::[]))))))))))
in (let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.char_lid, mk_int_alias))::((FStar_Absyn_Const.uint8_lid, mk_int_alias))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _53_2155 -> (match (_53_2155) with
| (l, _53_2154) -> begin
(FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_53_2158, f) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun env se -> (let _53_2164 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _122_1800 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.fprint1 ">>>>Encoding [%s]\n") _122_1800))
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
in (let _53_2172 = (encode_sigelt' env se)
in (match (_53_2172) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _122_1803 = (let _122_1802 = (let _122_1801 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_122_1801))
in (_122_1802)::[])
in (_122_1803, e))
end
| _53_2175 -> begin
(let _122_1810 = (let _122_1809 = (let _122_1805 = (let _122_1804 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_122_1804))
in (_122_1805)::g)
in (let _122_1808 = (let _122_1807 = (let _122_1806 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_122_1806))
in (_122_1807)::[])
in (FStar_List.append _122_1809 _122_1808)))
in (_122_1810, e))
end)
end)))))
and encode_sigelt' = (fun env se -> (let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Absyn_Syntax.str "Prims.all_")))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_53_2181, _53_2183, _53_2185, _53_2187, FStar_Absyn_Syntax.Effect::[], _53_2191) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2196, _53_2198, _53_2200, _53_2202, _53_2204) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2209, _53_2211, _53_2213, _53_2215, _53_2217) when (FStar_Absyn_Syntax.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(let _53_2223 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2223) with
| (tname, ttok, env) -> begin
(let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _122_1815 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (FStar_ToSMT_Term.mk_Valid _122_1815))
in (let decls = (let _122_1823 = (let _122_1822 = (let _122_1821 = (let _122_1820 = (let _122_1819 = (let _122_1818 = (let _122_1817 = (let _122_1816 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _122_1816))
in (FStar_ToSMT_Term.mkEq _122_1817))
in ((valid_b2t_x)::[], (xx)::[], _122_1818))
in (FStar_ToSMT_Term.mkForall _122_1819))
in (_122_1820, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_122_1821))
in (_122_1822)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_122_1823)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _53_2231, t, tags, _53_2235) -> begin
(let _53_2241 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2241) with
| (tname, ttok, env) -> begin
(let _53_2250 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _53_2247 -> begin
(tps, t)
end)
in (match (_53_2250) with
| (tps, t) -> begin
(let _53_2257 = (encode_binders None tps env)
in (match (_53_2257) with
| (vars, guards, env', binder_decls, _53_2256) -> begin
(let tok_app = (let _122_1824 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _122_1824 vars))
in (let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _122_1826 = (let _122_1825 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _122_1825))
in (FStar_ToSMT_Term.mkApp _122_1826))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _53_2263 -> begin
(let _122_1828 = (let _122_1827 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _122_1827))
in (_122_1828)::[])
end)
in (let decls = (let _122_1839 = (let _122_1832 = (let _122_1831 = (let _122_1830 = (let _122_1829 = (FStar_List.map Prims.snd vars)
in (tname, _122_1829, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_122_1830))
in (_122_1831)::(tok_decl)::[])
in (FStar_List.append _122_1832 fresh_tok))
in (let _122_1838 = (let _122_1837 = (let _122_1836 = (let _122_1835 = (let _122_1834 = (let _122_1833 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _122_1833))
in (FStar_ToSMT_Term.mkForall _122_1834))
in (_122_1835, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_122_1836))
in (_122_1837)::[])
in (FStar_List.append _122_1839 _122_1838)))
in (let t = (whnf env t)
in (let _53_2275 = (match ((FStar_All.pipe_right tags (FStar_Util.for_some (fun _53_18 -> (match (_53_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _53_2270 -> begin
false
end))))) with
| true -> begin
(let _122_1842 = (FStar_ToSMT_Term.mk_Valid app)
in (let _122_1841 = (encode_formula t env')
in (_122_1842, _122_1841)))
end
| false -> begin
(let _122_1843 = (encode_typ_term t env')
in (app, _122_1843))
end)
in (match (_53_2275) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _122_1850 = (let _122_1849 = (let _122_1848 = (let _122_1847 = (let _122_1846 = (let _122_1845 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _122_1844 = (FStar_ToSMT_Term.mkEq (def, body))
in (_122_1845, _122_1844)))
in (FStar_ToSMT_Term.mkImp _122_1846))
in ((def)::[], vars, _122_1847))
in (FStar_ToSMT_Term.mkForall _122_1848))
in (_122_1849, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_122_1850))
in (let kindingAx = (let _53_2279 = (let _122_1851 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _122_1851 env' app))
in (match (_53_2279) with
| (k, decls) -> begin
(let _122_1859 = (let _122_1858 = (let _122_1857 = (let _122_1856 = (let _122_1855 = (let _122_1854 = (let _122_1853 = (let _122_1852 = (FStar_ToSMT_Term.mk_and_l guards)
in (_122_1852, k))
in (FStar_ToSMT_Term.mkImp _122_1853))
in ((app)::[], vars, _122_1854))
in (FStar_ToSMT_Term.mkForall _122_1855))
in (_122_1856, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_122_1857))
in (_122_1858)::[])
in (FStar_List.append decls _122_1859))
end))
in (let g = (let _122_1860 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _122_1860))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _53_2286) -> begin
(let tt = (whnf env t)
in (let _53_2292 = (encode_free_var env lid t tt quals)
in (match (_53_2292) with
| (decls, env) -> begin
(match (((FStar_Absyn_Util.is_smt_lemma t) && ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface))) with
| true -> begin
(let _122_1862 = (let _122_1861 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _122_1861))
in (_122_1862, env))
end
| false -> begin
(decls, env)
end)
end)))
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _53_2296, _53_2298) -> begin
(let _53_2303 = (encode_formula f env)
in (match (_53_2303) with
| (f, decls) -> begin
(let g = (let _122_1867 = (let _122_1866 = (let _122_1865 = (let _122_1864 = (let _122_1863 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _122_1863))
in Some (_122_1864))
in (f, _122_1865))
in FStar_ToSMT_Term.Assume (_122_1866))
in (_122_1867)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2309, datas, quals, _53_2313) when (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(let _53_2319 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2319) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _53_2322, _53_2324, _53_2326, _53_2328, _53_2330, _53_2332) when ((FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Absyn_Syntax.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.FStar_Absyn_Syntax.str
in (let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _122_1869 = (let _122_1868 = (primitive_type_axioms t tname tsym)
in (decl)::_122_1868)
in (_122_1869, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2342, datas, quals, _53_2346) -> begin
(let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_19 -> (match (_53_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _53_2353 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(let _53_2363 = c
in (match (_53_2363) with
| (name, args, _53_2360, _53_2362) -> begin
(let _122_1875 = (let _122_1874 = (let _122_1873 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _122_1873, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_122_1874))
in (_122_1875)::[])
end))
end
| false -> begin
(FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun tapp vars -> (match ((((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _122_1881 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _122_1881 FStar_Option.isNone))))))) with
| true -> begin
[]
end
| false -> begin
(let _53_2370 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2370) with
| (xxsym, xx) -> begin
(let _53_2413 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _53_2373 l -> (match (_53_2373) with
| (out, decls) -> begin
(let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _53_2383 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_53_2383) with
| (args, res) -> begin
(let indices = (match ((let _122_1884 = (FStar_Absyn_Util.compress_typ res)
in _122_1884.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_53_2385, indices) -> begin
indices
end
| _53_2390 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _122_1889 = (let _122_1888 = (let _122_1887 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_122_1887, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _122_1888))
in (push_typ_var env a.FStar_Absyn_Syntax.v _122_1889))
end
| FStar_Util.Inr (x) -> begin
(let _122_1892 = (let _122_1891 = (let _122_1890 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_122_1890, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _122_1891))
in (push_term_var env x.FStar_Absyn_Syntax.v _122_1892))
end)) env))
in (let _53_2401 = (encode_args indices env)
in (match (_53_2401) with
| (indices, decls') -> begin
(let _53_2402 = (match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(FStar_All.failwith "Impossible")
end
| false -> begin
()
end)
in (let eqs = (let _122_1899 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _122_1896 = (let _122_1895 = (FStar_ToSMT_Term.mkFreeV v)
in (_122_1895, a))
in (FStar_ToSMT_Term.mkEq _122_1896))
end
| FStar_Util.Inr (a) -> begin
(let _122_1898 = (let _122_1897 = (FStar_ToSMT_Term.mkFreeV v)
in (_122_1897, a))
in (FStar_ToSMT_Term.mkEq _122_1898))
end)) vars indices)
in (FStar_All.pipe_right _122_1899 FStar_ToSMT_Term.mk_and_l))
in (let _122_1904 = (let _122_1903 = (let _122_1902 = (let _122_1901 = (let _122_1900 = (mk_data_tester env l xx)
in (_122_1900, eqs))
in (FStar_ToSMT_Term.mkAnd _122_1901))
in (out, _122_1902))
in (FStar_ToSMT_Term.mkOr _122_1903))
in (_122_1904, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_53_2413) with
| (data_ax, decls) -> begin
(let _53_2416 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2416) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _122_1905 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _122_1905 xx tapp))
in (let _122_1912 = (let _122_1911 = (let _122_1910 = (let _122_1909 = (let _122_1908 = (let _122_1907 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _122_1906 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _122_1907, _122_1906)))
in (FStar_ToSMT_Term.mkForall _122_1908))
in (_122_1909, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_122_1910))
in (_122_1911)::[])
in (FStar_List.append decls _122_1912)))
end))
end))
end))
end))
in (let k = (FStar_Absyn_Util.close_kind tps k)
in (let _53_2428 = (match ((let _122_1913 = (FStar_Absyn_Util.compress_kind k)
in _122_1913.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _53_2424 -> begin
(false, [], k)
end)
in (match (_53_2428) with
| (is_kind_arrow, formals, res) -> begin
(let _53_2435 = (encode_binders None formals env)
in (match (_53_2435) with
| (vars, guards, env', binder_decls, _53_2434) -> begin
(let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _53_20 -> (match (_53_20) with
| FStar_Absyn_Syntax.Projector (_53_2441) -> begin
true
end
| _53_2444 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(let rec projectee = (fun i _53_21 -> (match (_53_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_53_2459) -> begin
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
in (let _53_2474 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_53_2465, xx::suffix) -> begin
(xx, suffix)
end
| _53_2471 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_2474) with
| (xx, suffix) -> begin
(let dproj_app = (let _122_1927 = (let _122_1926 = (let _122_1925 = (mk_typ_projector_name d a)
in (let _122_1924 = (let _122_1923 = (FStar_ToSMT_Term.mkFreeV xx)
in (_122_1923)::[])
in (_122_1925, _122_1924)))
in (FStar_ToSMT_Term.mkApp _122_1926))
in (mk_ApplyT _122_1927 suffix))
in (let _122_1932 = (let _122_1931 = (let _122_1930 = (let _122_1929 = (let _122_1928 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _122_1928))
in (FStar_ToSMT_Term.mkForall _122_1929))
in (_122_1930, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_122_1931))
in (_122_1932)::[]))
end))))
end
| _53_2477 -> begin
[]
end))
in (let pretype_axioms = (fun tapp vars -> (let _53_2483 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2483) with
| (xxsym, xx) -> begin
(let _53_2486 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2486) with
| (ffsym, ff) -> begin
(let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _122_1945 = (let _122_1944 = (let _122_1943 = (let _122_1942 = (let _122_1941 = (let _122_1940 = (let _122_1939 = (let _122_1938 = (let _122_1937 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _122_1937))
in (FStar_ToSMT_Term.mkEq _122_1938))
in (xx_has_type, _122_1939))
in (FStar_ToSMT_Term.mkImp _122_1940))
in ((xx_has_type)::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _122_1941))
in (FStar_ToSMT_Term.mkForall _122_1942))
in (_122_1943, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_122_1944))
in (_122_1945)::[]))
end))
end)))
in (let _53_2491 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2491) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _122_1947 = (let _122_1946 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _122_1946))
in (FStar_ToSMT_Term.mkApp _122_1947))
in (let _53_2516 = (let tname_decl = (let _122_1951 = (let _122_1950 = (FStar_All.pipe_right vars (FStar_List.map (fun _53_2497 -> (match (_53_2497) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _122_1949 = (varops.next_id ())
in (tname, _122_1950, FStar_ToSMT_Term.Type_sort, _122_1949)))
in (constructor_or_logic_type_decl _122_1951))
in (let _53_2513 = (match (vars) with
| [] -> begin
(let _122_1955 = (let _122_1954 = (let _122_1953 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _122_1952 -> Some (_122_1952)) _122_1953))
in (push_free_tvar env t tname _122_1954))
in ([], _122_1955))
end
| _53_2501 -> begin
(let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _122_1956 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _122_1956))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match (((not (is_logical)) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_22 -> (match (_53_22) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _53_2508 -> begin
false
end)))))) with
| true -> begin
((ttok_app)::[])::((tapp)::[])::[]
end
| false -> begin
((ttok_app)::[])::[]
end)
in (let name_tok_corr = (let _122_1961 = (let _122_1960 = (let _122_1959 = (let _122_1958 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _122_1958))
in (FStar_ToSMT_Term.mkForall' _122_1959))
in (_122_1960, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_122_1961))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_53_2513) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_53_2516) with
| (decls, env) -> begin
(let kindingAx = (let _53_2519 = (encode_knd res env' tapp)
in (match (_53_2519) with
| (k, decls) -> begin
(let karr = (match (is_kind_arrow) with
| true -> begin
(let _122_1965 = (let _122_1964 = (let _122_1963 = (let _122_1962 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _122_1962))
in (_122_1963, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_122_1964))
in (_122_1965)::[])
end
| false -> begin
[]
end)
in (let _122_1971 = (let _122_1970 = (let _122_1969 = (let _122_1968 = (let _122_1967 = (let _122_1966 = (FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _122_1966))
in (FStar_ToSMT_Term.mkForall _122_1967))
in (_122_1968, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_122_1969))
in (_122_1970)::[])
in (FStar_List.append (FStar_List.append decls karr) _122_1971)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _122_1972 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _122_1972))
end
| false -> begin
(let _122_1979 = (let _122_1977 = (let _122_1975 = (let _122_1973 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _122_1973))
in (let _122_1974 = (inversion_axioms tapp vars)
in (FStar_List.append _122_1975 _122_1974)))
in (let _122_1976 = (projection_axioms tapp vars)
in (FStar_List.append _122_1977 _122_1976)))
in (let _122_1978 = (pretype_axioms tapp vars)
in (FStar_List.append _122_1979 _122_1978)))
end)
in (let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _53_2526, _53_2528, _53_2530, _53_2532, _53_2534) when (FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_53_2540, tps, _53_2543), quals, _53_2547, drange) -> begin
(let t = (let _122_1981 = (FStar_List.map (fun _53_2554 -> (match (_53_2554) with
| (x, _53_2553) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _122_1981 t))
in (let _53_2559 = (new_term_constant_and_tok_from_lid env d)
in (match (_53_2559) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _53_2568 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_53_2568) with
| (formals, t_res) -> begin
(let _53_2571 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2571) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _53_2578 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2578) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _53_23 -> (match (_53_23) with
| FStar_Util.Inl (a) -> begin
(let _122_1983 = (mk_typ_projector_name d a)
in (_122_1983, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _122_1984 = (mk_term_projector_name d x)
in (_122_1984, FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _122_1986 = (let _122_1985 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _122_1985))
in (FStar_All.pipe_right _122_1986 FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _53_2592 = (encode_typ_pred None t env ddtok_tm)
in (match (_53_2592) with
| (tok_typing, decls3) -> begin
(let _53_2599 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2599) with
| (vars', guards', env'', decls_formals, _53_2598) -> begin
(let _53_2604 = (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_53_2604) with
| (ty_pred', decls_pred) -> begin
(let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _53_2608 -> begin
(let _122_1988 = (let _122_1987 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _122_1987))
in (_122_1988)::[])
end)
in (let encode_elim = (fun _53_2611 -> (match (()) with
| () -> begin
(let _53_2614 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_53_2614) with
| (head, args) -> begin
(match ((let _122_1991 = (FStar_Absyn_Util.compress_typ head)
in _122_1991.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _53_2620 = (encode_args args env')
in (match (_53_2620) with
| (encoded_args, arg_decls) -> begin
(let _53_2644 = (FStar_List.fold_left (fun _53_2624 arg -> (match (_53_2624) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(let _53_2632 = (let _122_1994 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _122_1994))
in (match (_53_2632) with
| (_53_2629, tv, env) -> begin
(let _122_1996 = (let _122_1995 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_122_1995)::eqns)
in (env, (tv)::arg_vars, _122_1996))
end))
end
| FStar_Util.Inr (varg) -> begin
(let _53_2639 = (let _122_1997 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _122_1997))
in (match (_53_2639) with
| (_53_2636, xv, env) -> begin
(let _122_1999 = (let _122_1998 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_122_1998)::eqns)
in (env, (xv)::arg_vars, _122_1999))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_53_2644) with
| (_53_2641, arg_vars, eqns) -> begin
(let arg_vars = (FStar_List.rev arg_vars)
in (let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _122_2006 = (let _122_2005 = (let _122_2004 = (let _122_2003 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _122_2002 = (let _122_2001 = (let _122_2000 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _122_2000))
in (FStar_ToSMT_Term.mkImp _122_2001))
in ((ty_pred)::[], _122_2003, _122_2002)))
in (FStar_ToSMT_Term.mkForall _122_2004))
in (_122_2005, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_122_2006))
in (let subterm_ordering = (match ((FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _122_2007 = (varops.fresh "x")
in (_122_2007, FStar_ToSMT_Term.Term_sort))
in (let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _122_2016 = (let _122_2015 = (let _122_2014 = (let _122_2013 = (let _122_2008 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_122_2008)::[])
in (let _122_2012 = (let _122_2011 = (let _122_2010 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _122_2009 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_122_2010, _122_2009)))
in (FStar_ToSMT_Term.mkImp _122_2011))
in (_122_2013, (x)::[], _122_2012)))
in (FStar_ToSMT_Term.mkForall _122_2014))
in (_122_2015, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_122_2016))))
end
| false -> begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _122_2019 = (let _122_2018 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _122_2018 dapp))
in (_122_2019)::[])
end
| _53_2659 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _122_2026 = (let _122_2025 = (let _122_2024 = (let _122_2023 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _122_2022 = (let _122_2021 = (let _122_2020 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _122_2020))
in (FStar_ToSMT_Term.mkImp _122_2021))
in ((ty_pred)::[], _122_2023, _122_2022)))
in (FStar_ToSMT_Term.mkForall _122_2024))
in (_122_2025, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_122_2026)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _53_2663 -> begin
(let _53_2664 = (let _122_2029 = (let _122_2028 = (FStar_Absyn_Print.sli d)
in (let _122_2027 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _122_2028 _122_2027)))
in (FStar_Tc_Errors.warn drange _122_2029))
in ([], []))
end)
end))
end))
in (let _53_2668 = (encode_elim ())
in (match (_53_2668) with
| (decls2, elim) -> begin
(let g = (let _122_2054 = (let _122_2053 = (let _122_2038 = (let _122_2037 = (let _122_2036 = (let _122_2035 = (let _122_2034 = (let _122_2033 = (let _122_2032 = (let _122_2031 = (let _122_2030 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _122_2030))
in Some (_122_2031))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _122_2032))
in FStar_ToSMT_Term.DeclFun (_122_2033))
in (_122_2034)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _122_2035))
in (FStar_List.append _122_2036 proxy_fresh))
in (FStar_List.append _122_2037 decls_formals))
in (FStar_List.append _122_2038 decls_pred))
in (let _122_2052 = (let _122_2051 = (let _122_2050 = (let _122_2042 = (let _122_2041 = (let _122_2040 = (let _122_2039 = (FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _122_2039))
in (FStar_ToSMT_Term.mkForall _122_2040))
in (_122_2041, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_122_2042))
in (let _122_2049 = (let _122_2048 = (let _122_2047 = (let _122_2046 = (let _122_2045 = (let _122_2044 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _122_2043 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _122_2044, _122_2043)))
in (FStar_ToSMT_Term.mkForall _122_2045))
in (_122_2046, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_122_2047))
in (_122_2048)::[])
in (_122_2050)::_122_2049))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_122_2051)
in (FStar_List.append _122_2053 _122_2052)))
in (FStar_List.append _122_2054 elim))
in ((FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end)))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _53_2672, _53_2674, _53_2676) -> begin
(let _53_2681 = (encode_signature env ses)
in (match (_53_2681) with
| (g, env) -> begin
(let _53_2693 = (FStar_All.pipe_right g (FStar_List.partition (fun _53_24 -> (match (_53_24) with
| FStar_ToSMT_Term.Assume (_53_2684, Some ("inversion axiom")) -> begin
false
end
| _53_2690 -> begin
true
end))))
in (match (_53_2693) with
| (g', inversions) -> begin
(let _53_2702 = (FStar_All.pipe_right g' (FStar_List.partition (fun _53_25 -> (match (_53_25) with
| FStar_ToSMT_Term.DeclFun (_53_2696) -> begin
true
end
| _53_2699 -> begin
false
end))))
in (match (_53_2702) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_53_2704, _53_2706, _53_2708, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_26 -> (match (_53_26) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _53_2720 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _53_2725, _53_2727, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (FStar_List.length binders)
in (let _53_2739 = (FStar_Util.first_N nbinders formals)
in (match (_53_2739) with
| (formals, extra_formals) -> begin
(let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _122_2069 = (let _122_2068 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _122_2068))
in FStar_Util.Inl (_122_2069))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _122_2071 = (let _122_2070 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _122_2070))
in FStar_Util.Inr (_122_2071))
end
| _53_2753 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _122_2072 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _122_2072 FStar_Absyn_Util.name_binders))
in (let body = (let _122_2078 = (let _122_2074 = (let _122_2073 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _122_2073))
in (body, _122_2074))
in (let _122_2077 = (let _122_2076 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _122_2075 -> Some (_122_2075)) _122_2076))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _122_2078 _122_2077 body.FStar_Absyn_Syntax.pos)))
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
(let _53_2791 = (FStar_Util.first_N nformals binders)
in (match (_53_2791) with
| (bs0, rest) -> begin
(let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _53_2795 -> begin
(FStar_All.failwith "impossible")
end)
in (let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end
| false -> begin
(match ((nformals > nbinders)) with
| true -> begin
(let _53_2800 = (eta_expand binders formals body tres)
in (match (_53_2800) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end
| false -> begin
(binders, body, formals, tres)
end)
end))))
end
| _53_2802 -> begin
(let _122_2087 = (let _122_2086 = (FStar_Absyn_Print.exp_to_string e)
in (let _122_2085 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Absyn_Syntax.str _122_2086 _122_2085)))
in (FStar_All.failwith _122_2087))
end)
end
| _53_2804 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let tres = (FStar_Absyn_Util.comp_result c)
in (let _53_2812 = (eta_expand [] formals e tres)
in (match (_53_2812) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _53_2814 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _53_2816 -> (match (()) with
| () -> begin
(match ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_27 -> (match (_53_27) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _53_2827 -> begin
false
end))))) with
| true -> begin
([], env)
end
| false -> begin
(match ((FStar_All.pipe_right bindings (FStar_Util.for_some (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) with
| true -> begin
(let _122_2093 = (FStar_All.pipe_right bindings (FStar_List.collect (fun lb -> (match ((FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _122_2092 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _122_2092 lb.FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(Prims.raise Let_rec_unencodeable)
end))))
in (_122_2093, env))
end
| false -> begin
(let _53_2847 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _53_2834 lb -> (match (_53_2834) with
| (toks, typs, decls, env) -> begin
(let _53_2836 = (match ((FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| false -> begin
()
end)
in (let t_norm = (let _122_2096 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _122_2096 FStar_Absyn_Util.compress_typ))
in (let _53_2842 = (let _122_2097 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _122_2097 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_53_2842) with
| (tok, decl, env) -> begin
(let _122_2100 = (let _122_2099 = (let _122_2098 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_122_2098, tok))
in (_122_2099)::toks)
in (_122_2100, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_53_2847) with
| (toks, typs, decls, env) -> begin
(let toks = (FStar_List.rev toks)
in (let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (let typs = (FStar_List.rev typs)
in (match (((FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_28 -> (match (_53_28) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _53_2854 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _122_2103 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _122_2103)))))))) with
| true -> begin
(decls, env)
end
| false -> begin
(match ((not (is_rec))) with
| true -> begin
(match ((bindings, typs, toks)) with
| ({FStar_Absyn_Syntax.lbname = _53_2862; FStar_Absyn_Syntax.lbtyp = _53_2860; FStar_Absyn_Syntax.lbeff = _53_2858; FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _53_2878 = (destruct_bound_function flid t_norm e)
in (match (_53_2878) with
| (binders, body, formals, tres) -> begin
(let _53_2885 = (encode_binders None binders env)
in (match (_53_2885) with
| (vars, guards, env', binder_decls, _53_2884) -> begin
(let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _53_2888 -> begin
(let _122_2105 = (let _122_2104 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _122_2104))
in (FStar_ToSMT_Term.mkApp _122_2105))
end)
in (let _53_2892 = (encode_exp body env')
in (match (_53_2892) with
| (body, decls2) -> begin
(let eqn = (let _122_2114 = (let _122_2113 = (let _122_2110 = (let _122_2109 = (let _122_2108 = (let _122_2107 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _122_2106 = (FStar_ToSMT_Term.mkEq (app, body))
in (_122_2107, _122_2106)))
in (FStar_ToSMT_Term.mkImp _122_2108))
in ((app)::[], vars, _122_2109))
in (FStar_ToSMT_Term.mkForall _122_2110))
in (let _122_2112 = (let _122_2111 = (FStar_Util.format1 "Equation for %s" flid.FStar_Absyn_Syntax.str)
in Some (_122_2111))
in (_122_2113, _122_2112)))
in FStar_ToSMT_Term.Assume (_122_2114))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _53_2895 -> begin
(FStar_All.failwith "Impossible")
end)
end
| false -> begin
(let fuel = (let _122_2115 = (varops.fresh "fuel")
in (_122_2115, FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _53_2912 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _53_2901 _53_2906 -> (match ((_53_2901, _53_2906)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _122_2120 = (let _122_2119 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _122_2118 -> Some (_122_2118)) _122_2119))
in (push_free_var env flid gtok _122_2120))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_53_2912) with
| (gtoks, env) -> begin
(let gtoks = (FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _53_2921 t_norm _53_2930 -> (match ((_53_2921, _53_2930)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _53_2929; FStar_Absyn_Syntax.lbtyp = _53_2927; FStar_Absyn_Syntax.lbeff = _53_2925; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _53_2935 = (destruct_bound_function flid t_norm e)
in (match (_53_2935) with
| (binders, body, formals, tres) -> begin
(let _53_2942 = (encode_binders None binders env)
in (match (_53_2942) with
| (vars, guards, env', binder_decls, _53_2941) -> begin
(let decl_g = (let _122_2131 = (let _122_2130 = (let _122_2129 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_122_2129)
in (g, _122_2130, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_122_2131))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _122_2134 = (let _122_2133 = (let _122_2132 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_122_2132)::vars_tm)
in (g, _122_2133))
in (FStar_ToSMT_Term.mkApp _122_2134))
in (let gmax = (let _122_2137 = (let _122_2136 = (let _122_2135 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_122_2135)::vars_tm)
in (g, _122_2136))
in (FStar_ToSMT_Term.mkApp _122_2137))
in (let _53_2952 = (encode_exp body env')
in (match (_53_2952) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _122_2146 = (let _122_2145 = (let _122_2142 = (let _122_2141 = (let _122_2140 = (let _122_2139 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _122_2138 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_122_2139, _122_2138)))
in (FStar_ToSMT_Term.mkImp _122_2140))
in ((gsapp)::[], (fuel)::vars, _122_2141))
in (FStar_ToSMT_Term.mkForall _122_2142))
in (let _122_2144 = (let _122_2143 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Absyn_Syntax.str)
in Some (_122_2143))
in (_122_2145, _122_2144)))
in FStar_ToSMT_Term.Assume (_122_2146))
in (let eqn_f = (let _122_2150 = (let _122_2149 = (let _122_2148 = (let _122_2147 = (FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _122_2147))
in (FStar_ToSMT_Term.mkForall _122_2148))
in (_122_2149, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_122_2150))
in (let eqn_g' = (let _122_2159 = (let _122_2158 = (let _122_2157 = (let _122_2156 = (let _122_2155 = (let _122_2154 = (let _122_2153 = (let _122_2152 = (let _122_2151 = (FStar_ToSMT_Term.n_fuel 0)
in (_122_2151)::vars_tm)
in (g, _122_2152))
in (FStar_ToSMT_Term.mkApp _122_2153))
in (gsapp, _122_2154))
in (FStar_ToSMT_Term.mkEq _122_2155))
in ((gsapp)::[], (fuel)::vars, _122_2156))
in (FStar_ToSMT_Term.mkForall _122_2157))
in (_122_2158, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_122_2159))
in (let _53_2975 = (let _53_2962 = (encode_binders None formals env0)
in (match (_53_2962) with
| (vars, v_guards, env, binder_decls, _53_2961) -> begin
(let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _122_2160 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _122_2160 ((fuel)::vars)))
in (let _122_2164 = (let _122_2163 = (let _122_2162 = (let _122_2161 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _122_2161))
in (FStar_ToSMT_Term.mkForall _122_2162))
in (_122_2163, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_122_2164)))
in (let _53_2972 = (let _53_2969 = (encode_typ_pred None tres env gapp)
in (match (_53_2969) with
| (g_typing, d3) -> begin
(let _122_2172 = (let _122_2171 = (let _122_2170 = (let _122_2169 = (let _122_2168 = (let _122_2167 = (let _122_2166 = (let _122_2165 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_122_2165, g_typing))
in (FStar_ToSMT_Term.mkImp _122_2166))
in ((gapp)::[], (fuel)::vars, _122_2167))
in (FStar_ToSMT_Term.mkForall _122_2168))
in (_122_2169, None))
in FStar_ToSMT_Term.Assume (_122_2170))
in (_122_2171)::[])
in (d3, _122_2172))
end))
in (match (_53_2972) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_53_2975) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _53_2991 = (let _122_2175 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _53_2979 _53_2983 -> (match ((_53_2979, _53_2983)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _53_2987 = (encode_one_binding env0 gtok ty bs)
in (match (_53_2987) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _122_2175))
in (match (_53_2991) with
| (decls, eqns, env0) -> begin
(let _53_3000 = (let _122_2177 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _122_2177 (FStar_List.partition (fun _53_29 -> (match (_53_29) with
| FStar_ToSMT_Term.DeclFun (_53_2994) -> begin
true
end
| _53_2997 -> begin
false
end)))))
in (match (_53_3000) with
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
end)) (fun _53_2815 -> (match (_53_2815) with
| Let_rec_unencodeable -> begin
(let msg = (let _122_2180 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _122_2180 (FStar_String.concat " and ")))
in (let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _53_3027 = (encode_free_var env x t t_norm [])
in (match (_53_3027) with
| (decls, env) -> begin
(let _53_3032 = (lookup_lid env x)
in (match (_53_3032) with
| (n, x', _53_3031) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _53_3036) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun env lid t -> (let _53_3044 = (encode_function_type_as_formula None None t env)
in (match (_53_3044) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun env lid tt t_norm quals -> (match (((let _122_2193 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _122_2193)) || (FStar_Absyn_Util.is_lemma t_norm))) with
| true -> begin
(let _53_3053 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3053) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_3056) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _53_30 -> (match (_53_30) with
| (FStar_Util.Inl (_53_3061), _53_3064) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3067 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _53_3069 -> begin
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
in (let _53_3086 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _122_2195 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _122_2195))
end
| false -> begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end)
end
| None -> begin
([], (None, t_norm))
end)
in (match (_53_3086) with
| (formals, (pre_opt, res_t)) -> begin
(let _53_3090 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3090) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _53_3093 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _53_31 -> (match (_53_31) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _53_3109 = (FStar_Util.prefix vars)
in (match (_53_3109) with
| (_53_3104, (xxsym, _53_3107)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _122_2212 = (let _122_2211 = (let _122_2210 = (let _122_2209 = (let _122_2208 = (let _122_2207 = (let _122_2206 = (let _122_2205 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Absyn_Syntax.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _122_2205))
in (vapp, _122_2206))
in (FStar_ToSMT_Term.mkEq _122_2207))
in ((vapp)::[], vars, _122_2208))
in (FStar_ToSMT_Term.mkForall _122_2209))
in (_122_2210, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_122_2211))
in (_122_2212)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(let _53_3122 = (FStar_Util.prefix vars)
in (match (_53_3122) with
| (_53_3117, (xxsym, _53_3120)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _122_2214 = (let _122_2213 = (mk_term_projector_name d f)
in (_122_2213, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _122_2214))
in (let _122_2219 = (let _122_2218 = (let _122_2217 = (let _122_2216 = (let _122_2215 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in ((vapp)::[], vars, _122_2215))
in (FStar_ToSMT_Term.mkForall _122_2216))
in (_122_2217, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_122_2218))
in (_122_2219)::[])))
end))
end
| _53_3126 -> begin
[]
end)))))
in (let _53_3133 = (encode_binders None formals env)
in (match (_53_3133) with
| (vars, guards, env', decls1, _53_3132) -> begin
(let _53_3142 = (match (pre_opt) with
| None -> begin
(let _122_2220 = (FStar_ToSMT_Term.mk_and_l guards)
in (_122_2220, decls1))
end
| Some (p) -> begin
(let _53_3139 = (encode_formula p env')
in (match (_53_3139) with
| (g, ds) -> begin
(let _122_2221 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_122_2221, (FStar_List.append decls1 ds)))
end))
end)
in (match (_53_3142) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _122_2223 = (let _122_2222 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _122_2222))
in (FStar_ToSMT_Term.mkApp _122_2223))
in (let _53_3173 = (let vname_decl = (let _122_2226 = (let _122_2225 = (FStar_All.pipe_right formals (FStar_List.map (fun _53_32 -> (match (_53_32) with
| (FStar_Util.Inl (_53_3147), _53_3150) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3153 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _122_2225, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_122_2226))
in (let _53_3160 = (let env = (let _53_3155 = env
in {bindings = _53_3155.bindings; depth = _53_3155.depth; tcenv = _53_3155.tcenv; warn = _53_3155.warn; cache = _53_3155.cache; nolabels = _53_3155.nolabels; use_zfuel_name = _53_3155.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((not ((head_normal env tt)))) with
| true -> begin
(encode_typ_pred None tt env vtok_tm)
end
| false -> begin
(encode_typ_pred None t_norm env vtok_tm)
end))
in (match (_53_3160) with
| (tok_typing, decls2) -> begin
(let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _53_3170 = (match (formals) with
| [] -> begin
(let _122_2230 = (let _122_2229 = (let _122_2228 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _122_2227 -> Some (_122_2227)) _122_2228))
in (push_free_var env lid vname _122_2229))
in ((FStar_List.append decls2 ((tok_typing)::[])), _122_2230))
end
| _53_3164 -> begin
(let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _122_2231 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _122_2231))
in (let name_tok_corr = (let _122_2235 = (let _122_2234 = (let _122_2233 = (let _122_2232 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _122_2232))
in (FStar_ToSMT_Term.mkForall _122_2233))
in (_122_2234, None))
in FStar_ToSMT_Term.Assume (_122_2235))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_53_3170) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_53_3173) with
| (decls2, env) -> begin
(let _53_3181 = (let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (let _53_3177 = (encode_typ_term res_t env')
in (match (_53_3177) with
| (encoded_res_t, decls) -> begin
(let _122_2236 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _122_2236, decls))
end)))
in (match (_53_3181) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _122_2240 = (let _122_2239 = (let _122_2238 = (let _122_2237 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _122_2237))
in (FStar_ToSMT_Term.mkForall _122_2238))
in (_122_2239, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_122_2240))
in (let g = (let _122_2242 = (let _122_2241 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_122_2241)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _122_2242))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end)
end))
and encode_signature = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _53_3188 se -> (match (_53_3188) with
| (g, env) -> begin
(let _53_3192 = (encode_sigelt env se)
in (match (_53_3192) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun env bindings -> (let encode_binding = (fun b _53_3199 -> (match (_53_3199) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(let _53_3207 = (new_term_constant env x)
in (match (_53_3207) with
| (xxsym, xx, env') -> begin
(let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _53_3209 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _122_2257 = (FStar_Absyn_Print.strBvd x)
in (let _122_2256 = (FStar_Absyn_Print.typ_to_string t0)
in (let _122_2255 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.fprint3 "Normalized %s : %s to %s\n" _122_2257 _122_2256 _122_2255))))
end
| false -> begin
()
end)
in (let _53_3213 = (encode_typ_pred None t1 env xx)
in (match (_53_3213) with
| (t, decls') -> begin
(let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _122_2261 = (let _122_2260 = (FStar_Absyn_Print.strBvd x)
in (let _122_2259 = (FStar_Absyn_Print.typ_to_string t0)
in (let _122_2258 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _122_2260 _122_2259 _122_2258))))
in Some (_122_2261))
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
(let _53_3223 = (new_typ_constant env a)
in (match (_53_3223) with
| (aasym, aa, env') -> begin
(let _53_3226 = (encode_knd k env aa)
in (match (_53_3226) with
| (k, decls') -> begin
(let g = (let _122_2267 = (let _122_2266 = (let _122_2265 = (let _122_2264 = (let _122_2263 = (let _122_2262 = (FStar_Absyn_Print.strBvd a)
in Some (_122_2262))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _122_2263))
in FStar_ToSMT_Term.DeclFun (_122_2264))
in (_122_2265)::[])
in (FStar_List.append _122_2266 decls'))
in (FStar_List.append _122_2267 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(let t_norm = (whnf env t)
in (let _53_3235 = (encode_free_var env x t t_norm [])
in (match (_53_3235) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(let _53_3240 = (encode_sigelt env se)
in (match (_53_3240) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _53_3247 -> (match (_53_3247) with
| (l, _53_3244, _53_3246) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _53_3254 -> (match (_53_3254) with
| (l, _53_3251, _53_3253) -> begin
(let _122_2275 = (FStar_All.pipe_left (fun _122_2271 -> FStar_ToSMT_Term.Echo (_122_2271)) (Prims.fst l))
in (let _122_2274 = (let _122_2273 = (let _122_2272 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_122_2272))
in (_122_2273)::[])
in (_122_2275)::_122_2274))
end))))
in (prefix, suffix))))

let last_env = (FStar_Util.mk_ref [])

let init_env = (fun tcenv -> (let _122_2280 = (let _122_2279 = (let _122_2278 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _122_2278; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_122_2279)::[])
in (FStar_ST.op_Colon_Equals last_env _122_2280)))

let get_env = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_53_3260 -> begin
(let _53_3263 = e
in {bindings = _53_3263.bindings; depth = _53_3263.depth; tcenv = tcenv; warn = _53_3263.warn; cache = _53_3263.cache; nolabels = _53_3263.nolabels; use_zfuel_name = _53_3263.use_zfuel_name; encode_non_total_function_typ = _53_3263.encode_non_total_function_typ})
end))

let set_env = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _53_3269::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun _53_3271 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (FStar_Util.smap_copy hd.cache)
in (let top = (let _53_3277 = hd
in {bindings = _53_3277.bindings; depth = _53_3277.depth; tcenv = _53_3277.tcenv; warn = _53_3277.warn; cache = refs; nolabels = _53_3277.nolabels; use_zfuel_name = _53_3277.use_zfuel_name; encode_non_total_function_typ = _53_3277.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env = (fun _53_3280 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _53_3284::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env = (fun _53_3286 -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun _53_3287 -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun _53_3288 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_53_3291::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _53_3296 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let init = (fun tcenv -> (let _53_3298 = (init_env tcenv)
in (let _53_3300 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun msg -> (let _53_3303 = (push_env ())
in (let _53_3305 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))

let pop = (fun msg -> (let _53_3308 = (let _122_2301 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _122_2301))
in (let _53_3310 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))

let mark = (fun msg -> (let _53_3313 = (mark_env ())
in (let _53_3315 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun msg -> (let _53_3318 = (reset_mark_env ())
in (let _53_3320 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _53_3323 = (commit_mark_env ())
in (let _53_3325 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun tcenv se -> (let caption = (fun decls -> (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _122_2315 = (let _122_2314 = (let _122_2313 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _122_2313))
in FStar_ToSMT_Term.Caption (_122_2314))
in (_122_2315)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _53_3334 = (encode_sigelt env se)
in (match (_53_3334) with
| (decls, env) -> begin
(let _53_3335 = (set_env env)
in (let _122_2316 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _122_2316)))
end)))))

let encode_modul = (fun tcenv modul -> (let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)
in (let _53_3340 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(let _122_2321 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.fprint2 "Encoding externals for %s ... %s exports\n" name _122_2321))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _53_3347 = (encode_signature (let _53_3343 = env
in {bindings = _53_3343.bindings; depth = _53_3343.depth; tcenv = _53_3343.tcenv; warn = false; cache = _53_3343.cache; nolabels = _53_3343.nolabels; use_zfuel_name = _53_3343.use_zfuel_name; encode_non_total_function_typ = _53_3343.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_53_3347) with
| (decls, env) -> begin
(let caption = (fun decls -> (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _53_3353 = (set_env (let _53_3351 = env
in {bindings = _53_3351.bindings; depth = _53_3351.depth; tcenv = _53_3351.tcenv; warn = true; cache = _53_3351.cache; nolabels = _53_3351.nolabels; use_zfuel_name = _53_3351.use_zfuel_name; encode_non_total_function_typ = _53_3351.encode_non_total_function_typ}))
in (let _53_3355 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(FStar_Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun tcenv q -> (let _53_3360 = (let _122_2330 = (let _122_2329 = (let _122_2328 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _122_2328))
in (FStar_Util.format1 "Starting query at %s" _122_2329))
in (push _122_2330))
in (let pop = (fun _53_3363 -> (match (()) with
| () -> begin
(let _122_2335 = (let _122_2334 = (let _122_2333 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _122_2333))
in (FStar_Util.format1 "Ending query at %s" _122_2334))
in (pop _122_2335))
end))
in (let _53_3393 = (let env = (get_env tcenv)
in (let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _53_3376 = (let _122_2339 = (FStar_List.filter (fun _53_33 -> (match (_53_33) with
| FStar_Tc_Env.Binding_sig (_53_3370) -> begin
false
end
| _53_3373 -> begin
true
end)) bindings)
in (encode_env_bindings env _122_2339))
in (match (_53_3376) with
| (env_decls, env) -> begin
(let _53_3377 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(let _122_2340 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.fprint1 "Encoding query formula: %s\n" _122_2340))
end
| false -> begin
()
end)
in (let _53_3382 = (encode_formula_with_labels q env)
in (match (_53_3382) with
| (phi, labels, qdecls) -> begin
(let _53_3385 = (encode_labels labels)
in (match (_53_3385) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _122_2342 = (let _122_2341 = (FStar_ToSMT_Term.mkNot phi)
in (_122_2341, Some ("query")))
in FStar_ToSMT_Term.Assume (_122_2342))
in (let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_53_3393) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _53_3400); FStar_ToSMT_Term.hash = _53_3397; FStar_ToSMT_Term.freevars = _53_3395}, _53_3405) -> begin
(let _53_3408 = (pop ())
in ())
end
| _53_3411 when tcenv.FStar_Tc_Env.admit -> begin
(let _53_3412 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _53_3416) -> begin
(let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (let _53_3420 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _53_3426 -> (match (_53_3426) with
| (n, i) -> begin
(let _122_2365 = (let _122_2364 = (let _122_2349 = (let _122_2348 = (FStar_Util.string_of_int n)
in (let _122_2347 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _122_2348 _122_2347)))
in FStar_ToSMT_Term.Caption (_122_2349))
in (let _122_2363 = (let _122_2362 = (let _122_2354 = (let _122_2353 = (let _122_2352 = (let _122_2351 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _122_2350 = (FStar_ToSMT_Term.n_fuel n)
in (_122_2351, _122_2350)))
in (FStar_ToSMT_Term.mkEq _122_2352))
in (_122_2353, None))
in FStar_ToSMT_Term.Assume (_122_2354))
in (let _122_2361 = (let _122_2360 = (let _122_2359 = (let _122_2358 = (let _122_2357 = (let _122_2356 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _122_2355 = (FStar_ToSMT_Term.n_fuel i)
in (_122_2356, _122_2355)))
in (FStar_ToSMT_Term.mkEq _122_2357))
in (_122_2358, None))
in FStar_ToSMT_Term.Assume (_122_2359))
in (_122_2360)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_122_2362)::_122_2361))
in (_122_2364)::_122_2363))
in (FStar_List.append _122_2365 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _122_2369 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _122_2368 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_122_2369, _122_2368)))
in (let alt_configs = (let _122_2388 = (let _122_2387 = (match (((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) with
| true -> begin
(let _122_2372 = (let _122_2371 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _122_2370 = (FStar_ST.read FStar_Options.max_ifuel)
in (_122_2371, _122_2370)))
in (_122_2372)::[])
end
| false -> begin
[]
end)
in (let _122_2386 = (let _122_2385 = (match ((((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel))) with
| true -> begin
(let _122_2375 = (let _122_2374 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _122_2373 = (FStar_ST.read FStar_Options.max_ifuel)
in (_122_2374, _122_2373)))
in (_122_2375)::[])
end
| false -> begin
[]
end)
in (let _122_2384 = (let _122_2383 = (match ((((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)))) with
| true -> begin
(let _122_2378 = (let _122_2377 = (FStar_ST.read FStar_Options.max_fuel)
in (let _122_2376 = (FStar_ST.read FStar_Options.max_ifuel)
in (_122_2377, _122_2376)))
in (_122_2378)::[])
end
| false -> begin
[]
end)
in (let _122_2382 = (let _122_2381 = (match (((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel))) with
| true -> begin
(let _122_2380 = (let _122_2379 = (FStar_ST.read FStar_Options.min_fuel)
in (_122_2379, 1))
in (_122_2380)::[])
end
| false -> begin
[]
end)
in (_122_2381)::[])
in (_122_2383)::_122_2382))
in (_122_2385)::_122_2384))
in (_122_2387)::_122_2386))
in (FStar_List.flatten _122_2388))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _53_3435 -> begin
errs
end)
in (let _53_3437 = (match ((FStar_ST.read FStar_Options.print_fuels)) with
| true -> begin
(let _122_2396 = (let _122_2391 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _122_2391))
in (let _122_2395 = (let _122_2392 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _122_2392 FStar_Util.string_of_int))
in (let _122_2394 = (let _122_2393 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _122_2393 FStar_Util.string_of_int))
in (FStar_Util.fprint3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _122_2396 _122_2395 _122_2394))))
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
(let _122_2407 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _122_2407 (cb mi p [])))
end
| _53_3449 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _122_2409 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _122_2409 (fun _53_3455 -> (match (_53_3455) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _53_3458 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _53_3461 p alt _53_3466 -> (match ((_53_3461, _53_3466)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
(match (ok) with
| true -> begin
(match ((FStar_ST.read FStar_Options.print_fuels)) with
| true -> begin
(let _122_2417 = (let _122_2414 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _122_2414))
in (let _122_2416 = (FStar_Util.string_of_int prev_fuel)
in (let _122_2415 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.fprint3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _122_2417 _122_2416 _122_2415))))
end
| false -> begin
()
end)
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _122_2418 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _122_2418 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> (match (((FStar_ST.read FStar_Options.split_cases) > 0)) with
| true -> begin
(let _53_3471 = (let _122_2424 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _122_2424 q))
in (match (_53_3471) with
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
in (let _53_3472 = (match ((FStar_ST.read FStar_Options.admit_smt_queries)) with
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
in (let _53_3477 = (push "query")
in (let _53_3484 = (encode_formula_with_labels q env)
in (match (_53_3484) with
| (f, _53_3481, _53_3483) -> begin
(let _53_3485 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_3489) -> begin
true
end
| _53_3493 -> begin
false
end))
end)))))

let solver = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}

let dummy = {FStar_Tc_Env.init = (fun _53_3494 -> ()); FStar_Tc_Env.push = (fun _53_3496 -> ()); FStar_Tc_Env.pop = (fun _53_3498 -> ()); FStar_Tc_Env.mark = (fun _53_3500 -> ()); FStar_Tc_Env.reset_mark = (fun _53_3502 -> ()); FStar_Tc_Env.commit_mark = (fun _53_3504 -> ()); FStar_Tc_Env.encode_modul = (fun _53_3506 _53_3508 -> ()); FStar_Tc_Env.encode_sig = (fun _53_3510 _53_3512 -> ()); FStar_Tc_Env.solve = (fun _53_3514 _53_3516 -> ()); FStar_Tc_Env.is_trivial = (fun _53_3518 _53_3520 -> false); FStar_Tc_Env.finish = (fun _53_3522 -> ()); FStar_Tc_Env.refresh = (fun _53_3523 -> ())}





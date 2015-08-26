
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

let mk_typ_projector_name = (fun lid a -> (let _118_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _118_14)))

let mk_term_projector_name = (fun lid a -> (let a = (let _118_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _118_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _118_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str (escape_null_name a))
in (FStar_All.pipe_left escape _118_20))))

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _53_62 -> (match (()) with
| () -> begin
(let _118_30 = (let _118_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _118_29 lid.FStar_Absyn_Syntax.str))
in (FStar_All.failwith _118_30))
end))
in (let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _118_31 = (FStar_Absyn_Util.compress_typ t)
in _118_31.FStar_Absyn_Syntax.n)) with
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

let mk_term_projector_name_by_pos = (fun lid i -> (let _118_37 = (let _118_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Absyn_Syntax.str _118_36))
in (FStar_All.pipe_left escape _118_37)))

let mk_typ_projector = (fun lid a -> (let _118_43 = (let _118_42 = (mk_typ_projector_name lid a)
in (_118_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _118_43)))

let mk_term_projector = (fun lid a -> (let _118_49 = (let _118_48 = (mk_term_projector_name lid a)
in (_118_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _118_49)))

let mk_term_projector_by_pos = (fun lid i -> (let _118_55 = (let _118_54 = (mk_term_projector_name_by_pos lid i)
in (_118_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _118_55)))

let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Absyn_Syntax.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Absyn_Syntax.ident  ->  FStar_Absyn_Syntax.ident  ->  Prims.string; new_fvar : FStar_Absyn_Syntax.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _53_101 -> (match (()) with
| () -> begin
(let _118_159 = (FStar_Util.smap_create 100)
in (let _118_158 = (FStar_Util.smap_create 100)
in (_118_159, _118_158)))
end))
in (let scopes = (let _118_161 = (let _118_160 = (new_scope ())
in (_118_160)::[])
in (FStar_Util.mk_ref _118_161))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _118_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _118_165 (fun _53_109 -> (match (_53_109) with
| (names, _53_108) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_53_112) -> begin
(let _53_114 = (FStar_Util.incr ctr)
in (let _118_167 = (let _118_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _118_166))
in (Prims.strcat (Prims.strcat y "__") _118_167)))
end)
in (let top_scope = (let _118_169 = (let _118_168 = (FStar_ST.read scopes)
in (FStar_List.hd _118_168))
in (FStar_All.pipe_left Prims.fst _118_169))
in (let _53_118 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _118_175 = (let _118_174 = (FStar_All.pipe_left mk_unique pp.FStar_Absyn_Syntax.idText)
in (Prims.strcat _118_174 "__"))
in (Prims.strcat _118_175 rn.FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Absyn_Syntax.str))
in (let next_id = (fun _53_126 -> (match (()) with
| () -> begin
(let _53_127 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _118_183 = (let _118_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _118_182))
in (FStar_Util.format2 "%s_%s" pfx _118_183)))
in (let string_const = (fun s -> (match ((let _118_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _118_187 (fun _53_136 -> (match (_53_136) with
| (_53_134, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _118_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _118_188))
in (let top_scope = (let _118_190 = (let _118_189 = (FStar_ST.read scopes)
in (FStar_List.hd _118_189))
in (FStar_All.pipe_left Prims.snd _118_190))
in (let _53_143 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _53_146 -> (match (()) with
| () -> begin
(let _118_195 = (let _118_194 = (new_scope ())
in (let _118_193 = (FStar_ST.read scopes)
in (_118_194)::_118_193))
in (FStar_ST.op_Colon_Equals scopes _118_195))
end))
in (let pop = (fun _53_148 -> (match (()) with
| () -> begin
(let _118_199 = (let _118_198 = (FStar_ST.read scopes)
in (FStar_List.tl _118_198))
in (FStar_ST.op_Colon_Equals scopes _118_199))
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

let unmangle = (fun x -> (let _118_215 = (let _118_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _118_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_118_214, _118_213)))
in (FStar_Absyn_Util.mkbvd _118_215)))

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

let print_env = (fun e -> (let _118_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _53_2 -> (match (_53_2) with
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
in (FStar_All.pipe_right _118_301 (FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

let caption_t = (fun env t -> (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _118_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_118_311))
end
| false -> begin
None
end))

let fresh_fvar = (fun x s -> (let xsym = (varops.fresh x)
in (let _118_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _118_316))))

let gen_term_var = (fun env x -> (let ysym = (let _118_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _118_321))
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
(let _118_336 = (let _118_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _118_335))
in (FStar_All.failwith _118_336))
end
| Some (b, t) -> begin
t
end))

let gen_typ_var = (fun env x -> (let ysym = (let _118_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _118_341))
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
(let _118_356 = (let _118_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _118_355))
in (FStar_All.failwith _118_356))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _118_367 = (let _53_295 = env
in (let _118_366 = (let _118_365 = (let _118_364 = (let _118_363 = (let _118_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _118_361 -> Some (_118_361)) _118_362))
in (x, fname, _118_363, None))
in Binding_fvar (_118_364))
in (_118_365)::env.bindings)
in {bindings = _118_366; depth = _53_295.depth; tcenv = _53_295.tcenv; warn = _53_295.warn; cache = _53_295.cache; nolabels = _53_295.nolabels; use_zfuel_name = _53_295.use_zfuel_name; encode_non_total_function_typ = _53_295.encode_non_total_function_typ}))
in (fname, ftok, _118_367)))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _53_5 -> (match (_53_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _53_307 -> begin
None
end))))

let lookup_lid = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _118_378 = (let _118_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _118_377))
in (FStar_All.failwith _118_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun env x fname ftok -> (let _53_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _53_317.depth; tcenv = _53_317.tcenv; warn = _53_317.warn; cache = _53_317.cache; nolabels = _53_317.nolabels; use_zfuel_name = _53_317.use_zfuel_name; encode_non_total_function_typ = _53_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun env x f -> (let _53_326 = (lookup_lid env x)
in (match (_53_326) with
| (t1, t2, _53_325) -> begin
(let t3 = (let _118_395 = (let _118_394 = (let _118_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_118_393)::[])
in (f, _118_394))
in (FStar_ToSMT_Term.mkApp _118_395))
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
(match ((let _118_399 = (let _118_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _118_398 Prims.fst))
in (FStar_Util.starts_with _118_399 "fuel"))) with
| true -> begin
(let _118_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _118_400 fuel))
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
(let _118_402 = (let _118_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _118_401))
in (FStar_All.failwith _118_402))
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
in (let _118_417 = (let _53_392 = env
in (let _118_416 = (let _118_415 = (let _118_414 = (let _118_413 = (let _118_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _118_411 -> Some (_118_411)) _118_412))
in (x, fname, _118_413))
in Binding_ftvar (_118_414))
in (_118_415)::env.bindings)
in {bindings = _118_416; depth = _53_392.depth; tcenv = _53_392.tcenv; warn = _53_392.warn; cache = _53_392.cache; nolabels = _53_392.nolabels; use_zfuel_name = _53_392.use_zfuel_name; encode_non_total_function_typ = _53_392.encode_non_total_function_typ}))
in (fname, ftok, _118_417)))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _53_6 -> (match (_53_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _53_403 -> begin
None
end)))) with
| None -> begin
(let _118_424 = (let _118_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _118_423))
in (FStar_All.failwith _118_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun env x fname ftok -> (let _53_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _53_411.depth; tcenv = _53_411.tcenv; warn = _53_411.warn; cache = _53_411.cache; nolabels = _53_411.nolabels; use_zfuel_name = _53_411.use_zfuel_name; encode_non_total_function_typ = _53_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun env a -> (match ((let _118_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _118_435 Prims.snd))) with
| None -> begin
(let _118_437 = (let _118_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _118_436))
in (FStar_All.failwith _118_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> (let _118_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _118_440 Prims.fst)))

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
(let _118_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _118_453))
end
| _53_469 -> begin
(let _118_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _118_454 FStar_List.hd))
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
(let _118_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _118_460 FStar_Option.isNone))
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

let trivial_post = (fun t -> (let _118_482 = (let _118_481 = (let _118_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_118_479)::[])
in (let _118_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_118_481, _118_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _118_482 None t.FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _118_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _118_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _118_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _118_490))
end
| _53_527 -> begin
(let _118_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _118_491))
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
(let _118_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _118_504))
end
| _53_542 -> begin
(let _118_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _118_505))
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
(let _118_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _118_561))
end
| FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _118_562 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_ToSMT_Term.boxInt _118_562))
end
| FStar_Absyn_Syntax.Const_int (i) -> begin
(let _118_563 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _118_563))
end
| FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _118_567 = (let _118_566 = (let _118_565 = (let _118_564 = (FStar_ToSMT_Term.mkInteger32 i)
in (FStar_ToSMT_Term.boxInt _118_564))
in (_118_565)::[])
in ("FStar.Int32.Int32", _118_566))
in (FStar_ToSMT_Term.mkApp _118_567))
end
| FStar_Absyn_Syntax.Const_string (bytes, _53_627) -> begin
(let _118_568 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _118_568))
end
| c -> begin
(let _118_570 = (let _118_569 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _118_569))
in (FStar_All.failwith _118_570))
end))

let as_function_typ = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_53_638) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_53_641) -> begin
(let _118_579 = (FStar_Absyn_Util.unrefine t)
in (aux true _118_579))
end
| _53_644 -> begin
(match (norm) with
| true -> begin
(let _118_580 = (whnf env t)
in (aux false _118_580))
end
| false -> begin
(let _118_583 = (let _118_582 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _118_581 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _118_582 _118_581)))
in (FStar_All.failwith _118_583))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun k env -> (match ((let _118_619 = (FStar_Absyn_Util.compress_kind k)
in _118_619.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_53_649, k0) -> begin
(let _53_653 = (match ((FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _118_621 = (FStar_Absyn_Print.kind_to_string k)
in (let _118_620 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _118_621 _118_620)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _53_657) -> begin
(let _118_623 = (let _118_622 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _118_622))
in (_118_623, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(let tsym = (let _118_624 = (varops.fresh "t")
in (_118_624, FStar_ToSMT_Term.Type_sort))
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
(let _118_633 = (let _118_632 = (let _118_631 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_631))
in (_118_632, body))
in (FStar_ToSMT_Term.mkAnd _118_633))
end)
in (let _118_635 = (let _118_634 = (FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _118_634))
in (FStar_ToSMT_Term.mkForall _118_635)))))
end
| _53_698 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _118_637 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _118_637 (FStar_List.filter (fun _53_703 -> (match (_53_703) with
| (x, _53_702) -> begin
(x <> (Prims.fst tsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _53_709) -> begin
(let _118_640 = (let _118_639 = (let _118_638 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _118_638))
in (FStar_ToSMT_Term.mkApp _118_639))
in (_118_640, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _118_641 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_118_641))
end
| false -> begin
None
end)
in (let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _118_643 = (let _118_642 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _118_642))
in (FStar_ToSMT_Term.mkApp _118_643))
in (let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _118_652 = (let _118_651 = (let _118_650 = (let _118_649 = (let _118_648 = (let _118_647 = (let _118_646 = (let _118_645 = (let _118_644 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_644))
in (_118_645, k_interp))
in (FStar_ToSMT_Term.mkAnd _118_646))
in (t_has_k, _118_647))
in (FStar_ToSMT_Term.mkIff _118_648))
in ((t_has_k)::[], (tsym)::cvars, _118_649))
in (FStar_ToSMT_Term.mkForall _118_650))
in (_118_651, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_118_652))
in (let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _53_721 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _53_724 -> begin
(let _118_654 = (let _118_653 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _118_653))
in (FStar_All.failwith _118_654))
end))
and encode_knd = (fun k env t -> (let _53_730 = (encode_knd_term k env)
in (match (_53_730) with
| (k, decls) -> begin
(let _118_658 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_118_658, decls))
end)))
and encode_binders = (fun fuel_opt bs env -> (let _53_734 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _118_662 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.fprint1 "Encoding binders %s\n" _118_662))
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
(let _118_666 = (FStar_Absyn_Print.strBvd a)
in (let _118_665 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _118_666 aasym _118_665)))
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
(let _53_772 = (let _118_667 = (norm_t env t)
in (encode_typ_pred fuel_opt _118_667 env xx))
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
(let _118_672 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_118_672, decls))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _53_800 = (encode_typ_term t env)
in (match (_53_800) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _118_677 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_118_677, decls))
end
| Some (f) -> begin
(let _118_678 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_118_678, decls))
end)
end))))
and encode_typ_term = (fun t env -> (let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _118_681 = (lookup_typ_var env a)
in (_118_681, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _118_682 = (lookup_free_tvar env fv)
in (_118_682, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
(match (((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _53_821 = (encode_binders None binders env)
in (match (_53_821) with
| (vars, guards, env', decls, _53_820) -> begin
(let fsym = (let _118_683 = (varops.fresh "f")
in (_118_683, FStar_ToSMT_Term.Term_sort))
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
(let _118_684 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_684, decls))
end
| Some (pre) -> begin
(let _53_836 = (encode_formula pre env')
in (match (_53_836) with
| (guard, decls0) -> begin
(let _118_685 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_118_685, (FStar_List.append decls decls0)))
end))
end)
in (match (_53_839) with
| (guards, guard_decls) -> begin
(let t_interp = (let _118_687 = (let _118_686 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _118_686))
in (FStar_ToSMT_Term.mkForall _118_687))
in (let cvars = (let _118_689 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _118_689 (FStar_List.filter (fun _53_844 -> (match (_53_844) with
| (x, _53_843) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _53_850) -> begin
(let _118_692 = (let _118_691 = (let _118_690 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _118_690))
in (FStar_ToSMT_Term.mkApp _118_691))
in (_118_692, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _118_693 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_118_693))
end
| false -> begin
None
end)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _118_695 = (let _118_694 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_694))
in (FStar_ToSMT_Term.mkApp _118_695))
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _118_697 = (let _118_696 = (FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_118_696, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_118_697))
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _118_704 = (let _118_703 = (let _118_702 = (let _118_701 = (let _118_700 = (let _118_699 = (let _118_698 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _118_698))
in (f_has_t, _118_699))
in (FStar_ToSMT_Term.mkImp _118_700))
in ((f_has_t)::[], (fsym)::cvars, _118_701))
in (mkForall_fuel _118_702))
in (_118_703, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_118_704))
in (let t_interp = (let _118_708 = (let _118_707 = (let _118_706 = (let _118_705 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in ((f_has_t_z)::[], (fsym)::cvars, _118_705))
in (FStar_ToSMT_Term.mkForall _118_706))
in (_118_707, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_118_708))
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
in (let t_kinding = (let _118_710 = (let _118_709 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_118_709, None))
in FStar_ToSMT_Term.Assume (_118_710))
in (let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _118_717 = (let _118_716 = (let _118_715 = (let _118_714 = (let _118_713 = (let _118_712 = (let _118_711 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _118_711))
in (f_has_t, _118_712))
in (FStar_ToSMT_Term.mkImp _118_713))
in ((f_has_t)::[], (fsym)::[], _118_714))
in (mkForall_fuel _118_715))
in (_118_716, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_118_717))
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
(let encoding = (let _118_719 = (let _118_718 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_118_718, refinement))
in (FStar_ToSMT_Term.mkAnd _118_719))
in (let cvars = (let _118_721 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _118_721 (FStar_List.filter (fun _53_914 -> (match (_53_914) with
| (y, _53_913) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_921, _53_923) -> begin
(let _118_724 = (let _118_723 = (let _118_722 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _118_722))
in (FStar_ToSMT_Term.mkApp _118_723))
in (_118_724, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _118_726 = (let _118_725 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_725))
in (FStar_ToSMT_Term.mkApp _118_726))
in (let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _118_728 = (let _118_727 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (ffv)::(xfv)::cvars, _118_727))
in (FStar_ToSMT_Term.mkForall _118_728))
in (let t_decls = (let _118_735 = (let _118_734 = (let _118_733 = (let _118_732 = (let _118_731 = (let _118_730 = (let _118_729 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_118_729))
in (assumption, _118_730))
in FStar_ToSMT_Term.Assume (_118_731))
in (_118_732)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_118_733)
in (tdecl)::_118_734)
in (FStar_List.append (FStar_List.append decls decls') _118_735))
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
(let ttm = (let _118_736 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _118_736))
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
in (let t = (let _118_741 = (let _118_740 = (FStar_List.map (fun _53_10 -> (match (_53_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _118_740))
in (FStar_ToSMT_Term.mkApp _118_741))
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
(let ttm = (let _118_742 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _118_742))
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
(let key_body = (let _118_746 = (let _118_745 = (let _118_744 = (let _118_743 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_743, body))
in (FStar_ToSMT_Term.mkImp _118_744))
in ([], vars, _118_745))
in (FStar_ToSMT_Term.mkForall _118_746))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1010, _53_1012) -> begin
(let _118_749 = (let _118_748 = (let _118_747 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _118_747))
in (FStar_ToSMT_Term.mkApp _118_748))
in (_118_749, []))
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
in (let t = (let _118_751 = (let _118_750 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _118_750))
in (FStar_ToSMT_Term.mkApp _118_751))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _118_758 = (let _118_757 = (let _118_756 = (let _118_755 = (let _118_754 = (let _118_753 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _118_752 = (FStar_ToSMT_Term.mkEq (app, body))
in (_118_753, _118_752)))
in (FStar_ToSMT_Term.mkImp _118_754))
in ((app)::[], (FStar_List.append vars cvars), _118_755))
in (FStar_ToSMT_Term.mkForall _118_756))
in (_118_757, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_118_758))
in (let kinding = (let _53_1027 = (let _118_759 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _118_759 env t))
in (match (_53_1027) with
| (ktm, decls'') -> begin
(let _118_763 = (let _118_762 = (let _118_761 = (let _118_760 = (FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_118_760, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_118_761))
in (_118_762)::[])
in (FStar_List.append decls'' _118_763))
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
(let _118_764 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _118_764 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _118_769 = (let _118_768 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _118_767 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _118_766 = (FStar_Absyn_Print.typ_to_string t0)
in (let _118_765 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _118_768 _118_767 _118_766 _118_765)))))
in (FStar_All.failwith _118_769))
end)))
and encode_exp = (fun e env -> (let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_53_1049) -> begin
(let _118_772 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _118_772 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _53_1056) -> begin
(let _118_773 = (lookup_free_var env v)
in (_118_773, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _118_774 = (encode_const c)
in (_118_774, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _53_1064) -> begin
(let _53_1067 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _53_1071)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _53_1077) -> begin
(let e = (let _118_775 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _118_775))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fallback = (fun _53_1086 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _118_778 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_118_778, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _53_1090 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _118_779 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _118_779))) with
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
in (let e = (let _118_781 = (let _118_780 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _118_780))
in (FStar_Absyn_Syntax.mk_Exp_abs _118_781 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
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
(let key_body = (let _118_785 = (let _118_784 = (let _118_783 = (let _118_782 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_782, body))
in (FStar_ToSMT_Term.mkImp _118_783))
in ([], vars, _118_784))
in (FStar_ToSMT_Term.mkForall _118_785))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1124, _53_1126) -> begin
(let _118_788 = (let _118_787 = (let _118_786 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _118_786))
in (FStar_ToSMT_Term.mkApp _118_787))
in (_118_788, []))
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
in (let f = (let _118_790 = (let _118_789 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _118_789))
in (FStar_ToSMT_Term.mkApp _118_790))
in (let app = (mk_ApplyE f vars)
in (let _53_1140 = (encode_typ_pred None tfun env f)
in (match (_53_1140) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _118_792 = (let _118_791 = (FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_118_791, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_118_792))
in (let interp_f = (let _118_799 = (let _118_798 = (let _118_797 = (let _118_796 = (let _118_795 = (let _118_794 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _118_793 = (FStar_ToSMT_Term.mkEq (app, body))
in (_118_794, _118_793)))
in (FStar_ToSMT_Term.mkImp _118_795))
in ((app)::[], (FStar_List.append vars cvars), _118_796))
in (FStar_ToSMT_Term.mkForall _118_797))
in (_118_798, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_118_799))
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
(let _118_800 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_118_800, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_53_1196); FStar_Absyn_Syntax.tk = _53_1194; FStar_Absyn_Syntax.pos = _53_1192; FStar_Absyn_Syntax.fvs = _53_1190; FStar_Absyn_Syntax.uvs = _53_1188}, _53_1200) -> begin
(let _118_801 = (whnf_e env e)
in (encode_exp _118_801 env))
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
in (let ty = (let _118_804 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _118_804 (FStar_Absyn_Util.subst_typ subst)))
in (let _53_1228 = (encode_typ_pred None ty env app_tm)
in (match (_53_1228) with
| (has_type, decls'') -> begin
(let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _118_806 = (let _118_805 = (FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_118_805, None))
in FStar_ToSMT_Term.Assume (_118_806))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _53_1235 = (lookup_free_var_sym env fv)
in (match (_53_1235) with
| (fname, fuel_args) -> begin
(let tm = (let _118_812 = (let _118_811 = (let _118_810 = (FStar_List.map (fun _53_11 -> (match (_53_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _118_810))
in (fname, _118_811))
in (FStar_ToSMT_Term.mkApp' _118_812))
in (tm, decls))
end)))
in (let head = (FStar_Absyn_Util.compress_exp head)
in (let _53_1242 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186")))) with
| true -> begin
(let _118_814 = (FStar_Absyn_Print.exp_to_string head)
in (let _118_813 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _118_814 _118_813)))
end
| false -> begin
()
end)
in (let head_type = (let _118_817 = (let _118_816 = (let _118_815 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _118_815))
in (whnf env _118_816))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _118_817))
in (let _53_1245 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _118_820 = (FStar_Absyn_Print.exp_to_string head)
in (let _118_819 = (FStar_Absyn_Print.tag_of_exp head)
in (let _118_818 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _118_820 _118_819 _118_818))))
end
| false -> begin
()
end)
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _118_824 = (let _118_823 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _118_822 = (FStar_Absyn_Print.exp_to_string e0)
in (let _118_821 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _118_823 _118_822 _118_821))))
in (FStar_All.failwith _118_824))
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
in (let _118_825 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_118_825, (decl_e)::[])))))
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
(let _118_836 = (let _118_835 = (let _118_834 = (let _118_833 = (let _118_832 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _118_832))
in (FStar_ToSMT_Term.mkEq _118_833))
in (guard, _118_834))
in (FStar_ToSMT_Term.mkAnd _118_835))
in (_118_836, decls2))
end))
end)
in (match (_53_1343) with
| (guard, decls2) -> begin
(let _53_1346 = (encode_exp br env)
in (match (_53_1346) with
| (br, decls3) -> begin
(let _118_837 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_118_837, (FStar_List.append (FStar_List.append decls decls2) decls3)))
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
(let _118_840 = (let _118_839 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _118_838 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _118_839 _118_838)))
in (FStar_All.failwith _118_840))
end))))
and encode_pat = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _53_1358 -> begin
(let _118_843 = (encode_one_pat env pat)
in (_118_843)::[])
end))
and encode_one_pat = (fun env pat -> (let _53_1361 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _118_846 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.fprint1 "Encoding pattern %s\n" _118_846))
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
(let _118_854 = (let _118_853 = (encode_const c)
in (scrutinee, _118_853))
in (FStar_ToSMT_Term.mkEq _118_854))
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1415, args) -> begin
(let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1424 -> (match (_53_1424) with
| (arg, _53_1423) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _118_857 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _118_857)))
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
(let _118_865 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1460 -> (match (_53_1460) with
| (arg, _53_1459) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _118_864 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _118_864)))
end))))
in (FStar_All.pipe_right _118_865 FStar_List.flatten))
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
and encode_function_type_as_formula = (fun induction_on t env -> (let v_or_t_pat = (fun p -> (match ((let _118_879 = (FStar_Absyn_Util.unmeta_exp p)
in _118_879.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (_53_1509, (FStar_Util.Inl (_53_1516), _53_1519)::(FStar_Util.Inr (e), _53_1513)::[]) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app (_53_1525, (FStar_Util.Inl (t), _53_1529)::[]) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _53_1535 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun p -> (match ((let _118_882 = (FStar_Absyn_Util.unmeta_exp p)
in _118_882.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app (_53_1539, _53_1551::(FStar_Util.Inr (hd), _53_1548)::(FStar_Util.Inr (tl), _53_1543)::[]) -> begin
(let _118_884 = (v_or_t_pat hd)
in (let _118_883 = (lemma_pats tl)
in (_118_884)::_118_883))
end
| _53_1556 -> begin
[]
end))
in (let _53_1595 = (match ((let _118_885 = (FStar_Absyn_Util.compress_typ t)
in _118_885.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _53_1565; FStar_Absyn_Syntax.pos = _53_1563; FStar_Absyn_Syntax.fvs = _53_1561; FStar_Absyn_Syntax.uvs = _53_1559}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _53_1584)::(FStar_Util.Inl (post), _53_1579)::(FStar_Util.Inr (pats), _53_1574)::[] -> begin
(let _118_886 = (lemma_pats pats)
in (binders, pre, post, _118_886))
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
(let _53_1618 = (let _118_888 = (FStar_All.pipe_right patterns (FStar_List.map (fun _53_12 -> (match (_53_12) with
| (FStar_Util.Inl (t), _53_1607) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _53_1612) -> begin
(encode_exp e (let _53_1614 = env
in {bindings = _53_1614.bindings; depth = _53_1614.depth; tcenv = _53_1614.tcenv; warn = _53_1614.warn; cache = _53_1614.cache; nolabels = _53_1614.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1614.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _118_888 FStar_List.unzip))
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
(let _118_890 = (let _118_889 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _118_889 e))
in (_118_890)::pats)
end
| _53_1626 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(let _118_895 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_118_895)::pats)
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _118_897 = (let _118_896 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _118_896 tl))
in (aux _118_897 vars))
end
| _53_1637 -> begin
pats
end))
in (let _118_898 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _118_898 vars)))
end)
end)
in (let env = (let _53_1639 = env
in {bindings = _53_1639.bindings; depth = _53_1639.depth; tcenv = _53_1639.tcenv; warn = _53_1639.warn; cache = _53_1639.cache; nolabels = true; use_zfuel_name = _53_1639.use_zfuel_name; encode_non_total_function_typ = _53_1639.encode_non_total_function_typ})
in (let _53_1644 = (let _118_899 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _118_899 env))
in (match (_53_1644) with
| (pre, decls'') -> begin
(let _53_1647 = (let _118_900 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _118_900 env))
in (match (_53_1647) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _118_905 = (let _118_904 = (let _118_903 = (let _118_902 = (let _118_901 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_118_901, post))
in (FStar_ToSMT_Term.mkImp _118_902))
in (pats, vars, _118_903))
in (FStar_ToSMT_Term.mkForall _118_904))
in (_118_905, decls)))
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
(let _118_923 = (f args)
in (_118_923, [], decls))
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
(let _118_939 = (f phis)
in (_118_939, labs, decls))
end))))
in (let const_op = (fun f _53_1691 -> (f, [], []))
in (let un_op = (fun f l -> (let _118_953 = (FStar_List.hd l)
in (FStar_All.pipe_left f _118_953)))
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
(let _118_967 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_118_967, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
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
in (let unboxInt_l = (fun f l -> (let _118_979 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _118_979)))
in (let connectives = (let _118_1040 = (let _118_988 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _118_988))
in (let _118_1039 = (let _118_1038 = (let _118_994 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _118_994))
in (let _118_1037 = (let _118_1036 = (let _118_1035 = (let _118_1003 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _118_1003))
in (let _118_1034 = (let _118_1033 = (let _118_1032 = (let _118_1012 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _118_1012))
in (let _118_1031 = (let _118_1030 = (let _118_1018 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _118_1018))
in (_118_1030)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_118_1032)::_118_1031))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_118_1033)
in (_118_1035)::_118_1034))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_118_1036)
in (_118_1038)::_118_1037))
in (_118_1040)::_118_1039))
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
(let lvar = (let _118_1043 = (varops.fresh "label")
in (_118_1043, FStar_ToSMT_Term.Bool_sort))
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
(let _118_1044 = (FStar_ToSMT_Term.mk_Valid tt)
in (_118_1044, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _53_1845 = (encode_binders None bs env)
in (match (_53_1845) with
| (vars, guards, env, decls, _53_1844) -> begin
(let _53_1861 = (let _118_1054 = (FStar_All.pipe_right ps (FStar_List.map (fun _53_17 -> (match (_53_17) with
| (FStar_Util.Inl (t), _53_1850) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _53_1855) -> begin
(encode_exp e (let _53_1857 = env
in {bindings = _53_1857.bindings; depth = _53_1857.depth; tcenv = _53_1857.tcenv; warn = _53_1857.warn; cache = _53_1857.cache; nolabels = _53_1857.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1857.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _118_1054 FStar_List.unzip))
in (match (_53_1861) with
| (pats, decls') -> begin
(let _53_1865 = (encode_formula_with_labels body env)
in (match (_53_1865) with
| (body, labs, decls'') -> begin
(let _118_1055 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _118_1055, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _53_1866 = (match ((FStar_Tc_Env.debug env.tcenv FStar_Options.Low)) with
| true -> begin
(let _118_1056 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.fprint1 ">>>> Destructing as formula ... %s\n" _118_1056))
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
(let _118_1073 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.fprint1 ">>>> Got QALL [%s]\n" _118_1073))
end
| false -> begin
()
end)
in (let _53_1899 = (encode_q_body env vars pats body)
in (match (_53_1899) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _118_1076 = (let _118_1075 = (let _118_1074 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _118_1074))
in (FStar_ToSMT_Term.mkForall _118_1075))
in (_118_1076, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(let _53_1912 = (encode_q_body env vars pats body)
in (match (_53_1912) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _118_1079 = (let _118_1078 = (let _118_1077 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _118_1077))
in (FStar_ToSMT_Term.mkExists _118_1078))
in (_118_1079, labs, decls))
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
in (let quant = (fun vars body -> (fun x -> (let t1 = (let _118_1122 = (let _118_1121 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _118_1121))
in (FStar_ToSMT_Term.mkApp _118_1122))
in (let vname_decl = (let _118_1124 = (let _118_1123 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _118_1123, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_118_1124))
in (let _118_1130 = (let _118_1129 = (let _118_1128 = (let _118_1127 = (let _118_1126 = (let _118_1125 = (FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _118_1125))
in (FStar_ToSMT_Term.mkForall _118_1126))
in (_118_1127, None))
in FStar_ToSMT_Term.Assume (_118_1128))
in (_118_1129)::[])
in (vname_decl)::_118_1130)))))
in (let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _118_1290 = (let _118_1139 = (let _118_1138 = (let _118_1137 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1137))
in (quant axy _118_1138))
in (FStar_Absyn_Const.op_Eq, _118_1139))
in (let _118_1289 = (let _118_1288 = (let _118_1146 = (let _118_1145 = (let _118_1144 = (let _118_1143 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _118_1143))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1144))
in (quant axy _118_1145))
in (FStar_Absyn_Const.op_notEq, _118_1146))
in (let _118_1287 = (let _118_1286 = (let _118_1155 = (let _118_1154 = (let _118_1153 = (let _118_1152 = (let _118_1151 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1150 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1151, _118_1150)))
in (FStar_ToSMT_Term.mkLT _118_1152))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1153))
in (quant xy _118_1154))
in (FStar_Absyn_Const.op_LT, _118_1155))
in (let _118_1285 = (let _118_1284 = (let _118_1164 = (let _118_1163 = (let _118_1162 = (let _118_1161 = (let _118_1160 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1159 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1160, _118_1159)))
in (FStar_ToSMT_Term.mkLTE _118_1161))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1162))
in (quant xy _118_1163))
in (FStar_Absyn_Const.op_LTE, _118_1164))
in (let _118_1283 = (let _118_1282 = (let _118_1173 = (let _118_1172 = (let _118_1171 = (let _118_1170 = (let _118_1169 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1168 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1169, _118_1168)))
in (FStar_ToSMT_Term.mkGT _118_1170))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1171))
in (quant xy _118_1172))
in (FStar_Absyn_Const.op_GT, _118_1173))
in (let _118_1281 = (let _118_1280 = (let _118_1182 = (let _118_1181 = (let _118_1180 = (let _118_1179 = (let _118_1178 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1177 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1178, _118_1177)))
in (FStar_ToSMT_Term.mkGTE _118_1179))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1180))
in (quant xy _118_1181))
in (FStar_Absyn_Const.op_GTE, _118_1182))
in (let _118_1279 = (let _118_1278 = (let _118_1191 = (let _118_1190 = (let _118_1189 = (let _118_1188 = (let _118_1187 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1186 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1187, _118_1186)))
in (FStar_ToSMT_Term.mkSub _118_1188))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1189))
in (quant xy _118_1190))
in (FStar_Absyn_Const.op_Subtraction, _118_1191))
in (let _118_1277 = (let _118_1276 = (let _118_1198 = (let _118_1197 = (let _118_1196 = (let _118_1195 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _118_1195))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1196))
in (quant qx _118_1197))
in (FStar_Absyn_Const.op_Minus, _118_1198))
in (let _118_1275 = (let _118_1274 = (let _118_1207 = (let _118_1206 = (let _118_1205 = (let _118_1204 = (let _118_1203 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1202 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1203, _118_1202)))
in (FStar_ToSMT_Term.mkAdd _118_1204))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1205))
in (quant xy _118_1206))
in (FStar_Absyn_Const.op_Addition, _118_1207))
in (let _118_1273 = (let _118_1272 = (let _118_1216 = (let _118_1215 = (let _118_1214 = (let _118_1213 = (let _118_1212 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1211 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1212, _118_1211)))
in (FStar_ToSMT_Term.mkMul _118_1213))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1214))
in (quant xy _118_1215))
in (FStar_Absyn_Const.op_Multiply, _118_1216))
in (let _118_1271 = (let _118_1270 = (let _118_1225 = (let _118_1224 = (let _118_1223 = (let _118_1222 = (let _118_1221 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1220 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1221, _118_1220)))
in (FStar_ToSMT_Term.mkDiv _118_1222))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1223))
in (quant xy _118_1224))
in (FStar_Absyn_Const.op_Division, _118_1225))
in (let _118_1269 = (let _118_1268 = (let _118_1234 = (let _118_1233 = (let _118_1232 = (let _118_1231 = (let _118_1230 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1229 = (FStar_ToSMT_Term.unboxInt y)
in (_118_1230, _118_1229)))
in (FStar_ToSMT_Term.mkMod _118_1231))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _118_1232))
in (quant xy _118_1233))
in (FStar_Absyn_Const.op_Modulus, _118_1234))
in (let _118_1267 = (let _118_1266 = (let _118_1243 = (let _118_1242 = (let _118_1241 = (let _118_1240 = (let _118_1239 = (FStar_ToSMT_Term.unboxBool x)
in (let _118_1238 = (FStar_ToSMT_Term.unboxBool y)
in (_118_1239, _118_1238)))
in (FStar_ToSMT_Term.mkAnd _118_1240))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1241))
in (quant xy _118_1242))
in (FStar_Absyn_Const.op_And, _118_1243))
in (let _118_1265 = (let _118_1264 = (let _118_1252 = (let _118_1251 = (let _118_1250 = (let _118_1249 = (let _118_1248 = (FStar_ToSMT_Term.unboxBool x)
in (let _118_1247 = (FStar_ToSMT_Term.unboxBool y)
in (_118_1248, _118_1247)))
in (FStar_ToSMT_Term.mkOr _118_1249))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1250))
in (quant xy _118_1251))
in (FStar_Absyn_Const.op_Or, _118_1252))
in (let _118_1263 = (let _118_1262 = (let _118_1259 = (let _118_1258 = (let _118_1257 = (let _118_1256 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _118_1256))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_1257))
in (quant qx _118_1258))
in (FStar_Absyn_Const.op_Negation, _118_1259))
in (_118_1262)::[])
in (_118_1264)::_118_1263))
in (_118_1266)::_118_1265))
in (_118_1268)::_118_1267))
in (_118_1270)::_118_1269))
in (_118_1272)::_118_1271))
in (_118_1274)::_118_1273))
in (_118_1276)::_118_1275))
in (_118_1278)::_118_1277))
in (_118_1280)::_118_1279))
in (_118_1282)::_118_1281))
in (_118_1284)::_118_1283))
in (_118_1286)::_118_1285))
in (_118_1288)::_118_1287))
in (_118_1290)::_118_1289))
in (let mk = (fun l v -> (let _118_1322 = (FStar_All.pipe_right prims (FStar_List.filter (fun _53_1944 -> (match (_53_1944) with
| (l', _53_1943) -> begin
(FStar_Absyn_Syntax.lid_equals l l')
end))))
in (FStar_All.pipe_right _118_1322 (FStar_List.collect (fun _53_1948 -> (match (_53_1948) with
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
in (let _118_1354 = (let _118_1345 = (let _118_1344 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_118_1344, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_118_1345))
in (let _118_1353 = (let _118_1352 = (let _118_1351 = (let _118_1350 = (let _118_1349 = (let _118_1348 = (let _118_1347 = (let _118_1346 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _118_1346))
in (FStar_ToSMT_Term.mkImp _118_1347))
in ((typing_pred)::[], (xx)::[], _118_1348))
in (mkForall_fuel _118_1349))
in (_118_1350, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_118_1351))
in (_118_1352)::[])
in (_118_1354)::_118_1353))))
in (let mk_bool = (fun _53_1965 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _118_1374 = (let _118_1364 = (let _118_1363 = (let _118_1362 = (let _118_1361 = (let _118_1360 = (let _118_1359 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _118_1359))
in (FStar_ToSMT_Term.mkImp _118_1360))
in ((typing_pred)::[], (xx)::[], _118_1361))
in (mkForall_fuel _118_1362))
in (_118_1363, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_118_1364))
in (let _118_1373 = (let _118_1372 = (let _118_1371 = (let _118_1370 = (let _118_1369 = (let _118_1368 = (let _118_1365 = (FStar_ToSMT_Term.boxBool b)
in (_118_1365)::[])
in (let _118_1367 = (let _118_1366 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _118_1366 tt))
in (_118_1368, (bb)::[], _118_1367)))
in (FStar_ToSMT_Term.mkForall _118_1369))
in (_118_1370, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_118_1371))
in (_118_1372)::[])
in (_118_1374)::_118_1373))))))
in (let mk_int = (fun _53_1972 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _118_1386 = (let _118_1385 = (let _118_1384 = (let _118_1383 = (let _118_1382 = (let _118_1381 = (FStar_ToSMT_Term.boxInt a)
in (let _118_1380 = (let _118_1379 = (FStar_ToSMT_Term.boxInt b)
in (_118_1379)::[])
in (_118_1381)::_118_1380))
in (tt)::_118_1382)
in (tt)::_118_1383)
in ("Prims.Precedes", _118_1384))
in (FStar_ToSMT_Term.mkApp _118_1385))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _118_1386))
in (let precedes_y_x = (let _118_1387 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _118_1387))
in (let _118_1428 = (let _118_1393 = (let _118_1392 = (let _118_1391 = (let _118_1390 = (let _118_1389 = (let _118_1388 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _118_1388))
in (FStar_ToSMT_Term.mkImp _118_1389))
in ((typing_pred)::[], (xx)::[], _118_1390))
in (mkForall_fuel _118_1391))
in (_118_1392, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_118_1393))
in (let _118_1427 = (let _118_1426 = (let _118_1400 = (let _118_1399 = (let _118_1398 = (let _118_1397 = (let _118_1394 = (FStar_ToSMT_Term.boxInt b)
in (_118_1394)::[])
in (let _118_1396 = (let _118_1395 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _118_1395 tt))
in (_118_1397, (bb)::[], _118_1396)))
in (FStar_ToSMT_Term.mkForall _118_1398))
in (_118_1399, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_118_1400))
in (let _118_1425 = (let _118_1424 = (let _118_1423 = (let _118_1422 = (let _118_1421 = (let _118_1420 = (let _118_1419 = (let _118_1418 = (let _118_1417 = (let _118_1416 = (let _118_1415 = (let _118_1414 = (let _118_1403 = (let _118_1402 = (FStar_ToSMT_Term.unboxInt x)
in (let _118_1401 = (FStar_ToSMT_Term.mkInteger' 0)
in (_118_1402, _118_1401)))
in (FStar_ToSMT_Term.mkGT _118_1403))
in (let _118_1413 = (let _118_1412 = (let _118_1406 = (let _118_1405 = (FStar_ToSMT_Term.unboxInt y)
in (let _118_1404 = (FStar_ToSMT_Term.mkInteger' 0)
in (_118_1405, _118_1404)))
in (FStar_ToSMT_Term.mkGTE _118_1406))
in (let _118_1411 = (let _118_1410 = (let _118_1409 = (let _118_1408 = (FStar_ToSMT_Term.unboxInt y)
in (let _118_1407 = (FStar_ToSMT_Term.unboxInt x)
in (_118_1408, _118_1407)))
in (FStar_ToSMT_Term.mkLT _118_1409))
in (_118_1410)::[])
in (_118_1412)::_118_1411))
in (_118_1414)::_118_1413))
in (typing_pred_y)::_118_1415)
in (typing_pred)::_118_1416)
in (FStar_ToSMT_Term.mk_and_l _118_1417))
in (_118_1418, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _118_1419))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _118_1420))
in (mkForall_fuel _118_1421))
in (_118_1422, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_118_1423))
in (_118_1424)::[])
in (_118_1426)::_118_1425))
in (_118_1428)::_118_1427)))))))))))
in (let mk_int_alias = (fun _53_1984 tt -> (let _118_1437 = (let _118_1436 = (let _118_1435 = (let _118_1434 = (let _118_1433 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Absyn_Syntax.str, []))
in (tt, _118_1433))
in (FStar_ToSMT_Term.mkEq _118_1434))
in (_118_1435, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_118_1436))
in (_118_1437)::[]))
in (let mk_str = (fun _53_1988 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.String_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _118_1457 = (let _118_1447 = (let _118_1446 = (let _118_1445 = (let _118_1444 = (let _118_1443 = (let _118_1442 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _118_1442))
in (FStar_ToSMT_Term.mkImp _118_1443))
in ((typing_pred)::[], (xx)::[], _118_1444))
in (mkForall_fuel _118_1445))
in (_118_1446, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_118_1447))
in (let _118_1456 = (let _118_1455 = (let _118_1454 = (let _118_1453 = (let _118_1452 = (let _118_1451 = (let _118_1448 = (FStar_ToSMT_Term.boxString b)
in (_118_1448)::[])
in (let _118_1450 = (let _118_1449 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _118_1449 tt))
in (_118_1451, (bb)::[], _118_1450)))
in (FStar_ToSMT_Term.mkForall _118_1452))
in (_118_1453, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_118_1454))
in (_118_1455)::[])
in (_118_1457)::_118_1456))))))
in (let mk_ref = (fun reft_name _53_1996 -> (let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let refa = (let _118_1464 = (let _118_1463 = (let _118_1462 = (FStar_ToSMT_Term.mkFreeV aa)
in (_118_1462)::[])
in (reft_name, _118_1463))
in (FStar_ToSMT_Term.mkApp _118_1464))
in (let refb = (let _118_1467 = (let _118_1466 = (let _118_1465 = (FStar_ToSMT_Term.mkFreeV bb)
in (_118_1465)::[])
in (reft_name, _118_1466))
in (FStar_ToSMT_Term.mkApp _118_1467))
in (let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _118_1486 = (let _118_1473 = (let _118_1472 = (let _118_1471 = (let _118_1470 = (let _118_1469 = (let _118_1468 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _118_1468))
in (FStar_ToSMT_Term.mkImp _118_1469))
in ((typing_pred)::[], (xx)::(aa)::[], _118_1470))
in (mkForall_fuel _118_1471))
in (_118_1472, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_118_1473))
in (let _118_1485 = (let _118_1484 = (let _118_1483 = (let _118_1482 = (let _118_1481 = (let _118_1480 = (let _118_1479 = (let _118_1478 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _118_1477 = (let _118_1476 = (let _118_1475 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _118_1474 = (FStar_ToSMT_Term.mkFreeV bb)
in (_118_1475, _118_1474)))
in (FStar_ToSMT_Term.mkEq _118_1476))
in (_118_1478, _118_1477)))
in (FStar_ToSMT_Term.mkImp _118_1479))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _118_1480))
in (mkForall_fuel' 2 _118_1481))
in (_118_1482, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_118_1483))
in (_118_1484)::[])
in (_118_1486)::_118_1485))))))))))
in (let mk_false_interp = (fun _53_2006 false_tm -> (let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _118_1493 = (let _118_1492 = (let _118_1491 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_118_1491, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_118_1492))
in (_118_1493)::[])))
in (let mk_and_interp = (fun conj _53_2012 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1500 = (let _118_1499 = (let _118_1498 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_118_1498)::[])
in ("Valid", _118_1499))
in (FStar_ToSMT_Term.mkApp _118_1500))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1507 = (let _118_1506 = (let _118_1505 = (let _118_1504 = (let _118_1503 = (let _118_1502 = (let _118_1501 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_118_1501, valid))
in (FStar_ToSMT_Term.mkIff _118_1502))
in ((valid)::[], (aa)::(bb)::[], _118_1503))
in (FStar_ToSMT_Term.mkForall _118_1504))
in (_118_1505, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_118_1506))
in (_118_1507)::[])))))))))
in (let mk_or_interp = (fun disj _53_2023 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1514 = (let _118_1513 = (let _118_1512 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_118_1512)::[])
in ("Valid", _118_1513))
in (FStar_ToSMT_Term.mkApp _118_1514))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1521 = (let _118_1520 = (let _118_1519 = (let _118_1518 = (let _118_1517 = (let _118_1516 = (let _118_1515 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_118_1515, valid))
in (FStar_ToSMT_Term.mkIff _118_1516))
in ((valid)::[], (aa)::(bb)::[], _118_1517))
in (FStar_ToSMT_Term.mkForall _118_1518))
in (_118_1519, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_118_1520))
in (_118_1521)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _118_1528 = (let _118_1527 = (let _118_1526 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_118_1526)::[])
in ("Valid", _118_1527))
in (FStar_ToSMT_Term.mkApp _118_1528))
in (let _118_1535 = (let _118_1534 = (let _118_1533 = (let _118_1532 = (let _118_1531 = (let _118_1530 = (let _118_1529 = (FStar_ToSMT_Term.mkEq (x, y))
in (_118_1529, valid))
in (FStar_ToSMT_Term.mkIff _118_1530))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _118_1531))
in (FStar_ToSMT_Term.mkForall _118_1532))
in (_118_1533, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_118_1534))
in (_118_1535)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1542 = (let _118_1541 = (let _118_1540 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_118_1540)::[])
in ("Valid", _118_1541))
in (FStar_ToSMT_Term.mkApp _118_1542))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1549 = (let _118_1548 = (let _118_1547 = (let _118_1546 = (let _118_1545 = (let _118_1544 = (let _118_1543 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_118_1543, valid))
in (FStar_ToSMT_Term.mkIff _118_1544))
in ((valid)::[], (aa)::(bb)::[], _118_1545))
in (FStar_ToSMT_Term.mkForall _118_1546))
in (_118_1547, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_118_1548))
in (_118_1549)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1556 = (let _118_1555 = (let _118_1554 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_118_1554)::[])
in ("Valid", _118_1555))
in (FStar_ToSMT_Term.mkApp _118_1556))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _118_1563 = (let _118_1562 = (let _118_1561 = (let _118_1560 = (let _118_1559 = (let _118_1558 = (let _118_1557 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_118_1557, valid))
in (FStar_ToSMT_Term.mkIff _118_1558))
in ((valid)::[], (aa)::(bb)::[], _118_1559))
in (FStar_ToSMT_Term.mkForall _118_1560))
in (_118_1561, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_118_1562))
in (_118_1563)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _118_1570 = (let _118_1569 = (let _118_1568 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_118_1568)::[])
in ("Valid", _118_1569))
in (FStar_ToSMT_Term.mkApp _118_1570))
in (let valid_b_x = (let _118_1573 = (let _118_1572 = (let _118_1571 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_118_1571)::[])
in ("Valid", _118_1572))
in (FStar_ToSMT_Term.mkApp _118_1573))
in (let _118_1586 = (let _118_1585 = (let _118_1584 = (let _118_1583 = (let _118_1582 = (let _118_1581 = (let _118_1580 = (let _118_1579 = (let _118_1578 = (let _118_1574 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1574)::[])
in (let _118_1577 = (let _118_1576 = (let _118_1575 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1575, valid_b_x))
in (FStar_ToSMT_Term.mkImp _118_1576))
in (_118_1578, (xx)::[], _118_1577)))
in (FStar_ToSMT_Term.mkForall _118_1579))
in (_118_1580, valid))
in (FStar_ToSMT_Term.mkIff _118_1581))
in ((valid)::[], (aa)::(bb)::[], _118_1582))
in (FStar_ToSMT_Term.mkForall _118_1583))
in (_118_1584, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_118_1585))
in (_118_1586)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _118_1593 = (let _118_1592 = (let _118_1591 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_118_1591)::[])
in ("Valid", _118_1592))
in (FStar_ToSMT_Term.mkApp _118_1593))
in (let valid_b_x = (let _118_1596 = (let _118_1595 = (let _118_1594 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_118_1594)::[])
in ("Valid", _118_1595))
in (FStar_ToSMT_Term.mkApp _118_1596))
in (let _118_1609 = (let _118_1608 = (let _118_1607 = (let _118_1606 = (let _118_1605 = (let _118_1604 = (let _118_1603 = (let _118_1602 = (let _118_1601 = (let _118_1597 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1597)::[])
in (let _118_1600 = (let _118_1599 = (let _118_1598 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_118_1598, valid_b_x))
in (FStar_ToSMT_Term.mkImp _118_1599))
in (_118_1601, (xx)::[], _118_1600)))
in (FStar_ToSMT_Term.mkExists _118_1602))
in (_118_1603, valid))
in (FStar_ToSMT_Term.mkIff _118_1604))
in ((valid)::[], (aa)::(bb)::[], _118_1605))
in (FStar_ToSMT_Term.mkForall _118_1606))
in (_118_1607, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_118_1608))
in (_118_1609)::[]))))))))))
in (let mk_foralltyp_interp = (fun for_all tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1616 = (let _118_1615 = (let _118_1614 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_118_1614)::[])
in ("Valid", _118_1615))
in (FStar_ToSMT_Term.mkApp _118_1616))
in (let valid_a_b = (let _118_1619 = (let _118_1618 = (let _118_1617 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_118_1617)::[])
in ("Valid", _118_1618))
in (FStar_ToSMT_Term.mkApp _118_1619))
in (let _118_1632 = (let _118_1631 = (let _118_1630 = (let _118_1629 = (let _118_1628 = (let _118_1627 = (let _118_1626 = (let _118_1625 = (let _118_1624 = (let _118_1620 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1620)::[])
in (let _118_1623 = (let _118_1622 = (let _118_1621 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1621, valid_a_b))
in (FStar_ToSMT_Term.mkImp _118_1622))
in (_118_1624, (bb)::[], _118_1623)))
in (FStar_ToSMT_Term.mkForall _118_1625))
in (_118_1626, valid))
in (FStar_ToSMT_Term.mkIff _118_1627))
in ((valid)::[], (kk)::(aa)::[], _118_1628))
in (FStar_ToSMT_Term.mkForall _118_1629))
in (_118_1630, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_118_1631))
in (_118_1632)::[]))))))))))
in (let mk_existstyp_interp = (fun for_some tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _118_1639 = (let _118_1638 = (let _118_1637 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_118_1637)::[])
in ("Valid", _118_1638))
in (FStar_ToSMT_Term.mkApp _118_1639))
in (let valid_a_b = (let _118_1642 = (let _118_1641 = (let _118_1640 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_118_1640)::[])
in ("Valid", _118_1641))
in (FStar_ToSMT_Term.mkApp _118_1642))
in (let _118_1655 = (let _118_1654 = (let _118_1653 = (let _118_1652 = (let _118_1651 = (let _118_1650 = (let _118_1649 = (let _118_1648 = (let _118_1647 = (let _118_1643 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1643)::[])
in (let _118_1646 = (let _118_1645 = (let _118_1644 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_118_1644, valid_a_b))
in (FStar_ToSMT_Term.mkImp _118_1645))
in (_118_1647, (bb)::[], _118_1646)))
in (FStar_ToSMT_Term.mkExists _118_1648))
in (_118_1649, valid))
in (FStar_ToSMT_Term.mkIff _118_1650))
in ((valid)::[], (kk)::(aa)::[], _118_1651))
in (FStar_ToSMT_Term.mkForall _118_1652))
in (_118_1653, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_118_1654))
in (_118_1655)::[]))))))))))
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
(let _118_1798 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.fprint1 ">>>>Encoding [%s]\n") _118_1798))
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
(let _118_1801 = (let _118_1800 = (let _118_1799 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_118_1799))
in (_118_1800)::[])
in (_118_1801, e))
end
| _53_2136 -> begin
(let _118_1808 = (let _118_1807 = (let _118_1803 = (let _118_1802 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_118_1802))
in (_118_1803)::g)
in (let _118_1806 = (let _118_1805 = (let _118_1804 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_118_1804))
in (_118_1805)::[])
in (FStar_List.append _118_1807 _118_1806)))
in (_118_1808, e))
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
in (let valid_b2t_x = (let _118_1813 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (FStar_ToSMT_Term.mk_Valid _118_1813))
in (let decls = (let _118_1821 = (let _118_1820 = (let _118_1819 = (let _118_1818 = (let _118_1817 = (let _118_1816 = (let _118_1815 = (let _118_1814 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _118_1814))
in (FStar_ToSMT_Term.mkEq _118_1815))
in ((valid_b2t_x)::[], (xx)::[], _118_1816))
in (FStar_ToSMT_Term.mkForall _118_1817))
in (_118_1818, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_118_1819))
in (_118_1820)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_118_1821)
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
(let tok_app = (let _118_1822 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _118_1822 vars))
in (let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _118_1824 = (let _118_1823 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _118_1823))
in (FStar_ToSMT_Term.mkApp _118_1824))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _53_2224 -> begin
(let _118_1826 = (let _118_1825 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _118_1825))
in (_118_1826)::[])
end)
in (let decls = (let _118_1837 = (let _118_1830 = (let _118_1829 = (let _118_1828 = (let _118_1827 = (FStar_List.map Prims.snd vars)
in (tname, _118_1827, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_118_1828))
in (_118_1829)::(tok_decl)::[])
in (FStar_List.append _118_1830 fresh_tok))
in (let _118_1836 = (let _118_1835 = (let _118_1834 = (let _118_1833 = (let _118_1832 = (let _118_1831 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _118_1831))
in (FStar_ToSMT_Term.mkForall _118_1832))
in (_118_1833, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_118_1834))
in (_118_1835)::[])
in (FStar_List.append _118_1837 _118_1836)))
in (let t = (whnf env t)
in (let _53_2236 = (match ((FStar_All.pipe_right tags (FStar_Util.for_some (fun _53_18 -> (match (_53_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _53_2231 -> begin
false
end))))) with
| true -> begin
(let _118_1840 = (FStar_ToSMT_Term.mk_Valid app)
in (let _118_1839 = (encode_formula t env')
in (_118_1840, _118_1839)))
end
| false -> begin
(let _118_1841 = (encode_typ_term t env')
in (app, _118_1841))
end)
in (match (_53_2236) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _118_1848 = (let _118_1847 = (let _118_1846 = (let _118_1845 = (let _118_1844 = (let _118_1843 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _118_1842 = (FStar_ToSMT_Term.mkEq (def, body))
in (_118_1843, _118_1842)))
in (FStar_ToSMT_Term.mkImp _118_1844))
in ((def)::[], vars, _118_1845))
in (FStar_ToSMT_Term.mkForall _118_1846))
in (_118_1847, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_118_1848))
in (let kindingAx = (let _53_2240 = (let _118_1849 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _118_1849 env' app))
in (match (_53_2240) with
| (k, decls) -> begin
(let _118_1857 = (let _118_1856 = (let _118_1855 = (let _118_1854 = (let _118_1853 = (let _118_1852 = (let _118_1851 = (let _118_1850 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_1850, k))
in (FStar_ToSMT_Term.mkImp _118_1851))
in ((app)::[], vars, _118_1852))
in (FStar_ToSMT_Term.mkForall _118_1853))
in (_118_1854, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_118_1855))
in (_118_1856)::[])
in (FStar_List.append decls _118_1857))
end))
in (let g = (let _118_1858 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _118_1858))
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
(let _118_1860 = (let _118_1859 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _118_1859))
in (_118_1860, env))
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
(let g = (let _118_1865 = (let _118_1864 = (let _118_1863 = (let _118_1862 = (let _118_1861 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _118_1861))
in Some (_118_1862))
in (f, _118_1863))
in FStar_ToSMT_Term.Assume (_118_1864))
in (_118_1865)::[])
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
in (let _118_1867 = (let _118_1866 = (primitive_type_axioms t tname tsym)
in (decl)::_118_1866)
in (_118_1867, (push_free_tvar env t tname (Some (tsym))))))))
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
(let _118_1873 = (let _118_1872 = (let _118_1871 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _118_1871, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_118_1872))
in (_118_1873)::[])
end))
end
| false -> begin
(FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun tapp vars -> (match ((((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _118_1879 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _118_1879 FStar_Option.isNone))))))) with
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
(let indices = (match ((let _118_1882 = (FStar_Absyn_Util.compress_typ res)
in _118_1882.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_53_2346, indices) -> begin
indices
end
| _53_2351 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _118_1887 = (let _118_1886 = (let _118_1885 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_118_1885, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _118_1886))
in (push_typ_var env a.FStar_Absyn_Syntax.v _118_1887))
end
| FStar_Util.Inr (x) -> begin
(let _118_1890 = (let _118_1889 = (let _118_1888 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_118_1888, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _118_1889))
in (push_term_var env x.FStar_Absyn_Syntax.v _118_1890))
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
in (let eqs = (let _118_1897 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _118_1894 = (let _118_1893 = (FStar_ToSMT_Term.mkFreeV v)
in (_118_1893, a))
in (FStar_ToSMT_Term.mkEq _118_1894))
end
| FStar_Util.Inr (a) -> begin
(let _118_1896 = (let _118_1895 = (FStar_ToSMT_Term.mkFreeV v)
in (_118_1895, a))
in (FStar_ToSMT_Term.mkEq _118_1896))
end)) vars indices)
in (FStar_All.pipe_right _118_1897 FStar_ToSMT_Term.mk_and_l))
in (let _118_1902 = (let _118_1901 = (let _118_1900 = (let _118_1899 = (let _118_1898 = (mk_data_tester env l xx)
in (_118_1898, eqs))
in (FStar_ToSMT_Term.mkAnd _118_1899))
in (out, _118_1900))
in (FStar_ToSMT_Term.mkOr _118_1901))
in (_118_1902, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_53_2374) with
| (data_ax, decls) -> begin
(let _53_2377 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2377) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _118_1903 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _118_1903 xx tapp))
in (let _118_1910 = (let _118_1909 = (let _118_1908 = (let _118_1907 = (let _118_1906 = (let _118_1905 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _118_1904 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _118_1905, _118_1904)))
in (FStar_ToSMT_Term.mkForall _118_1906))
in (_118_1907, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_118_1908))
in (_118_1909)::[])
in (FStar_List.append decls _118_1910)))
end))
end))
end))
end))
in (let k = (FStar_Absyn_Util.close_kind tps k)
in (let _53_2389 = (match ((let _118_1911 = (FStar_Absyn_Util.compress_kind k)
in _118_1911.FStar_Absyn_Syntax.n)) with
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
(let dproj_app = (let _118_1925 = (let _118_1924 = (let _118_1923 = (mk_typ_projector_name d a)
in (let _118_1922 = (let _118_1921 = (FStar_ToSMT_Term.mkFreeV xx)
in (_118_1921)::[])
in (_118_1923, _118_1922)))
in (FStar_ToSMT_Term.mkApp _118_1924))
in (mk_ApplyT _118_1925 suffix))
in (let _118_1930 = (let _118_1929 = (let _118_1928 = (let _118_1927 = (let _118_1926 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _118_1926))
in (FStar_ToSMT_Term.mkForall _118_1927))
in (_118_1928, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_118_1929))
in (_118_1930)::[]))
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
in (let _118_1943 = (let _118_1942 = (let _118_1941 = (let _118_1940 = (let _118_1939 = (let _118_1938 = (let _118_1937 = (let _118_1936 = (let _118_1935 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _118_1935))
in (FStar_ToSMT_Term.mkEq _118_1936))
in (xx_has_type, _118_1937))
in (FStar_ToSMT_Term.mkImp _118_1938))
in ((xx_has_type)::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _118_1939))
in (FStar_ToSMT_Term.mkForall _118_1940))
in (_118_1941, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_118_1942))
in (_118_1943)::[]))
end))
end)))
in (let _53_2452 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2452) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _118_1945 = (let _118_1944 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _118_1944))
in (FStar_ToSMT_Term.mkApp _118_1945))
in (let _53_2477 = (let tname_decl = (let _118_1949 = (let _118_1948 = (FStar_All.pipe_right vars (FStar_List.map (fun _53_2458 -> (match (_53_2458) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _118_1947 = (varops.next_id ())
in (tname, _118_1948, FStar_ToSMT_Term.Type_sort, _118_1947)))
in (constructor_or_logic_type_decl _118_1949))
in (let _53_2474 = (match (vars) with
| [] -> begin
(let _118_1953 = (let _118_1952 = (let _118_1951 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _118_1950 -> Some (_118_1950)) _118_1951))
in (push_free_tvar env t tname _118_1952))
in ([], _118_1953))
end
| _53_2462 -> begin
(let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _118_1954 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _118_1954))
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
in (let name_tok_corr = (let _118_1959 = (let _118_1958 = (let _118_1957 = (let _118_1956 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _118_1956))
in (FStar_ToSMT_Term.mkForall' _118_1957))
in (_118_1958, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_118_1959))
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
(let _118_1963 = (let _118_1962 = (let _118_1961 = (let _118_1960 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _118_1960))
in (_118_1961, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_118_1962))
in (_118_1963)::[])
end
| false -> begin
[]
end)
in (let _118_1969 = (let _118_1968 = (let _118_1967 = (let _118_1966 = (let _118_1965 = (let _118_1964 = (FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _118_1964))
in (FStar_ToSMT_Term.mkForall _118_1965))
in (_118_1966, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_118_1967))
in (_118_1968)::[])
in (FStar_List.append (FStar_List.append decls karr) _118_1969)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _118_1970 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _118_1970))
end
| false -> begin
(let _118_1977 = (let _118_1975 = (let _118_1973 = (let _118_1971 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _118_1971))
in (let _118_1972 = (inversion_axioms tapp vars)
in (FStar_List.append _118_1973 _118_1972)))
in (let _118_1974 = (projection_axioms tapp vars)
in (FStar_List.append _118_1975 _118_1974)))
in (let _118_1976 = (pretype_axioms tapp vars)
in (FStar_List.append _118_1977 _118_1976)))
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
(let _118_1979 = (mk_typ_projector_name d a)
in (_118_1979, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _118_1980 = (mk_term_projector_name d x)
in (_118_1980, FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _118_1982 = (let _118_1981 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _118_1981))
in (FStar_All.pipe_right _118_1982 FStar_ToSMT_Term.constructor_to_decl))
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
(let _118_1984 = (let _118_1983 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _118_1983))
in (_118_1984)::[])
end)
in (let encode_elim = (fun _53_2563 -> (match (()) with
| () -> begin
(let _53_2566 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_53_2566) with
| (head, args) -> begin
(match ((let _118_1987 = (FStar_Absyn_Util.compress_typ head)
in _118_1987.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _53_2572 = (encode_args args env')
in (match (_53_2572) with
| (encoded_args, arg_decls) -> begin
(let _53_2596 = (FStar_List.fold_left (fun _53_2576 arg -> (match (_53_2576) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(let _53_2584 = (let _118_1990 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _118_1990))
in (match (_53_2584) with
| (_53_2581, tv, env) -> begin
(let _118_1992 = (let _118_1991 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_118_1991)::eqns)
in (env, (tv)::arg_vars, _118_1992))
end))
end
| FStar_Util.Inr (varg) -> begin
(let _53_2591 = (let _118_1993 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _118_1993))
in (match (_53_2591) with
| (_53_2588, xv, env) -> begin
(let _118_1995 = (let _118_1994 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_118_1994)::eqns)
in (env, (xv)::arg_vars, _118_1995))
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
in (let typing_inversion = (let _118_2002 = (let _118_2001 = (let _118_2000 = (let _118_1999 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _118_1998 = (let _118_1997 = (let _118_1996 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _118_1996))
in (FStar_ToSMT_Term.mkImp _118_1997))
in ((ty_pred)::[], _118_1999, _118_1998)))
in (FStar_ToSMT_Term.mkForall _118_2000))
in (_118_2001, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_118_2002))
in (let subterm_ordering = (match ((FStar_Absyn_Syntax.lid_equals d FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _118_2003 = (varops.fresh "x")
in (_118_2003, FStar_ToSMT_Term.Term_sort))
in (let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _118_2012 = (let _118_2011 = (let _118_2010 = (let _118_2009 = (let _118_2004 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_118_2004)::[])
in (let _118_2008 = (let _118_2007 = (let _118_2006 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _118_2005 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_118_2006, _118_2005)))
in (FStar_ToSMT_Term.mkImp _118_2007))
in (_118_2009, (x)::[], _118_2008)))
in (FStar_ToSMT_Term.mkForall _118_2010))
in (_118_2011, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_118_2012))))
end
| false -> begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _118_2015 = (let _118_2014 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _118_2014 dapp))
in (_118_2015)::[])
end
| _53_2611 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _118_2022 = (let _118_2021 = (let _118_2020 = (let _118_2019 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _118_2018 = (let _118_2017 = (let _118_2016 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _118_2016))
in (FStar_ToSMT_Term.mkImp _118_2017))
in ((ty_pred)::[], _118_2019, _118_2018)))
in (FStar_ToSMT_Term.mkForall _118_2020))
in (_118_2021, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_118_2022)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _53_2615 -> begin
(let _53_2616 = (let _118_2025 = (let _118_2024 = (FStar_Absyn_Print.sli d)
in (let _118_2023 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _118_2024 _118_2023)))
in (FStar_Tc_Errors.warn drange _118_2025))
in ([], []))
end)
end))
end))
in (let _53_2620 = (encode_elim ())
in (match (_53_2620) with
| (decls2, elim) -> begin
(let g = (let _118_2050 = (let _118_2049 = (let _118_2034 = (let _118_2033 = (let _118_2032 = (let _118_2031 = (let _118_2030 = (let _118_2029 = (let _118_2028 = (let _118_2027 = (let _118_2026 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _118_2026))
in Some (_118_2027))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _118_2028))
in FStar_ToSMT_Term.DeclFun (_118_2029))
in (_118_2030)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _118_2031))
in (FStar_List.append _118_2032 proxy_fresh))
in (FStar_List.append _118_2033 decls_formals))
in (FStar_List.append _118_2034 decls_pred))
in (let _118_2048 = (let _118_2047 = (let _118_2046 = (let _118_2038 = (let _118_2037 = (let _118_2036 = (let _118_2035 = (FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _118_2035))
in (FStar_ToSMT_Term.mkForall _118_2036))
in (_118_2037, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_118_2038))
in (let _118_2045 = (let _118_2044 = (let _118_2043 = (let _118_2042 = (let _118_2041 = (let _118_2040 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _118_2039 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _118_2040, _118_2039)))
in (FStar_ToSMT_Term.mkForall _118_2041))
in (_118_2042, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_118_2043))
in (_118_2044)::[])
in (_118_2046)::_118_2045))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_118_2047)
in (FStar_List.append _118_2049 _118_2048)))
in (FStar_List.append _118_2050 elim))
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
(let _118_2065 = (let _118_2064 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _118_2064))
in FStar_Util.Inl (_118_2065))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _118_2067 = (let _118_2066 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _118_2066))
in FStar_Util.Inr (_118_2067))
end
| _53_2705 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _118_2068 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _118_2068 FStar_Absyn_Util.name_binders))
in (let body = (let _118_2074 = (let _118_2070 = (let _118_2069 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _118_2069))
in (body, _118_2070))
in (let _118_2073 = (let _118_2072 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _118_2071 -> Some (_118_2071)) _118_2072))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _118_2074 _118_2073 body.FStar_Absyn_Syntax.pos)))
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
(let _118_2083 = (let _118_2082 = (FStar_Absyn_Print.exp_to_string e)
in (let _118_2081 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Absyn_Syntax.str _118_2082 _118_2081)))
in (FStar_All.failwith _118_2083))
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
(let _118_2089 = (FStar_All.pipe_right bindings (FStar_List.collect (fun lb -> (match ((FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _118_2088 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _118_2088 lb.FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(Prims.raise Let_rec_unencodeable)
end))))
in (_118_2089, env))
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
in (let t_norm = (let _118_2092 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _118_2092 FStar_Absyn_Util.compress_typ))
in (let _53_2794 = (let _118_2093 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _118_2093 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_53_2794) with
| (tok, decl, env) -> begin
(let _118_2096 = (let _118_2095 = (let _118_2094 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_118_2094, tok))
in (_118_2095)::toks)
in (_118_2096, (t_norm)::typs, (decl)::decls, env))
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
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _118_2099 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _118_2099)))))))) with
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
(let _118_2101 = (let _118_2100 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _118_2100))
in (FStar_ToSMT_Term.mkApp _118_2101))
end)
in (let _53_2844 = (encode_exp body env')
in (match (_53_2844) with
| (body, decls2) -> begin
(let eqn = (let _118_2110 = (let _118_2109 = (let _118_2106 = (let _118_2105 = (let _118_2104 = (let _118_2103 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _118_2102 = (FStar_ToSMT_Term.mkEq (app, body))
in (_118_2103, _118_2102)))
in (FStar_ToSMT_Term.mkImp _118_2104))
in ((app)::[], vars, _118_2105))
in (FStar_ToSMT_Term.mkForall _118_2106))
in (let _118_2108 = (let _118_2107 = (FStar_Util.format1 "Equation for %s" flid.FStar_Absyn_Syntax.str)
in Some (_118_2107))
in (_118_2109, _118_2108)))
in FStar_ToSMT_Term.Assume (_118_2110))
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
(let fuel = (let _118_2111 = (varops.fresh "fuel")
in (_118_2111, FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _53_2864 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _53_2853 _53_2858 -> (match ((_53_2853, _53_2858)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _118_2116 = (let _118_2115 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _118_2114 -> Some (_118_2114)) _118_2115))
in (push_free_var env flid gtok _118_2116))
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
(let decl_g = (let _118_2127 = (let _118_2126 = (let _118_2125 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_118_2125)
in (g, _118_2126, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_118_2127))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _118_2130 = (let _118_2129 = (let _118_2128 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_118_2128)::vars_tm)
in (g, _118_2129))
in (FStar_ToSMT_Term.mkApp _118_2130))
in (let gmax = (let _118_2133 = (let _118_2132 = (let _118_2131 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_118_2131)::vars_tm)
in (g, _118_2132))
in (FStar_ToSMT_Term.mkApp _118_2133))
in (let _53_2904 = (encode_exp body env')
in (match (_53_2904) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _118_2142 = (let _118_2141 = (let _118_2138 = (let _118_2137 = (let _118_2136 = (let _118_2135 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _118_2134 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_118_2135, _118_2134)))
in (FStar_ToSMT_Term.mkImp _118_2136))
in ((gsapp)::[], (fuel)::vars, _118_2137))
in (FStar_ToSMT_Term.mkForall _118_2138))
in (let _118_2140 = (let _118_2139 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Absyn_Syntax.str)
in Some (_118_2139))
in (_118_2141, _118_2140)))
in FStar_ToSMT_Term.Assume (_118_2142))
in (let eqn_f = (let _118_2146 = (let _118_2145 = (let _118_2144 = (let _118_2143 = (FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _118_2143))
in (FStar_ToSMT_Term.mkForall _118_2144))
in (_118_2145, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_118_2146))
in (let eqn_g' = (let _118_2155 = (let _118_2154 = (let _118_2153 = (let _118_2152 = (let _118_2151 = (let _118_2150 = (let _118_2149 = (let _118_2148 = (let _118_2147 = (FStar_ToSMT_Term.n_fuel 0)
in (_118_2147)::vars_tm)
in (g, _118_2148))
in (FStar_ToSMT_Term.mkApp _118_2149))
in (gsapp, _118_2150))
in (FStar_ToSMT_Term.mkEq _118_2151))
in ((gsapp)::[], (fuel)::vars, _118_2152))
in (FStar_ToSMT_Term.mkForall _118_2153))
in (_118_2154, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_118_2155))
in (let _53_2927 = (let _53_2914 = (encode_binders None formals env0)
in (match (_53_2914) with
| (vars, v_guards, env, binder_decls, _53_2913) -> begin
(let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _118_2156 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _118_2156 ((fuel)::vars)))
in (let _118_2160 = (let _118_2159 = (let _118_2158 = (let _118_2157 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _118_2157))
in (FStar_ToSMT_Term.mkForall _118_2158))
in (_118_2159, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_118_2160)))
in (let _53_2924 = (let _53_2921 = (encode_typ_pred None tres env gapp)
in (match (_53_2921) with
| (g_typing, d3) -> begin
(let _118_2168 = (let _118_2167 = (let _118_2166 = (let _118_2165 = (let _118_2164 = (let _118_2163 = (let _118_2162 = (let _118_2161 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_118_2161, g_typing))
in (FStar_ToSMT_Term.mkImp _118_2162))
in ((gapp)::[], (fuel)::vars, _118_2163))
in (FStar_ToSMT_Term.mkForall _118_2164))
in (_118_2165, None))
in FStar_ToSMT_Term.Assume (_118_2166))
in (_118_2167)::[])
in (d3, _118_2168))
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
in (let _53_2943 = (let _118_2171 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _53_2931 _53_2935 -> (match ((_53_2931, _53_2935)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _53_2939 = (encode_one_binding env0 gtok ty bs)
in (match (_53_2939) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _118_2171))
in (match (_53_2943) with
| (decls, eqns, env0) -> begin
(let _53_2952 = (let _118_2173 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _118_2173 (FStar_List.partition (fun _53_29 -> (match (_53_29) with
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
(let msg = (let _118_2176 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _118_2176 (FStar_String.concat " and ")))
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
and encode_free_var = (fun env lid tt t_norm quals -> (match (((let _118_2189 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _118_2189)) || (FStar_Absyn_Util.is_lemma t_norm))) with
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
(let _118_2191 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _118_2191))
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
in (let _118_2208 = (let _118_2207 = (let _118_2206 = (let _118_2205 = (let _118_2204 = (let _118_2203 = (let _118_2202 = (let _118_2201 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Absyn_Syntax.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _118_2201))
in (vapp, _118_2202))
in (FStar_ToSMT_Term.mkEq _118_2203))
in ((vapp)::[], vars, _118_2204))
in (FStar_ToSMT_Term.mkForall _118_2205))
in (_118_2206, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_118_2207))
in (_118_2208)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(let _53_3074 = (FStar_Util.prefix vars)
in (match (_53_3074) with
| (_53_3069, (xxsym, _53_3072)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _118_2210 = (let _118_2209 = (mk_term_projector_name d f)
in (_118_2209, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _118_2210))
in (let _118_2215 = (let _118_2214 = (let _118_2213 = (let _118_2212 = (let _118_2211 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in ((vapp)::[], vars, _118_2211))
in (FStar_ToSMT_Term.mkForall _118_2212))
in (_118_2213, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_118_2214))
in (_118_2215)::[])))
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
(let _118_2216 = (FStar_ToSMT_Term.mk_and_l guards)
in (_118_2216, decls1))
end
| Some (p) -> begin
(let _53_3091 = (encode_formula p env')
in (match (_53_3091) with
| (g, ds) -> begin
(let _118_2217 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_118_2217, (FStar_List.append decls1 ds)))
end))
end)
in (match (_53_3094) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _118_2219 = (let _118_2218 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _118_2218))
in (FStar_ToSMT_Term.mkApp _118_2219))
in (let _53_3125 = (let vname_decl = (let _118_2222 = (let _118_2221 = (FStar_All.pipe_right formals (FStar_List.map (fun _53_32 -> (match (_53_32) with
| (FStar_Util.Inl (_53_3099), _53_3102) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3105 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _118_2221, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_118_2222))
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
(let _118_2226 = (let _118_2225 = (let _118_2224 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _118_2223 -> Some (_118_2223)) _118_2224))
in (push_free_var env lid vname _118_2225))
in ((FStar_List.append decls2 ((tok_typing)::[])), _118_2226))
end
| _53_3116 -> begin
(let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _118_2227 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _118_2227))
in (let name_tok_corr = (let _118_2231 = (let _118_2230 = (let _118_2229 = (let _118_2228 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _118_2228))
in (FStar_ToSMT_Term.mkForall _118_2229))
in (_118_2230, None))
in FStar_ToSMT_Term.Assume (_118_2231))
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
(let _118_2232 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _118_2232, decls))
end)))
in (match (_53_3133) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _118_2236 = (let _118_2235 = (let _118_2234 = (let _118_2233 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _118_2233))
in (FStar_ToSMT_Term.mkForall _118_2234))
in (_118_2235, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_118_2236))
in (let g = (let _118_2238 = (let _118_2237 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_118_2237)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _118_2238))
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
(let _118_2253 = (FStar_Absyn_Print.strBvd x)
in (let _118_2252 = (FStar_Absyn_Print.typ_to_string t0)
in (let _118_2251 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.fprint3 "Normalized %s : %s to %s\n" _118_2253 _118_2252 _118_2251))))
end
| false -> begin
()
end)
in (let _53_3165 = (encode_typ_pred None t1 env xx)
in (match (_53_3165) with
| (t, decls') -> begin
(let caption = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(let _118_2257 = (let _118_2256 = (FStar_Absyn_Print.strBvd x)
in (let _118_2255 = (FStar_Absyn_Print.typ_to_string t0)
in (let _118_2254 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _118_2256 _118_2255 _118_2254))))
in Some (_118_2257))
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
(let g = (let _118_2263 = (let _118_2262 = (let _118_2261 = (let _118_2260 = (let _118_2259 = (let _118_2258 = (FStar_Absyn_Print.strBvd a)
in Some (_118_2258))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _118_2259))
in FStar_ToSMT_Term.DeclFun (_118_2260))
in (_118_2261)::[])
in (FStar_List.append _118_2262 decls'))
in (FStar_List.append _118_2263 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
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
(let _118_2271 = (FStar_All.pipe_left (fun _118_2267 -> FStar_ToSMT_Term.Echo (_118_2267)) (Prims.fst l))
in (let _118_2270 = (let _118_2269 = (let _118_2268 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_118_2268))
in (_118_2269)::[])
in (_118_2271)::_118_2270))
end))))
in (prefix, suffix))))

let last_env = (FStar_Util.mk_ref [])

let init_env = (fun tcenv -> (let _118_2276 = (let _118_2275 = (let _118_2274 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _118_2274; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_118_2275)::[])
in (FStar_ST.op_Colon_Equals last_env _118_2276)))

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

let pop = (fun msg -> (let _53_3260 = (let _118_2297 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _118_2297))
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
(let _118_2311 = (let _118_2310 = (let _118_2309 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _118_2309))
in FStar_ToSMT_Term.Caption (_118_2310))
in (_118_2311)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _53_3286 = (encode_sigelt env se)
in (match (_53_3286) with
| (decls, env) -> begin
(let _53_3287 = (set_env env)
in (let _118_2312 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _118_2312)))
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
(let _118_2317 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.fprint2 "Encoding externals for %s ... %s exports\n" name _118_2317))
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

let solve = (fun tcenv q -> (let _53_3312 = (let _118_2326 = (let _118_2325 = (let _118_2324 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _118_2324))
in (FStar_Util.format1 "Starting query at %s" _118_2325))
in (push _118_2326))
in (let pop = (fun _53_3315 -> (match (()) with
| () -> begin
(let _118_2331 = (let _118_2330 = (let _118_2329 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _118_2329))
in (FStar_Util.format1 "Ending query at %s" _118_2330))
in (pop _118_2331))
end))
in (let _53_3345 = (let env = (get_env tcenv)
in (let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _53_3328 = (let _118_2335 = (FStar_List.filter (fun _53_33 -> (match (_53_33) with
| FStar_Tc_Env.Binding_sig (_53_3322) -> begin
false
end
| _53_3325 -> begin
true
end)) bindings)
in (encode_env_bindings env _118_2335))
in (match (_53_3328) with
| (env_decls, env) -> begin
(let _53_3329 = (match ((FStar_Tc_Env.debug tcenv FStar_Options.Low)) with
| true -> begin
(let _118_2336 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.fprint1 "Encoding query formula: %s\n" _118_2336))
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
in (let qry = (let _118_2338 = (let _118_2337 = (FStar_ToSMT_Term.mkNot phi)
in (_118_2337, Some ("query")))
in FStar_ToSMT_Term.Assume (_118_2338))
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
(let _118_2361 = (let _118_2360 = (let _118_2345 = (let _118_2344 = (FStar_Util.string_of_int n)
in (let _118_2343 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _118_2344 _118_2343)))
in FStar_ToSMT_Term.Caption (_118_2345))
in (let _118_2359 = (let _118_2358 = (let _118_2350 = (let _118_2349 = (let _118_2348 = (let _118_2347 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _118_2346 = (FStar_ToSMT_Term.n_fuel n)
in (_118_2347, _118_2346)))
in (FStar_ToSMT_Term.mkEq _118_2348))
in (_118_2349, None))
in FStar_ToSMT_Term.Assume (_118_2350))
in (let _118_2357 = (let _118_2356 = (let _118_2355 = (let _118_2354 = (let _118_2353 = (let _118_2352 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _118_2351 = (FStar_ToSMT_Term.n_fuel i)
in (_118_2352, _118_2351)))
in (FStar_ToSMT_Term.mkEq _118_2353))
in (_118_2354, None))
in FStar_ToSMT_Term.Assume (_118_2355))
in (_118_2356)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_118_2358)::_118_2357))
in (_118_2360)::_118_2359))
in (FStar_List.append _118_2361 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _118_2365 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _118_2364 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_118_2365, _118_2364)))
in (let alt_configs = (let _118_2384 = (let _118_2383 = (match (((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) with
| true -> begin
(let _118_2368 = (let _118_2367 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _118_2366 = (FStar_ST.read FStar_Options.max_ifuel)
in (_118_2367, _118_2366)))
in (_118_2368)::[])
end
| false -> begin
[]
end)
in (let _118_2382 = (let _118_2381 = (match ((((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel))) with
| true -> begin
(let _118_2371 = (let _118_2370 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _118_2369 = (FStar_ST.read FStar_Options.max_ifuel)
in (_118_2370, _118_2369)))
in (_118_2371)::[])
end
| false -> begin
[]
end)
in (let _118_2380 = (let _118_2379 = (match ((((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)))) with
| true -> begin
(let _118_2374 = (let _118_2373 = (FStar_ST.read FStar_Options.max_fuel)
in (let _118_2372 = (FStar_ST.read FStar_Options.max_ifuel)
in (_118_2373, _118_2372)))
in (_118_2374)::[])
end
| false -> begin
[]
end)
in (let _118_2378 = (let _118_2377 = (match (((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel))) with
| true -> begin
(let _118_2376 = (let _118_2375 = (FStar_ST.read FStar_Options.min_fuel)
in (_118_2375, 1))
in (_118_2376)::[])
end
| false -> begin
[]
end)
in (_118_2377)::[])
in (_118_2379)::_118_2378))
in (_118_2381)::_118_2380))
in (_118_2383)::_118_2382))
in (FStar_List.flatten _118_2384))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _53_3387 -> begin
errs
end)
in (let _53_3389 = (match ((FStar_ST.read FStar_Options.print_fuels)) with
| true -> begin
(let _118_2392 = (let _118_2387 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _118_2387))
in (let _118_2391 = (let _118_2388 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _118_2388 FStar_Util.string_of_int))
in (let _118_2390 = (let _118_2389 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _118_2389 FStar_Util.string_of_int))
in (FStar_Util.fprint3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _118_2392 _118_2391 _118_2390))))
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
(let _118_2403 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _118_2403 (cb mi p [])))
end
| _53_3401 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _118_2405 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _118_2405 (fun _53_3407 -> (match (_53_3407) with
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
(let _118_2413 = (let _118_2410 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _118_2410))
in (let _118_2412 = (FStar_Util.string_of_int prev_fuel)
in (let _118_2411 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.fprint3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _118_2413 _118_2412 _118_2411))))
end
| false -> begin
()
end)
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _118_2414 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _118_2414 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> (match (((FStar_ST.read FStar_Options.split_cases) > 0)) with
| true -> begin
(let _53_3423 = (let _118_2420 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _118_2420 q))
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





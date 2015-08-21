
let add_fuel = (fun ( x ) ( tl ) -> (match ((Support.ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
tl
end
| false -> begin
(x)::tl
end))

let withenv = (fun ( c ) ( _52_40 ) -> (match (_52_40) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun ( args ) -> (Support.List.filter (fun ( _52_1 ) -> (match (_52_1) with
| (Support.Microsoft.FStar.Util.Inl (_52_44), _52_47) -> begin
false
end
| _52_50 -> begin
true
end)) args))

let escape = (fun ( s ) -> (Support.Microsoft.FStar.Util.replace_char s '\'' '_'))

let escape_null_name = (fun ( a ) -> (match ((a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = "_")) with
| true -> begin
(Support.String.strcat a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)
end
| false -> begin
a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end))

let mk_typ_projector_name = (fun ( lid ) ( a ) -> (let _116_14 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _116_14)))

let mk_term_projector_name = (fun ( lid ) ( a ) -> (let a = (let _116_19 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _116_19; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _116_20 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _116_20))))

let primitive_projector_by_pos = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _52_62 ) -> (match (()) with
| () -> begin
(let _116_30 = (let _116_29 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" _116_29 lid.Microsoft_FStar_Absyn_Syntax.str))
in (Support.All.failwith _116_30))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _116_31 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _116_31.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _52_66)) -> begin
(match (((i < 0) || (i >= (Support.List.length binders)))) with
| true -> begin
(fail ())
end
| false -> begin
(let b = (Support.List.nth binders i)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(mk_typ_projector_name lid a.Microsoft_FStar_Absyn_Syntax.v)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(mk_term_projector_name lid x.Microsoft_FStar_Absyn_Syntax.v)
end))
end)
end
| _52_75 -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun ( lid ) ( i ) -> (let _116_37 = (let _116_36 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _116_36))
in (Support.All.pipe_left escape _116_37)))

let mk_typ_projector = (fun ( lid ) ( a ) -> (let _116_43 = (let _116_42 = (mk_typ_projector_name lid a)
in (_116_42, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _116_43)))

let mk_term_projector = (fun ( lid ) ( a ) -> (let _116_49 = (let _116_48 = (mk_term_projector_name lid a)
in (_116_48, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _116_49)))

let mk_term_projector_by_pos = (fun ( lid ) ( i ) -> (let _116_55 = (let _116_54 = (mk_term_projector_name_by_pos lid i)
in (_116_54, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _116_55)))

let mk_data_tester = (fun ( env ) ( l ) ( x ) -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let is_Mkvarops_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun ( _52_101 ) -> (match (()) with
| () -> begin
(let _116_159 = (Support.Microsoft.FStar.Util.smap_create 100)
in (let _116_158 = (Support.Microsoft.FStar.Util.smap_create 100)
in (_116_159, _116_158)))
end))
in (let scopes = (let _116_161 = (let _116_160 = (new_scope ())
in (_116_160)::[])
in (Support.Microsoft.FStar.Util.mk_ref _116_161))
in (let mk_unique = (fun ( y ) -> (let y = (escape y)
in (let y = (match ((let _116_165 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _116_165 (fun ( _52_109 ) -> (match (_52_109) with
| (names, _52_108) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_52_112) -> begin
(let _52_114 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _116_167 = (let _116_166 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _116_166))
in (Support.String.strcat (Support.String.strcat y "__") _116_167)))
end)
in (let top_scope = (let _116_169 = (let _116_168 = (Support.ST.read scopes)
in (Support.List.hd _116_168))
in (Support.All.pipe_left Support.Prims.fst _116_169))
in (let _52_118 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun ( pp ) ( rn ) -> (let _116_175 = (let _116_174 = (Support.All.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.String.strcat _116_174 "__"))
in (Support.String.strcat _116_175 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun ( lid ) -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun ( _52_126 ) -> (match (()) with
| () -> begin
(let _52_127 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
end))
in (let fresh = (fun ( pfx ) -> (let _116_183 = (let _116_182 = (next_id ())
in (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int _116_182))
in (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx _116_183)))
in (let string_const = (fun ( s ) -> (match ((let _116_187 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _116_187 (fun ( _52_136 ) -> (match (_52_136) with
| (_52_134, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _116_188 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxString _116_188))
in (let top_scope = (let _116_190 = (let _116_189 = (Support.ST.read scopes)
in (Support.List.hd _116_189))
in (Support.All.pipe_left Support.Prims.snd _116_190))
in (let _52_143 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun ( _52_146 ) -> (match (()) with
| () -> begin
(let _116_195 = (let _116_194 = (new_scope ())
in (let _116_193 = (Support.ST.read scopes)
in (_116_194)::_116_193))
in (Support.ST.op_Colon_Equals scopes _116_195))
end))
in (let pop = (fun ( _52_148 ) -> (match (()) with
| () -> begin
(let _116_199 = (let _116_198 = (Support.ST.read scopes)
in (Support.List.tl _116_198))
in (Support.ST.op_Colon_Equals scopes _116_199))
end))
in (let mark = (fun ( _52_150 ) -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun ( _52_152 ) -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun ( _52_154 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _52_167 = (Support.Microsoft.FStar.Util.smap_fold hd1 (fun ( key ) ( value ) ( v ) -> (Support.Microsoft.FStar.Util.smap_add next1 key value)) ())
in (let _52_172 = (Support.Microsoft.FStar.Util.smap_fold hd2 (fun ( key ) ( value ) ( v ) -> (Support.Microsoft.FStar.Util.smap_add next2 key value)) ())
in (Support.ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _52_175 -> begin
(Support.All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun ( x ) -> (let _116_215 = (let _116_214 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _116_213 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_116_214, _116_213)))
in (Microsoft_FStar_Absyn_Util.mkbvd _116_215)))

type binding =
| Binding_var of (Microsoft_FStar_Absyn_Syntax.bvvdef * Microsoft_FStar_ToSMT_Term.term)
| Binding_tvar of (Microsoft_FStar_Absyn_Syntax.btvdef * Microsoft_FStar_ToSMT_Term.term)
| Binding_fvar of (Microsoft_FStar_Absyn_Syntax.lident * string * Microsoft_FStar_ToSMT_Term.term option * Microsoft_FStar_ToSMT_Term.term option)
| Binding_ftvar of (Microsoft_FStar_Absyn_Syntax.lident * string * Microsoft_FStar_ToSMT_Term.term option)

let is_Binding_var = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_tvar = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_tvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_fvar = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_ftvar = (fun ( _discr_ ) -> (match (_discr_) with
| Binding_ftvar (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_var____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_var (_52_180) -> begin
_52_180
end))

let ___Binding_tvar____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_tvar (_52_183) -> begin
_52_183
end))

let ___Binding_fvar____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_fvar (_52_186) -> begin
_52_186
end))

let ___Binding_ftvar____0 = (fun ( projectee ) -> (match (projectee) with
| Binding_ftvar (_52_189) -> begin
_52_189
end))

let binder_of_eithervar = (fun ( v ) -> (v, None))

type env_t =
{bindings : binding list; depth : int; tcenv : Microsoft_FStar_Tc_Env.env; warn : bool; cache : (string * Microsoft_FStar_ToSMT_Term.sort list * Microsoft_FStar_ToSMT_Term.decl list) Support.Microsoft.FStar.Util.smap; nolabels : bool; use_zfuel_name : bool; encode_non_total_function_typ : bool}

let is_Mkenv_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkenv_t"))

let print_env = (fun ( e ) -> (let _116_301 = (Support.All.pipe_right e.bindings (Support.List.map (fun ( _52_2 ) -> (match (_52_2) with
| Binding_var ((x, t)) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Binding_tvar ((a, t)) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Binding_fvar ((l, s, t, _52_214)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| Binding_ftvar ((l, s, t)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end))))
in (Support.All.pipe_right _116_301 (Support.String.concat ", "))))

let lookup_binding = (fun ( env ) ( f ) -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun ( env ) ( t ) -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _116_311 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_116_311))
end
| false -> begin
None
end))

let fresh_fvar = (fun ( x ) ( s ) -> (let xsym = (varops.fresh x)
in (let _116_316 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _116_316))))

let gen_term_var = (fun ( env ) ( x ) -> (let ysym = (let _116_321 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@x" _116_321))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _52_233 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _52_233.tcenv; warn = _52_233.warn; cache = _52_233.cache; nolabels = _52_233.nolabels; use_zfuel_name = _52_233.use_zfuel_name; encode_non_total_function_typ = _52_233.encode_non_total_function_typ})))))

let new_term_constant = (fun ( env ) ( x ) -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _52_239 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _52_239.depth; tcenv = _52_239.tcenv; warn = _52_239.warn; cache = _52_239.cache; nolabels = _52_239.nolabels; use_zfuel_name = _52_239.use_zfuel_name; encode_non_total_function_typ = _52_239.encode_non_total_function_typ})))))

let push_term_var = (fun ( env ) ( x ) ( t ) -> (let _52_244 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _52_244.depth; tcenv = _52_244.tcenv; warn = _52_244.warn; cache = _52_244.cache; nolabels = _52_244.nolabels; use_zfuel_name = _52_244.use_zfuel_name; encode_non_total_function_typ = _52_244.encode_non_total_function_typ}))

let lookup_term_var = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_3 ) -> (match (_52_3) with
| Binding_var ((b, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _52_254 -> begin
None
end)))) with
| None -> begin
(let _116_336 = (let _116_335 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" _116_335))
in (Support.All.failwith _116_336))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun ( env ) ( x ) -> (let ysym = (let _116_341 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@a" _116_341))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _52_264 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _52_264.tcenv; warn = _52_264.warn; cache = _52_264.cache; nolabels = _52_264.nolabels; use_zfuel_name = _52_264.use_zfuel_name; encode_non_total_function_typ = _52_264.encode_non_total_function_typ})))))

let new_typ_constant = (fun ( env ) ( x ) -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _52_270 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _52_270.depth; tcenv = _52_270.tcenv; warn = _52_270.warn; cache = _52_270.cache; nolabels = _52_270.nolabels; use_zfuel_name = _52_270.use_zfuel_name; encode_non_total_function_typ = _52_270.encode_non_total_function_typ})))))

let push_typ_var = (fun ( env ) ( x ) ( t ) -> (let _52_275 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _52_275.depth; tcenv = _52_275.tcenv; warn = _52_275.warn; cache = _52_275.cache; nolabels = _52_275.nolabels; use_zfuel_name = _52_275.use_zfuel_name; encode_non_total_function_typ = _52_275.encode_non_total_function_typ}))

let lookup_typ_var = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_4 ) -> (match (_52_4) with
| Binding_tvar ((b, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _52_285 -> begin
None
end)))) with
| None -> begin
(let _116_356 = (let _116_355 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" _116_355))
in (Support.All.failwith _116_356))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _116_367 = (let _52_295 = env
in (let _116_366 = (let _116_365 = (let _116_364 = (let _116_363 = (let _116_362 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _116_361 ) -> Some (_116_361)) _116_362))
in (x, fname, _116_363, None))
in Binding_fvar (_116_364))
in (_116_365)::env.bindings)
in {bindings = _116_366; depth = _52_295.depth; tcenv = _52_295.tcenv; warn = _52_295.warn; cache = _52_295.cache; nolabels = _52_295.nolabels; use_zfuel_name = _52_295.use_zfuel_name; encode_non_total_function_typ = _52_295.encode_non_total_function_typ}))
in (fname, ftok, _116_367)))))

let try_lookup_lid = (fun ( env ) ( a ) -> (lookup_binding env (fun ( _52_5 ) -> (match (_52_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _52_307 -> begin
None
end))))

let lookup_lid = (fun ( env ) ( a ) -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _116_378 = (let _116_377 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _116_377))
in (Support.All.failwith _116_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _52_317.depth; tcenv = _52_317.tcenv; warn = _52_317.warn; cache = _52_317.cache; nolabels = _52_317.nolabels; use_zfuel_name = _52_317.use_zfuel_name; encode_non_total_function_typ = _52_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun ( env ) ( x ) ( f ) -> (let _52_326 = (lookup_lid env x)
in (match (_52_326) with
| (t1, t2, _52_325) -> begin
(let t3 = (let _116_395 = (let _116_394 = (let _116_393 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_116_393)::[])
in (f, _116_394))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_395))
in (let _52_328 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _52_328.depth; tcenv = _52_328.tcenv; warn = _52_328.warn; cache = _52_328.cache; nolabels = _52_328.nolabels; use_zfuel_name = _52_328.use_zfuel_name; encode_non_total_function_typ = _52_328.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun ( env ) ( a ) -> (let _52_335 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_335) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _52_339 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((_52_343, fuel::[])) -> begin
(match ((let _116_399 = (let _116_398 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (Support.All.pipe_right _116_398 Support.Prims.fst))
in (Support.Microsoft.FStar.Util.starts_with _116_399 "fuel"))) with
| true -> begin
(let _116_400 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _116_400 fuel))
end
| false -> begin
t
end)
end
| _52_349 -> begin
t
end)
end
| _52_351 -> begin
(let _116_402 = (let _116_401 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _116_401))
in (Support.All.failwith _116_402))
end)
end)
end)))

let lookup_free_var_name = (fun ( env ) ( a ) -> (let _52_359 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_359) with
| (x, _52_356, _52_358) -> begin
x
end)))

let lookup_free_var_sym = (fun ( env ) ( a ) -> (let _52_365 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_365) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((g, zf)); Microsoft_FStar_ToSMT_Term.hash = _52_369; Microsoft_FStar_ToSMT_Term.freevars = _52_367}) when env.use_zfuel_name -> begin
(g, zf)
end
| _52_377 -> begin
(match (sym) with
| None -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((g, fuel::[])) -> begin
(g, (fuel)::[])
end
| _52_387 -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _116_417 = (let _52_392 = env
in (let _116_416 = (let _116_415 = (let _116_414 = (let _116_413 = (let _116_412 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _116_411 ) -> Some (_116_411)) _116_412))
in (x, fname, _116_413))
in Binding_ftvar (_116_414))
in (_116_415)::env.bindings)
in {bindings = _116_416; depth = _52_392.depth; tcenv = _52_392.tcenv; warn = _52_392.warn; cache = _52_392.cache; nolabels = _52_392.nolabels; use_zfuel_name = _52_392.use_zfuel_name; encode_non_total_function_typ = _52_392.encode_non_total_function_typ}))
in (fname, ftok, _116_417)))))

let lookup_tlid = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_6 ) -> (match (_52_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _52_403 -> begin
None
end)))) with
| None -> begin
(let _116_424 = (let _116_423 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _116_423))
in (Support.All.failwith _116_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _52_411.depth; tcenv = _52_411.tcenv; warn = _52_411.warn; cache = _52_411.cache; nolabels = _52_411.nolabels; use_zfuel_name = _52_411.use_zfuel_name; encode_non_total_function_typ = _52_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun ( env ) ( a ) -> (match ((let _116_435 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _116_435 Support.Prims.snd))) with
| None -> begin
(let _116_437 = (let _116_436 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _116_436))
in (Support.All.failwith _116_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun ( env ) ( a ) -> (let _116_440 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _116_440 Support.Prims.fst)))

let tok_of_name = (fun ( env ) ( nm ) -> (Support.Microsoft.FStar.Util.find_map env.bindings (fun ( _52_7 ) -> (match (_52_7) with
| (Binding_fvar ((_, nm', tok, _))) | (Binding_ftvar ((_, nm', tok))) when (nm = nm') -> begin
tok
end
| _52_436 -> begin
None
end))))

let mkForall_fuel' = (fun ( n ) ( _52_441 ) -> (match (_52_441) with
| (pats, vars, body) -> begin
(let fallback = (fun ( _52_443 ) -> (match (()) with
| () -> begin
(Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in (match ((Support.ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
(fallback ())
end
| false -> begin
(let _52_446 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_446) with
| (fsym, fterm) -> begin
(let add_fuel = (fun ( tms ) -> (Support.All.pipe_right tms (Support.List.map (fun ( p ) -> (match (p.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var ("HasType"), args)) -> begin
(Microsoft_FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _52_456 -> begin
p
end)))))
in (let pats = (add_fuel pats)
in (let body = (match (body.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Imp, guard::body'::[])) -> begin
(let guard = (match (guard.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.And, guards)) -> begin
(let _116_453 = (add_fuel guards)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _116_453))
end
| _52_469 -> begin
(let _116_454 = (add_fuel ((guard)::[]))
in (Support.All.pipe_right _116_454 Support.List.hd))
end)
in (Microsoft_FStar_ToSMT_Term.mkImp (guard, body')))
end
| _52_472 -> begin
body
end)
in (let vars = ((fsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars
in (Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))))))
end))
end))
end))

let mkForall_fuel = (mkForall_fuel' 1)

let head_normal = (fun ( env ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (v)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (v); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _116_460 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _116_460 Support.Option.isNone))
end
| _52_510 -> begin
false
end)))

let whnf = (fun ( env ) ( t ) -> (match ((head_normal env t)) with
| true -> begin
t
end
| false -> begin
(Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end))

let whnf_e = (fun ( env ) ( e ) -> (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))

let norm_t = (fun ( env ) ( t ) -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env.tcenv t))

let norm_k = (fun ( env ) ( k ) -> (Microsoft_FStar_Tc_Normalize.normalize_kind env.tcenv k))

let trivial_post = (fun ( t ) -> (let _116_482 = (let _116_481 = (let _116_479 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_116_479)::[])
in (let _116_480 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_116_481, _116_480)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _116_482 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun ( e ) ( vars ) -> (Support.All.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _116_489 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _116_489))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _116_490 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _116_490))
end
| _52_527 -> begin
(let _116_491 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _116_491))
end)) e)))

let mk_ApplyE_args = (fun ( e ) ( args ) -> (Support.All.pipe_right args (Support.List.fold_left (fun ( out ) ( arg ) -> (match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyET out t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))

let mk_ApplyT = (fun ( t ) ( vars ) -> (Support.All.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _116_504 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _116_504))
end
| _52_542 -> begin
(let _116_505 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _116_505))
end)) t)))

let mk_ApplyT_args = (fun ( t ) ( args ) -> (Support.All.pipe_right args (Support.List.fold_left (fun ( out ) ( arg ) -> (match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTT out t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))

let is_app = (fun ( _52_8 ) -> (match (_52_8) with
| (Microsoft_FStar_ToSMT_Term.Var ("ApplyTT")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyTE")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyET")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _52_561 -> begin
false
end))

let is_eta = (fun ( env ) ( vars ) ( t ) -> (let rec aux = (fun ( t ) ( xs ) -> (match ((t.Microsoft_FStar_ToSMT_Term.tm, xs)) with
| (Microsoft_FStar_ToSMT_Term.App ((app, f::{Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.FreeV (y); Microsoft_FStar_ToSMT_Term.hash = _52_572; Microsoft_FStar_ToSMT_Term.freevars = _52_570}::[])), x::xs) when ((is_app app) && (Microsoft_FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var (f), args)), _52_590) -> begin
(match ((((Support.List.length args) = (Support.List.length vars)) && (Support.List.forall2 (fun ( a ) ( v ) -> (match (a.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (fv) -> begin
(Microsoft_FStar_ToSMT_Term.fv_eq fv v)
end
| _52_597 -> begin
false
end)) args vars))) with
| true -> begin
(tok_of_name env f)
end
| false -> begin
None
end)
end
| (_52_599, []) -> begin
(let fvs = (Microsoft_FStar_ToSMT_Term.free_variables t)
in (match ((Support.All.pipe_right fvs (Support.List.for_all (fun ( fv ) -> (not ((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_ToSMT_Term.fv_eq fv) vars))))))) with
| true -> begin
Some (t)
end
| false -> begin
None
end))
end
| _52_605 -> begin
None
end))
in (aux t (Support.List.rev vars))))

type label =
(Microsoft_FStar_ToSMT_Term.fv * string * Support.Microsoft.FStar.Range.range)

type labels =
label list

type pattern =
{pat_vars : (Microsoft_FStar_Absyn_Syntax.either_var * Microsoft_FStar_ToSMT_Term.fv) list; pat_term : unit  ->  (Microsoft_FStar_ToSMT_Term.term * Microsoft_FStar_ToSMT_Term.decls_t); guard : Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term; projections : Microsoft_FStar_ToSMT_Term.term  ->  (Microsoft_FStar_Absyn_Syntax.either_var * Microsoft_FStar_ToSMT_Term.term) list}

let is_Mkpattern = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkpattern"))

exception Let_rec_unencodeable

let is_Let_rec_unencodeable = (fun ( _discr_ ) -> (match (_discr_) with
| Let_rec_unencodeable -> begin
true
end
| _ -> begin
false
end))

let encode_const = (fun ( _52_9 ) -> (match (_52_9) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
Microsoft_FStar_ToSMT_Term.mk_Term_unit
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (true) -> begin
(Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (false) -> begin
(Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkFalse)
end
| Microsoft_FStar_Absyn_Syntax.Const_char (c) -> begin
(let _116_561 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _116_561))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _116_562 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _116_562))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _116_563 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _116_563))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _116_567 = (let _116_566 = (let _116_565 = (let _116_564 = (Microsoft_FStar_ToSMT_Term.mkInteger' i)
in (Microsoft_FStar_ToSMT_Term.boxInt _116_564))
in (_116_565)::[])
in ("Int32.Int32", _116_566))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_567))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _52_627)) -> begin
(let _116_568 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_bytes bytes)
in (varops.string_const _116_568))
end
| c -> begin
(let _116_570 = (let _116_569 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" _116_569))
in (Support.All.failwith _116_570))
end))

let as_function_typ = (fun ( env ) ( t0 ) -> (let rec aux = (fun ( norm ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_52_638) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_641) -> begin
(let _116_579 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _116_579))
end
| _52_644 -> begin
(match (norm) with
| true -> begin
(let _116_580 = (whnf env t)
in (aux false _116_580))
end
| false -> begin
(let _116_583 = (let _116_582 = (Support.Microsoft.FStar.Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _116_581 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Support.Microsoft.FStar.Util.format2 "(%s) Expected a function typ; got %s" _116_582 _116_581)))
in (Support.All.failwith _116_583))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun ( k ) ( env ) -> (match ((let _116_619 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _116_619.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_52_649, k0)) -> begin
(let _52_653 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _116_621 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _116_620 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _116_621 _116_620)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _52_657)) -> begin
(let _116_623 = (let _116_622 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _116_622))
in (_116_623, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, kbody)) -> begin
(let tsym = (let _116_624 = (varops.fresh "t")
in (_116_624, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let t = (Microsoft_FStar_ToSMT_Term.mkFreeV tsym)
in (let _52_672 = (encode_binders None bs env)
in (match (_52_672) with
| (vars, guards, env', decls, _52_671) -> begin
(let app = (mk_ApplyT t vars)
in (let _52_676 = (encode_knd kbody env' app)
in (match (_52_676) with
| (kbody, decls') -> begin
(let rec aux = (fun ( app ) ( vars ) ( guards ) -> (match ((vars, guards)) with
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
| _52_695 -> begin
(let _116_633 = (let _116_632 = (let _116_631 = (Microsoft_FStar_ToSMT_Term.mk_PreKind app)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _116_631))
in (_116_632, body))
in (Microsoft_FStar_ToSMT_Term.mkAnd _116_633))
end)
in (let _116_635 = (let _116_634 = (Microsoft_FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _116_634))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_635)))))
end
| _52_698 -> begin
(Support.All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _116_637 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (Support.All.pipe_right _116_637 (Support.List.filter (fun ( _52_703 ) -> (match (_52_703) with
| (x, _52_702) -> begin
(x <> (Support.Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((k', sorts, _52_709)) -> begin
(let _116_640 = (let _116_639 = (let _116_638 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _116_638))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_639))
in (_116_640, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _116_641 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_116_641))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _116_643 = (let _116_642 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _116_642))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_643))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _116_652 = (let _116_651 = (let _116_650 = (let _116_649 = (let _116_648 = (let _116_647 = (let _116_646 = (let _116_645 = (let _116_644 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _116_644))
in (_116_645, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _116_646))
in (t_has_k, _116_647))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_648))
in ((t_has_k)::[], (tsym)::cvars, _116_649))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_650))
in (_116_651, Some ((Support.String.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_116_652))
in (let k_decls = (Support.List.append (Support.List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _52_721 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _52_724 -> begin
(let _116_654 = (let _116_653 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" _116_653))
in (Support.All.failwith _116_654))
end))
and encode_knd = (fun ( k ) ( env ) ( t ) -> (let _52_730 = (encode_knd_term k env)
in (match (_52_730) with
| (k, decls) -> begin
(let _116_658 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_116_658, decls))
end)))
and encode_binders = (fun ( fuel_opt ) ( bs ) ( env ) -> (let _52_734 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _116_662 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" _116_662))
end
| false -> begin
()
end)
in (let _52_784 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _52_741 ) ( b ) -> (match (_52_741) with
| (vars, guards, env, decls, names) -> begin
(let _52_778 = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = a; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _52_744}) -> begin
(let a = (unmangle a)
in (let _52_753 = (gen_typ_var env a)
in (match (_52_753) with
| (aasym, aa, env') -> begin
(let _52_754 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _116_666 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _116_665 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _116_666 aasym _116_665)))
end
| false -> begin
()
end)
in (let _52_758 = (encode_knd k env aa)
in (match (_52_758) with
| (guard_a_k, decls') -> begin
((aasym, Microsoft_FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', Support.Microsoft.FStar.Util.Inl (a))
end)))
end)))
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _52_760}) -> begin
(let x = (unmangle x)
in (let _52_769 = (gen_term_var env x)
in (match (_52_769) with
| (xxsym, xx, env') -> begin
(let _52_772 = (let _116_667 = (norm_t env t)
in (encode_typ_pred fuel_opt _116_667 env xx))
in (match (_52_772) with
| (guard_x_t, decls') -> begin
((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', Support.Microsoft.FStar.Util.Inr (x))
end))
end)))
end)
in (match (_52_778) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (Support.List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_52_784) with
| (vars, guards, env, decls, names) -> begin
((Support.List.rev vars), (Support.List.rev guards), env, decls, (Support.List.rev names))
end))))
and encode_typ_pred = (fun ( fuel_opt ) ( t ) ( env ) ( e ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _52_792 = (encode_typ_term t env)
in (match (_52_792) with
| (t, decls) -> begin
(let _116_672 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_116_672, decls))
end))))
and encode_typ_pred' = (fun ( fuel_opt ) ( t ) ( env ) ( e ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _52_800 = (encode_typ_term t env)
in (match (_52_800) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _116_677 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_116_677, decls))
end
| Some (f) -> begin
(let _116_678 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_116_678, decls))
end)
end))))
and encode_typ_term = (fun ( t ) ( env ) -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _116_681 = (lookup_typ_var env a)
in (_116_681, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _116_682 = (lookup_free_tvar env fv)
in (_116_682, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
(match (((env.encode_non_total_function_typ && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _52_821 = (encode_binders None binders env)
in (match (_52_821) with
| (vars, guards, env', decls, _52_820) -> begin
(let fsym = (let _116_683 = (varops.fresh "f")
in (_116_683, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _52_827 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_52_827) with
| (pre_opt, res_t) -> begin
(let _52_830 = (encode_typ_pred None res_t env' app)
in (match (_52_830) with
| (res_pred, decls') -> begin
(let _52_839 = (match (pre_opt) with
| None -> begin
(let _116_684 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_116_684, decls))
end
| Some (pre) -> begin
(let _52_836 = (encode_formula pre env')
in (match (_52_836) with
| (guard, decls0) -> begin
(let _116_685 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_116_685, (Support.List.append decls decls0)))
end))
end)
in (match (_52_839) with
| (guards, guard_decls) -> begin
(let t_interp = (let _116_687 = (let _116_686 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _116_686))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_687))
in (let cvars = (let _116_689 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (Support.All.pipe_right _116_689 (Support.List.filter (fun ( _52_844 ) -> (match (_52_844) with
| (x, _52_843) -> begin
(x <> (Support.Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _52_850)) -> begin
(let _116_692 = (let _116_691 = (let _116_690 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _116_690))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_691))
in (_116_692, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _116_693 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_116_693))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _116_695 = (let _116_694 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _116_694))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_695))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _116_697 = (let _116_696 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_116_696, Some ((Support.String.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_116_697))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _116_704 = (let _116_703 = (let _116_702 = (let _116_701 = (let _116_700 = (let _116_699 = (let _116_698 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _116_698))
in (f_has_t, _116_699))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_700))
in ((f_has_t)::[], (fsym)::cvars, _116_701))
in (mkForall_fuel _116_702))
in (_116_703, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_704))
in (let t_interp = (let _116_708 = (let _116_707 = (let _116_706 = (let _116_705 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in ((f_has_t_z)::[], (fsym)::cvars, _116_705))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_706))
in (_116_707, Some ((Support.String.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_116_708))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _52_866 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end
| false -> begin
(let tsym = (varops.fresh "Non_total_Typ_fun")
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (Microsoft_FStar_ToSMT_Term.mkApp (tsym, []))
in (let t_kinding = (let _116_710 = (let _116_709 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_116_709, None))
in Microsoft_FStar_ToSMT_Term.Assume (_116_710))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _116_717 = (let _116_716 = (let _116_715 = (let _116_714 = (let _116_713 = (let _116_712 = (let _116_711 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _116_711))
in (f_has_t, _116_712))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_713))
in ((f_has_t)::[], (fsym)::[], _116_714))
in (mkForall_fuel _116_715))
in (_116_716, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_717))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_877) -> begin
(let _52_896 = (match ((Microsoft_FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, f)); Microsoft_FStar_Absyn_Syntax.tk = _52_886; Microsoft_FStar_Absyn_Syntax.pos = _52_884; Microsoft_FStar_Absyn_Syntax.fvs = _52_882; Microsoft_FStar_Absyn_Syntax.uvs = _52_880} -> begin
(x, f)
end
| _52_893 -> begin
(Support.All.failwith "impossible")
end)
in (match (_52_896) with
| (x, f) -> begin
(let _52_899 = (encode_typ_term x.Microsoft_FStar_Absyn_Syntax.sort env)
in (match (_52_899) with
| (base_t, decls) -> begin
(let _52_903 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_903) with
| (x, xtm, env') -> begin
(let _52_906 = (encode_formula f env')
in (match (_52_906) with
| (refinement, decls') -> begin
(let _52_909 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_909) with
| (fsym, fterm) -> begin
(let encoding = (let _116_719 = (let _116_718 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_116_718, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _116_719))
in (let cvars = (let _116_721 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (Support.All.pipe_right _116_721 (Support.List.filter (fun ( _52_914 ) -> (match (_52_914) with
| (y, _52_913) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_921, _52_923)) -> begin
(let _116_724 = (let _116_723 = (let _116_722 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _116_722))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_723))
in (_116_724, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _116_726 = (let _116_725 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _116_725))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_726))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _116_728 = (let _116_727 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (ffv)::(xfv)::cvars, _116_727))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_728))
in (let t_decls = (let _116_735 = (let _116_734 = (let _116_733 = (let _116_732 = (let _116_731 = (let _116_730 = (let _116_729 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_116_729))
in (assumption, _116_730))
in Microsoft_FStar_ToSMT_Term.Assume (_116_731))
in (_116_732)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_116_733)
in (tdecl)::_116_734)
in (Support.List.append (Support.List.append decls decls') _116_735))
in (let _52_936 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _116_736 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _116_736))
in (let _52_945 = (encode_knd k env ttm)
in (match (_52_945) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let is_full_app = (fun ( _52_952 ) -> (match (()) with
| () -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind head)
in (let _52_957 = (Microsoft_FStar_Absyn_Util.kind_formals kk)
in (match (_52_957) with
| (formals, _52_956) -> begin
((Support.List.length formals) = (Support.List.length args))
end)))
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_typ head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _52_964 = (encode_args args env)
in (match (_52_964) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _52_970 = (encode_args args env)
in (match (_52_970) with
| (args, decls) -> begin
(match ((is_full_app ())) with
| true -> begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _116_741 = (let _116_740 = (Support.List.map (fun ( _52_10 ) -> (match (_52_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (head, _116_740))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_741))
in (t, decls)))
end
| false -> begin
(let head = (lookup_free_tvar env fv)
in (let t = (mk_ApplyT_args head args)
in (t, decls)))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _116_742 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _116_742))
in (let _52_986 = (encode_knd k env ttm)
in (match (_52_986) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _52_989 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, body)) -> begin
(let _52_1001 = (encode_binders None bs env)
in (match (_52_1001) with
| (vars, guards, env, decls, _52_1000) -> begin
(let _52_1004 = (encode_typ_term body env)
in (match (_52_1004) with
| (body, decls') -> begin
(let key_body = (let _116_746 = (let _116_745 = (let _116_744 = (let _116_743 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_116_743, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_744))
in ([], vars, _116_745))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_746))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_1010, _52_1012)) -> begin
(let _116_749 = (let _116_748 = (let _116_747 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _116_747))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_748))
in (_116_749, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
(head, [])
end
| None -> begin
(let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tsym = (varops.fresh "Typ_lam")
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _116_751 = (let _116_750 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _116_750))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_751))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _116_758 = (let _116_757 = (let _116_756 = (let _116_755 = (let _116_754 = (let _116_753 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _116_752 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_116_753, _116_752)))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_754))
in ((app)::[], (Support.List.append vars cvars), _116_755))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_756))
in (_116_757, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_758))
in (let kinding = (let _52_1027 = (let _116_759 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _116_759 env t))
in (match (_52_1027) with
| (ktm, decls'') -> begin
(let _116_763 = (let _116_762 = (let _116_761 = (let _116_760 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_116_760, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_761))
in (_116_762)::[])
in (Support.List.append decls'' _116_763))
end))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _52_1030 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _52_1034)) -> begin
(encode_typ_term t env)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_52_1038) -> begin
(let _116_764 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _116_764 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _116_769 = (let _116_768 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _116_767 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _116_766 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _116_765 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _116_768 _116_767 _116_766 _116_765)))))
in (Support.All.failwith _116_769))
end)))
and encode_exp = (fun ( e ) ( env ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_52_1049) -> begin
(let _116_772 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _116_772 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _52_1056)) -> begin
(let _116_773 = (lookup_free_var env v)
in (_116_773, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _116_774 = (encode_const c)
in (_116_774, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _52_1064)) -> begin
(let _52_1067 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _52_1071))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _52_1077)) -> begin
(let e = (let _116_775 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _116_775))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun ( _52_1086 ) -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _116_778 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_116_778, (decl)::[]))))
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _52_1090 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _116_779 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (Support.All.pipe_left Support.Prims.op_Negation _116_779))) with
| true -> begin
(fallback ())
end
| false -> begin
(let tfun = (as_function_typ env tfun)
in (match (tfun.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
(let nformals = (Support.List.length bs')
in (match (((nformals < (Support.List.length bs)) && (Microsoft_FStar_Absyn_Util.is_total_comp c))) with
| true -> begin
(let _52_1102 = (Support.Microsoft.FStar.Util.first_N nformals bs)
in (match (_52_1102) with
| (bs0, rest) -> begin
(let res_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s (Microsoft_FStar_Absyn_Util.comp_result c))
end
| _52_1106 -> begin
(Support.All.failwith "Impossible")
end)
in (let e = (let _116_781 = (let _116_780 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _116_780))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _116_781 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end
| false -> begin
(let _52_1115 = (encode_binders None bs env)
in (match (_52_1115) with
| (vars, guards, envbody, decls, _52_1114) -> begin
(let _52_1118 = (encode_exp body envbody)
in (match (_52_1118) with
| (body, decls') -> begin
(let key_body = (let _116_785 = (let _116_784 = (let _116_783 = (let _116_782 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_116_782, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_783))
in ([], vars, _116_784))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_785))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_1124, _52_1126)) -> begin
(let _116_788 = (let _116_787 = (let _116_786 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _116_786))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_787))
in (_116_788, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let fsym = (varops.fresh "Exp_abs")
in (let fdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((fsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let f = (let _116_790 = (let _116_789 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _116_789))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_790))
in (let app = (mk_ApplyE f vars)
in (let _52_1140 = (encode_typ_pred None tfun env f)
in (match (_52_1140) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _116_792 = (let _116_791 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_116_791, Some ((Support.String.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_116_792))
in (let interp_f = (let _116_799 = (let _116_798 = (let _116_797 = (let _116_796 = (let _116_795 = (let _116_794 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _116_793 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_116_794, _116_793)))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_795))
in ((app)::[], (Support.List.append vars cvars), _116_796))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_797))
in (_116_798, Some ((Support.String.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_116_799))
in (let f_decls = (Support.List.append (Support.List.append (Support.List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _52_1144 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end))
end
| _52_1147 -> begin
(Support.All.failwith "Impossible")
end))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((l, _52_1158)); Microsoft_FStar_Absyn_Syntax.tk = _52_1155; Microsoft_FStar_Absyn_Syntax.pos = _52_1153; Microsoft_FStar_Absyn_Syntax.fvs = _52_1151; Microsoft_FStar_Absyn_Syntax.uvs = _52_1149}, (Support.Microsoft.FStar.Util.Inl (_52_1173), _52_1176)::(Support.Microsoft.FStar.Util.Inr (v1), _52_1170)::(Support.Microsoft.FStar.Util.Inr (v2), _52_1165)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals l.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
(let _52_1183 = (encode_exp v1 env)
in (match (_52_1183) with
| (v1, decls1) -> begin
(let _52_1186 = (encode_exp v2 env)
in (match (_52_1186) with
| (v2, decls2) -> begin
(let _116_800 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_116_800, (Support.List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_52_1196); Microsoft_FStar_Absyn_Syntax.tk = _52_1194; Microsoft_FStar_Absyn_Syntax.pos = _52_1192; Microsoft_FStar_Absyn_Syntax.fvs = _52_1190; Microsoft_FStar_Absyn_Syntax.uvs = _52_1188}, _52_1200)) -> begin
(let _116_801 = (whnf_e env e)
in (encode_exp _116_801 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args_e)) -> begin
(let _52_1209 = (encode_args args_e env)
in (match (_52_1209) with
| (args, decls) -> begin
(let encode_partial_app = (fun ( ht_opt ) -> (let _52_1214 = (encode_exp head env)
in (match (_52_1214) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (Support.List.append decls decls'))
end
| Some ((formals, c)) -> begin
(let _52_1223 = (Support.Microsoft.FStar.Util.first_N (Support.List.length args_e) formals)
in (match (_52_1223) with
| (formals, rest) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _116_804 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _116_804 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _52_1228 = (encode_typ_pred None ty env app_tm)
in (match (_52_1228) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _116_806 = (let _116_805 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_116_805, None))
in Microsoft_FStar_ToSMT_Term.Assume (_116_806))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun ( fv ) -> (let _52_1235 = (lookup_free_var_sym env fv)
in (match (_52_1235) with
| (fname, fuel_args) -> begin
(let tm = (let _116_812 = (let _116_811 = (let _116_810 = (Support.List.map (fun ( _52_11 ) -> (match (_52_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (Support.List.append fuel_args _116_810))
in (fname, _116_811))
in (Microsoft_FStar_ToSMT_Term.mkApp' _116_812))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _52_1242 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _116_814 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _116_813 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _116_814 _116_813)))
end
| false -> begin
()
end)
in (let head_type = (let _116_817 = (let _116_816 = (let _116_815 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _116_815))
in (whnf env _116_816))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.unrefine _116_817))
in (let _52_1245 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _116_820 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _116_819 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _116_818 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _116_820 _116_819 _116_818))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _116_824 = (let _116_823 = (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _116_822 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _116_821 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" _116_823 _116_822 _116_821))))
in (Support.All.failwith _116_824))
end
| Some ((formals, c)) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _52_1254)) when ((Support.List.length formals) = (Support.List.length args)) -> begin
(encode_full_app fv)
end
| _52_1258 -> begin
(match (((Support.List.length formals) > (Support.List.length args))) with
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
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (_52_1267); Microsoft_FStar_Absyn_Syntax.lbtyp = _52_1265; Microsoft_FStar_Absyn_Syntax.lbeff = _52_1263; Microsoft_FStar_Absyn_Syntax.lbdef = _52_1261}::[]), _52_1273)) -> begin
(Support.All.failwith "Impossible: already handled by encoding of Sig_let")
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (x); Microsoft_FStar_Absyn_Syntax.lbtyp = t1; Microsoft_FStar_Absyn_Syntax.lbeff = _52_1279; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let _52_1291 = (encode_exp e1 env)
in (match (_52_1291) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _52_1295 = (encode_exp e2 env')
in (match (_52_1295) with
| (ee2, decls2) -> begin
(ee2, (Support.List.append decls1 decls2))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_52_1297) -> begin
(let _52_1299 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = Microsoft_FStar_ToSMT_Term.DeclFun ((e, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _116_825 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_116_825, (decl_e)::[])))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _52_1309 = (encode_exp e env)
in (match (_52_1309) with
| (scr, decls) -> begin
(let _52_1349 = (Support.List.fold_right (fun ( _52_1313 ) ( _52_1316 ) -> (match ((_52_1313, _52_1316)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (Support.List.fold_right (fun ( _52_1320 ) ( _52_1323 ) -> (match ((_52_1320, _52_1323)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (Support.All.pipe_right projections (Support.List.fold_left (fun ( env ) ( _52_1329 ) -> (match (_52_1329) with
| (x, t) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v t)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _52_1343 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _52_1340 = (encode_exp w env)
in (match (_52_1340) with
| (w, decls2) -> begin
(let _116_836 = (let _116_835 = (let _116_834 = (let _116_833 = (let _116_832 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _116_832))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_833))
in (guard, _116_834))
in (Microsoft_FStar_ToSMT_Term.mkAnd _116_835))
in (_116_836, decls2))
end))
end)
in (match (_52_1343) with
| (guard, decls2) -> begin
(let _52_1346 = (encode_exp br env)
in (match (_52_1346) with
| (br, decls3) -> begin
(let _116_837 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_116_837, (Support.List.append (Support.List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (Microsoft_FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_52_1349) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (_52_1351) -> begin
(let _116_840 = (let _116_839 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _116_838 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" _116_839 _116_838)))
in (Support.All.failwith _116_840))
end))))
and encode_pat = (fun ( env ) ( pat ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _52_1358 -> begin
(let _116_843 = (encode_one_pat env pat)
in (_116_843)::[])
end))
and encode_one_pat = (fun ( env ) ( pat ) -> (let _52_1361 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _116_846 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" _116_846))
end
| false -> begin
()
end)
in (let _52_1365 = (Microsoft_FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_52_1365) with
| (vars, pat_exp_or_typ) -> begin
(let _52_1386 = (Support.All.pipe_right vars (Support.List.fold_left (fun ( _52_1368 ) ( v ) -> (match (_52_1368) with
| (env, vars) -> begin
(match (v) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_1376 = (gen_typ_var env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_1376) with
| (aa, _52_1374, env) -> begin
(env, ((v, (aa, Microsoft_FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_1383 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_1383) with
| (xx, _52_1381, env) -> begin
(env, ((v, (xx, Microsoft_FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_52_1386) with
| (env, vars) -> begin
(let rec mk_guard = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_1391) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
Microsoft_FStar_ToSMT_Term.mkTrue
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _116_854 = (let _116_853 = (encode_const c)
in (scrutinee, _116_853))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_854))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _52_1415, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( _52_1424 ) -> (match (_52_1424) with
| (arg, _52_1423) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _116_857 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _116_857)))
end))))
in (Microsoft_FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_1431) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_var (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((Support.Microsoft.FStar.Util.Inr (x), scrutinee))::[]
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((Support.Microsoft.FStar.Util.Inl (a), scrutinee))::[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_52_1448) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _52_1452, args)) -> begin
(let _116_865 = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( _52_1460 ) -> (match (_52_1460) with
| (arg, _52_1459) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _116_864 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _116_864)))
end))))
in (Support.All.pipe_right _116_865 Support.List.flatten))
end))
in (let pat_term = (fun ( _52_1463 ) -> (match (()) with
| () -> begin
(match (pat_exp_or_typ) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(encode_typ_term t env)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(encode_exp e env)
end)
end))
in (let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args = (fun ( l ) ( env ) -> (let _52_1493 = (Support.All.pipe_right l (Support.List.fold_left (fun ( _52_1473 ) ( x ) -> (match (_52_1473) with
| (tms, decls) -> begin
(match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1478) -> begin
(let _52_1482 = (encode_typ_term t env)
in (match (_52_1482) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inl (t))::tms, (Support.List.append decls decls'))
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1486) -> begin
(let _52_1490 = (encode_exp e env)
in (match (_52_1490) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inr (t))::tms, (Support.List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_52_1493) with
| (l, decls) -> begin
((Support.List.rev l), decls)
end)))
and encode_formula = (fun ( phi ) ( env ) -> (let _52_1499 = (encode_formula_with_labels phi env)
in (match (_52_1499) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _52_1502 -> begin
(Support.All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun ( induction_on ) ( t ) ( env ) -> (let v_or_t_pat = (fun ( p ) -> (match ((let _116_879 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _116_879.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1509, (Support.Microsoft.FStar.Util.Inl (_52_1516), _52_1519)::(Support.Microsoft.FStar.Util.Inr (e), _52_1513)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1525, (Support.Microsoft.FStar.Util.Inl (t), _52_1529)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _52_1535 -> begin
(Support.All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun ( p ) -> (match ((let _116_882 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _116_882.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1539, _52_1551::(Support.Microsoft.FStar.Util.Inr (hd), _52_1548)::(Support.Microsoft.FStar.Util.Inr (tl), _52_1543)::[])) -> begin
(let _116_884 = (v_or_t_pat hd)
in (let _116_883 = (lemma_pats tl)
in (_116_884)::_116_883))
end
| _52_1556 -> begin
[]
end))
in (let _52_1595 = (match ((let _116_885 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _116_885.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _52_1565; Microsoft_FStar_Absyn_Syntax.pos = _52_1563; Microsoft_FStar_Absyn_Syntax.fvs = _52_1561; Microsoft_FStar_Absyn_Syntax.uvs = _52_1559})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _52_1584)::(Support.Microsoft.FStar.Util.Inl (post), _52_1579)::(Support.Microsoft.FStar.Util.Inr (pats), _52_1574)::[] -> begin
(let _116_886 = (lemma_pats pats)
in (binders, pre, post, _116_886))
end
| _52_1588 -> begin
(Support.All.failwith "impos")
end)
end
| _52_1590 -> begin
(Support.All.failwith "Impos")
end)
in (match (_52_1595) with
| (binders, pre, post, patterns) -> begin
(let _52_1602 = (encode_binders None binders env)
in (match (_52_1602) with
| (vars, guards, env, decls, _52_1601) -> begin
(let _52_1618 = (let _116_888 = (Support.All.pipe_right patterns (Support.List.map (fun ( _52_12 ) -> (match (_52_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1607) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1612) -> begin
(encode_exp e (let _52_1614 = env
in {bindings = _52_1614.bindings; depth = _52_1614.depth; tcenv = _52_1614.tcenv; warn = _52_1614.warn; cache = _52_1614.cache; nolabels = _52_1614.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1614.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _116_888 Support.List.unzip))
in (match (_52_1618) with
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
(let _116_890 = (let _116_889 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _116_889 e))
in (_116_890)::pats)
end
| _52_1626 -> begin
(let rec aux = (fun ( tl ) ( vars ) -> (match (vars) with
| [] -> begin
(let _116_895 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_116_895)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _116_897 = (let _116_896 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _116_896 tl))
in (aux _116_897 vars))
end
| _52_1637 -> begin
pats
end))
in (let _116_898 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _116_898 vars)))
end)
end)
in (let env = (let _52_1639 = env
in {bindings = _52_1639.bindings; depth = _52_1639.depth; tcenv = _52_1639.tcenv; warn = _52_1639.warn; cache = _52_1639.cache; nolabels = true; use_zfuel_name = _52_1639.use_zfuel_name; encode_non_total_function_typ = _52_1639.encode_non_total_function_typ})
in (let _52_1644 = (let _116_899 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _116_899 env))
in (match (_52_1644) with
| (pre, decls'') -> begin
(let _52_1647 = (let _116_900 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _116_900 env))
in (match (_52_1647) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in (let _116_905 = (let _116_904 = (let _116_903 = (let _116_902 = (let _116_901 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_116_901, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_902))
in (pats, vars, _116_903))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_904))
in (_116_905, decls)))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun ( phi ) ( env ) -> (let enc = (fun ( f ) -> (fun ( l ) -> (let _52_1668 = (Support.Microsoft.FStar.Util.fold_map (fun ( decls ) ( x ) -> (match ((Support.Prims.fst x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _52_1660 = (encode_typ_term t env)
in (match (_52_1660) with
| (t, decls') -> begin
((Support.List.append decls decls'), t)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _52_1665 = (encode_exp e env)
in (match (_52_1665) with
| (e, decls') -> begin
((Support.List.append decls decls'), e)
end))
end)) [] l)
in (match (_52_1668) with
| (decls, args) -> begin
(let _116_923 = (f args)
in (_116_923, [], decls))
end))))
in (let enc_prop_c = (fun ( f ) -> (fun ( l ) -> (let _52_1688 = (Support.List.fold_right (fun ( t ) ( _52_1676 ) -> (match (_52_1676) with
| (phis, labs, decls) -> begin
(match ((Support.Prims.fst t)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _52_1682 = (encode_formula_with_labels t env)
in (match (_52_1682) with
| (phi, labs', decls') -> begin
((phi)::phis, (Support.List.append labs' labs), (Support.List.append decls' decls))
end))
end
| _52_1684 -> begin
(Support.All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_52_1688) with
| (phis, labs, decls) -> begin
(let _116_939 = (f phis)
in (_116_939, labs, decls))
end))))
in (let const_op = (fun ( f ) ( _52_1691 ) -> (f, [], []))
in (let un_op = (fun ( f ) ( l ) -> (let _116_953 = (Support.List.hd l)
in (Support.All.pipe_left f _116_953)))
in (let bin_op = (fun ( f ) ( _52_13 ) -> (match (_52_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _52_1702 -> begin
(Support.All.failwith "Impossible")
end))
in (let eq_op = (fun ( _52_14 ) -> (match (_52_14) with
| _52_1710::_52_1708::e1::e2::[] -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun ( _52_15 ) -> (match (_52_15) with
| (Support.Microsoft.FStar.Util.Inl (lhs), _52_1723)::(Support.Microsoft.FStar.Util.Inl (rhs), _52_1718)::[] -> begin
(let _52_1729 = (encode_formula_with_labels rhs env)
in (match (_52_1729) with
| (l1, labs1, decls1) -> begin
(match (l1.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _52_1732)) -> begin
(l1, labs1, decls1)
end
| _52_1736 -> begin
(let _52_1740 = (encode_formula_with_labels lhs env)
in (match (_52_1740) with
| (l2, labs2, decls2) -> begin
(let _116_967 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_116_967, (Support.List.append labs1 labs2), (Support.List.append decls1 decls2)))
end))
end)
end))
end
| _52_1742 -> begin
(Support.All.failwith "impossible")
end))
in (let mk_ite = (fun ( _52_16 ) -> (match (_52_16) with
| (Support.Microsoft.FStar.Util.Inl (guard), _52_1758)::(Support.Microsoft.FStar.Util.Inl (_then), _52_1753)::(Support.Microsoft.FStar.Util.Inl (_else), _52_1748)::[] -> begin
(let _52_1764 = (encode_formula_with_labels guard env)
in (match (_52_1764) with
| (g, labs1, decls1) -> begin
(let _52_1768 = (encode_formula_with_labels _then env)
in (match (_52_1768) with
| (t, labs2, decls2) -> begin
(let _52_1772 = (encode_formula_with_labels _else env)
in (match (_52_1772) with
| (e, labs3, decls3) -> begin
(let res = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (Support.List.append (Support.List.append labs1 labs2) labs3), (Support.List.append (Support.List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _52_1775 -> begin
(Support.All.failwith "impossible")
end))
in (let unboxInt_l = (fun ( f ) ( l ) -> (let _116_979 = (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _116_979)))
in (let connectives = (let _116_1040 = (let _116_988 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _116_988))
in (let _116_1039 = (let _116_1038 = (let _116_994 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _116_994))
in (let _116_1037 = (let _116_1036 = (let _116_1035 = (let _116_1003 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _116_1003))
in (let _116_1034 = (let _116_1033 = (let _116_1032 = (let _116_1012 = (Support.All.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _116_1012))
in (let _116_1031 = (let _116_1030 = (let _116_1018 = (Support.All.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _116_1018))
in (_116_1030)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_116_1032)::_116_1031))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_116_1033)
in (_116_1035)::_116_1034))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_116_1036)
in (_116_1038)::_116_1037))
in (_116_1040)::_116_1039))
in (let fallback = (fun ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((phi', msg, r, b))) -> begin
(let _52_1793 = (encode_formula_with_labels phi' env)
in (match (_52_1793) with
| (phi, labs, decls) -> begin
(match (env.nolabels) with
| true -> begin
(phi, [], decls)
end
| false -> begin
(let lvar = (let _116_1043 = (varops.fresh "label")
in (_116_1043, Microsoft_FStar_ToSMT_Term.Bool_sort))
in (let lterm = (Microsoft_FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (Microsoft_FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ih); Microsoft_FStar_Absyn_Syntax.tk = _52_1804; Microsoft_FStar_Absyn_Syntax.pos = _52_1802; Microsoft_FStar_Absyn_Syntax.fvs = _52_1800; Microsoft_FStar_Absyn_Syntax.uvs = _52_1798}, _52_1819::(Support.Microsoft.FStar.Util.Inr (l), _52_1816)::(Support.Microsoft.FStar.Util.Inl (phi), _52_1811)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals ih.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.using_IH) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let _52_1825 = (encode_exp l env)
in (match (_52_1825) with
| (e, decls) -> begin
(let _52_1828 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_52_1828) with
| (f, decls') -> begin
(f, [], (Support.List.append decls decls'))
end))
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.mkTrue, [], [])
end)
end
| _52_1830 -> begin
(let _52_1833 = (encode_typ_term phi env)
in (match (_52_1833) with
| (tt, decls) -> begin
(let _116_1044 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_116_1044, [], decls))
end))
end))
in (let encode_q_body = (fun ( env ) ( bs ) ( ps ) ( body ) -> (let _52_1845 = (encode_binders None bs env)
in (match (_52_1845) with
| (vars, guards, env, decls, _52_1844) -> begin
(let _52_1861 = (let _116_1054 = (Support.All.pipe_right ps (Support.List.map (fun ( _52_17 ) -> (match (_52_17) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1850) -> begin
(encode_typ_term t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1855) -> begin
(encode_exp e (let _52_1857 = env
in {bindings = _52_1857.bindings; depth = _52_1857.depth; tcenv = _52_1857.tcenv; warn = _52_1857.warn; cache = _52_1857.cache; nolabels = _52_1857.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1857.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _116_1054 Support.List.unzip))
in (match (_52_1861) with
| (pats, decls') -> begin
(let _52_1865 = (encode_formula_with_labels body env)
in (match (_52_1865) with
| (body, labs, decls'') -> begin
(let _116_1055 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _116_1055, body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'')))
end))
end))
end)))
in (let _52_1866 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _116_1056 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" _116_1056))
end
| false -> begin
()
end)
in (let phi = (Microsoft_FStar_Absyn_Util.compress_typ phi)
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn ((op, arms))) -> begin
(match ((Support.All.pipe_right connectives (Support.List.tryFind (fun ( _52_1878 ) -> (match (_52_1878) with
| (l, _52_1877) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some ((_52_1881, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, pats, body))) -> begin
(let _52_1891 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _116_1073 = (Support.All.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" _116_1073))
end
| false -> begin
()
end)
in (let _52_1899 = (encode_q_body env vars pats body)
in (match (_52_1899) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _116_1076 = (let _116_1075 = (let _116_1074 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _116_1074))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1075))
in (_116_1076, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _52_1912 = (encode_q_body env vars pats body)
in (match (_52_1912) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _116_1079 = (let _116_1078 = (let _116_1077 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _116_1077))
in (Microsoft_FStar_ToSMT_Term.mkExists _116_1078))
in (_116_1079, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : Microsoft_FStar_Absyn_Syntax.lident  ->  string  ->  Microsoft_FStar_ToSMT_Term.decl list; is : Microsoft_FStar_Absyn_Syntax.lident  ->  bool}

let is_Mkprims_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkprims_t"))

let prims = (let _52_1918 = (fresh_fvar "a" Microsoft_FStar_ToSMT_Term.Type_sort)
in (match (_52_1918) with
| (asym, a) -> begin
(let _52_1921 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_1921) with
| (xsym, x) -> begin
(let _52_1924 = (fresh_fvar "y" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_1924) with
| (ysym, y) -> begin
(let deffun = (fun ( vars ) ( body ) ( x ) -> (Microsoft_FStar_ToSMT_Term.DefineFun ((x, vars, Microsoft_FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun ( vars ) ( body ) -> (fun ( x ) -> (let t1 = (let _116_1122 = (let _116_1121 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _116_1121))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1122))
in (let vname_decl = (let _116_1124 = (let _116_1123 = (Support.All.pipe_right vars (Support.List.map Support.Prims.snd))
in (x, _116_1123, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_116_1124))
in (let _116_1130 = (let _116_1129 = (let _116_1128 = (let _116_1127 = (let _116_1126 = (let _116_1125 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _116_1125))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1126))
in (_116_1127, None))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1128))
in (_116_1129)::[])
in (vname_decl)::_116_1130)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _116_1290 = (let _116_1139 = (let _116_1138 = (let _116_1137 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1137))
in (quant axy _116_1138))
in (Microsoft_FStar_Absyn_Const.op_Eq, _116_1139))
in (let _116_1289 = (let _116_1288 = (let _116_1146 = (let _116_1145 = (let _116_1144 = (let _116_1143 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _116_1143))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1144))
in (quant axy _116_1145))
in (Microsoft_FStar_Absyn_Const.op_notEq, _116_1146))
in (let _116_1287 = (let _116_1286 = (let _116_1155 = (let _116_1154 = (let _116_1153 = (let _116_1152 = (let _116_1151 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1150 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1151, _116_1150)))
in (Microsoft_FStar_ToSMT_Term.mkLT _116_1152))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1153))
in (quant xy _116_1154))
in (Microsoft_FStar_Absyn_Const.op_LT, _116_1155))
in (let _116_1285 = (let _116_1284 = (let _116_1164 = (let _116_1163 = (let _116_1162 = (let _116_1161 = (let _116_1160 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1159 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1160, _116_1159)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _116_1161))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1162))
in (quant xy _116_1163))
in (Microsoft_FStar_Absyn_Const.op_LTE, _116_1164))
in (let _116_1283 = (let _116_1282 = (let _116_1173 = (let _116_1172 = (let _116_1171 = (let _116_1170 = (let _116_1169 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1168 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1169, _116_1168)))
in (Microsoft_FStar_ToSMT_Term.mkGT _116_1170))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1171))
in (quant xy _116_1172))
in (Microsoft_FStar_Absyn_Const.op_GT, _116_1173))
in (let _116_1281 = (let _116_1280 = (let _116_1182 = (let _116_1181 = (let _116_1180 = (let _116_1179 = (let _116_1178 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1177 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1178, _116_1177)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _116_1179))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1180))
in (quant xy _116_1181))
in (Microsoft_FStar_Absyn_Const.op_GTE, _116_1182))
in (let _116_1279 = (let _116_1278 = (let _116_1191 = (let _116_1190 = (let _116_1189 = (let _116_1188 = (let _116_1187 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1186 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1187, _116_1186)))
in (Microsoft_FStar_ToSMT_Term.mkSub _116_1188))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _116_1189))
in (quant xy _116_1190))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _116_1191))
in (let _116_1277 = (let _116_1276 = (let _116_1198 = (let _116_1197 = (let _116_1196 = (let _116_1195 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _116_1195))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _116_1196))
in (quant qx _116_1197))
in (Microsoft_FStar_Absyn_Const.op_Minus, _116_1198))
in (let _116_1275 = (let _116_1274 = (let _116_1207 = (let _116_1206 = (let _116_1205 = (let _116_1204 = (let _116_1203 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1202 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1203, _116_1202)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _116_1204))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _116_1205))
in (quant xy _116_1206))
in (Microsoft_FStar_Absyn_Const.op_Addition, _116_1207))
in (let _116_1273 = (let _116_1272 = (let _116_1216 = (let _116_1215 = (let _116_1214 = (let _116_1213 = (let _116_1212 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1211 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1212, _116_1211)))
in (Microsoft_FStar_ToSMT_Term.mkMul _116_1213))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _116_1214))
in (quant xy _116_1215))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _116_1216))
in (let _116_1271 = (let _116_1270 = (let _116_1225 = (let _116_1224 = (let _116_1223 = (let _116_1222 = (let _116_1221 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1220 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1221, _116_1220)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _116_1222))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _116_1223))
in (quant xy _116_1224))
in (Microsoft_FStar_Absyn_Const.op_Division, _116_1225))
in (let _116_1269 = (let _116_1268 = (let _116_1234 = (let _116_1233 = (let _116_1232 = (let _116_1231 = (let _116_1230 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1229 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_116_1230, _116_1229)))
in (Microsoft_FStar_ToSMT_Term.mkMod _116_1231))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _116_1232))
in (quant xy _116_1233))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _116_1234))
in (let _116_1267 = (let _116_1266 = (let _116_1243 = (let _116_1242 = (let _116_1241 = (let _116_1240 = (let _116_1239 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _116_1238 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_116_1239, _116_1238)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _116_1240))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1241))
in (quant xy _116_1242))
in (Microsoft_FStar_Absyn_Const.op_And, _116_1243))
in (let _116_1265 = (let _116_1264 = (let _116_1252 = (let _116_1251 = (let _116_1250 = (let _116_1249 = (let _116_1248 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _116_1247 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_116_1248, _116_1247)))
in (Microsoft_FStar_ToSMT_Term.mkOr _116_1249))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1250))
in (quant xy _116_1251))
in (Microsoft_FStar_Absyn_Const.op_Or, _116_1252))
in (let _116_1263 = (let _116_1262 = (let _116_1259 = (let _116_1258 = (let _116_1257 = (let _116_1256 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _116_1256))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_1257))
in (quant qx _116_1258))
in (Microsoft_FStar_Absyn_Const.op_Negation, _116_1259))
in (_116_1262)::[])
in (_116_1264)::_116_1263))
in (_116_1266)::_116_1265))
in (_116_1268)::_116_1267))
in (_116_1270)::_116_1269))
in (_116_1272)::_116_1271))
in (_116_1274)::_116_1273))
in (_116_1276)::_116_1275))
in (_116_1278)::_116_1277))
in (_116_1280)::_116_1279))
in (_116_1282)::_116_1281))
in (_116_1284)::_116_1283))
in (_116_1286)::_116_1285))
in (_116_1288)::_116_1287))
in (_116_1290)::_116_1289))
in (let mk = (fun ( l ) ( v ) -> (let _116_1322 = (Support.All.pipe_right prims (Support.List.filter (fun ( _52_1944 ) -> (match (_52_1944) with
| (l', _52_1943) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (Support.All.pipe_right _116_1322 (Support.List.collect (fun ( _52_1948 ) -> (match (_52_1948) with
| (_52_1946, b) -> begin
(b v)
end))))))
in (let is = (fun ( l ) -> (Support.All.pipe_right prims (Support.Microsoft.FStar.Util.for_some (fun ( _52_1954 ) -> (match (_52_1954) with
| (l', _52_1953) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

let primitive_type_axioms = (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let mk_unit = (fun ( _52_1960 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let _116_1354 = (let _116_1345 = (let _116_1344 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_116_1344, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1345))
in (let _116_1353 = (let _116_1352 = (let _116_1351 = (let _116_1350 = (let _116_1349 = (let _116_1348 = (let _116_1347 = (let _116_1346 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _116_1346))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1347))
in ((typing_pred)::[], (xx)::[], _116_1348))
in (mkForall_fuel _116_1349))
in (_116_1350, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1351))
in (_116_1352)::[])
in (_116_1354)::_116_1353))))
in (let mk_bool = (fun ( _52_1965 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _116_1374 = (let _116_1364 = (let _116_1363 = (let _116_1362 = (let _116_1361 = (let _116_1360 = (let _116_1359 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _116_1359))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1360))
in ((typing_pred)::[], (xx)::[], _116_1361))
in (mkForall_fuel _116_1362))
in (_116_1363, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1364))
in (let _116_1373 = (let _116_1372 = (let _116_1371 = (let _116_1370 = (let _116_1369 = (let _116_1368 = (let _116_1365 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_116_1365)::[])
in (let _116_1367 = (let _116_1366 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _116_1366 tt))
in (_116_1368, (bb)::[], _116_1367)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1369))
in (_116_1370, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1371))
in (_116_1372)::[])
in (_116_1374)::_116_1373))))))
in (let mk_int = (fun ( _52_1972 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _116_1386 = (let _116_1385 = (let _116_1384 = (let _116_1383 = (let _116_1382 = (let _116_1381 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _116_1380 = (let _116_1379 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_116_1379)::[])
in (_116_1381)::_116_1380))
in (tt)::_116_1382)
in (tt)::_116_1383)
in ("Prims.Precedes", _116_1384))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1385))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _116_1386))
in (let precedes_y_x = (let _116_1387 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _116_1387))
in (let _116_1428 = (let _116_1393 = (let _116_1392 = (let _116_1391 = (let _116_1390 = (let _116_1389 = (let _116_1388 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _116_1388))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1389))
in ((typing_pred)::[], (xx)::[], _116_1390))
in (mkForall_fuel _116_1391))
in (_116_1392, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1393))
in (let _116_1427 = (let _116_1426 = (let _116_1400 = (let _116_1399 = (let _116_1398 = (let _116_1397 = (let _116_1394 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_116_1394)::[])
in (let _116_1396 = (let _116_1395 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _116_1395 tt))
in (_116_1397, (bb)::[], _116_1396)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1398))
in (_116_1399, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1400))
in (let _116_1425 = (let _116_1424 = (let _116_1423 = (let _116_1422 = (let _116_1421 = (let _116_1420 = (let _116_1419 = (let _116_1418 = (let _116_1417 = (let _116_1416 = (let _116_1415 = (let _116_1414 = (let _116_1403 = (let _116_1402 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _116_1401 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_116_1402, _116_1401)))
in (Microsoft_FStar_ToSMT_Term.mkGT _116_1403))
in (let _116_1413 = (let _116_1412 = (let _116_1406 = (let _116_1405 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _116_1404 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_116_1405, _116_1404)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _116_1406))
in (let _116_1411 = (let _116_1410 = (let _116_1409 = (let _116_1408 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _116_1407 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_116_1408, _116_1407)))
in (Microsoft_FStar_ToSMT_Term.mkLT _116_1409))
in (_116_1410)::[])
in (_116_1412)::_116_1411))
in (_116_1414)::_116_1413))
in (typing_pred_y)::_116_1415)
in (typing_pred)::_116_1416)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _116_1417))
in (_116_1418, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1419))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _116_1420))
in (mkForall_fuel _116_1421))
in (_116_1422, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1423))
in (_116_1424)::[])
in (_116_1426)::_116_1425))
in (_116_1428)::_116_1427)))))))))))
in (let mk_int_alias = (fun ( _52_1984 ) ( tt ) -> (let _116_1437 = (let _116_1436 = (let _116_1435 = (let _116_1434 = (let _116_1433 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _116_1433))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_1434))
in (_116_1435, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1436))
in (_116_1437)::[]))
in (let mk_str = (fun ( _52_1988 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _116_1457 = (let _116_1447 = (let _116_1446 = (let _116_1445 = (let _116_1444 = (let _116_1443 = (let _116_1442 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _116_1442))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1443))
in ((typing_pred)::[], (xx)::[], _116_1444))
in (mkForall_fuel _116_1445))
in (_116_1446, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1447))
in (let _116_1456 = (let _116_1455 = (let _116_1454 = (let _116_1453 = (let _116_1452 = (let _116_1451 = (let _116_1448 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_116_1448)::[])
in (let _116_1450 = (let _116_1449 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _116_1449 tt))
in (_116_1451, (bb)::[], _116_1450)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1452))
in (_116_1453, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1454))
in (_116_1455)::[])
in (_116_1457)::_116_1456))))))
in (let mk_ref = (fun ( reft_name ) ( _52_1996 ) -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _116_1464 = (let _116_1463 = (let _116_1462 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_116_1462)::[])
in (reft_name, _116_1463))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1464))
in (let refb = (let _116_1467 = (let _116_1466 = (let _116_1465 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_116_1465)::[])
in (reft_name, _116_1466))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1467))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _116_1486 = (let _116_1473 = (let _116_1472 = (let _116_1471 = (let _116_1470 = (let _116_1469 = (let _116_1468 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _116_1468))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1469))
in ((typing_pred)::[], (xx)::(aa)::[], _116_1470))
in (mkForall_fuel _116_1471))
in (_116_1472, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1473))
in (let _116_1485 = (let _116_1484 = (let _116_1483 = (let _116_1482 = (let _116_1481 = (let _116_1480 = (let _116_1479 = (let _116_1478 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _116_1477 = (let _116_1476 = (let _116_1475 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _116_1474 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_116_1475, _116_1474)))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_1476))
in (_116_1478, _116_1477)))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1479))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _116_1480))
in (mkForall_fuel' 2 _116_1481))
in (_116_1482, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1483))
in (_116_1484)::[])
in (_116_1486)::_116_1485))))))))))
in (let mk_false_interp = (fun ( _52_2006 ) ( false_tm ) -> (let valid = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _116_1493 = (let _116_1492 = (let _116_1491 = (Microsoft_FStar_ToSMT_Term.mkIff (Microsoft_FStar_ToSMT_Term.mkFalse, valid))
in (_116_1491, Some ("False interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1492))
in (_116_1493)::[])))
in (let mk_and_interp = (fun ( conj ) ( _52_2012 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _116_1500 = (let _116_1499 = (let _116_1498 = (Microsoft_FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_116_1498)::[])
in ("Valid", _116_1499))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1500))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _116_1507 = (let _116_1506 = (let _116_1505 = (let _116_1504 = (let _116_1503 = (let _116_1502 = (let _116_1501 = (Microsoft_FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_116_1501, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1502))
in ((valid)::[], (aa)::(bb)::[], _116_1503))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1504))
in (_116_1505, Some ("/\\ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1506))
in (_116_1507)::[])))))))))
in (let mk_or_interp = (fun ( disj ) ( _52_2023 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _116_1514 = (let _116_1513 = (let _116_1512 = (Microsoft_FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_116_1512)::[])
in ("Valid", _116_1513))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1514))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _116_1521 = (let _116_1520 = (let _116_1519 = (let _116_1518 = (let _116_1517 = (let _116_1516 = (let _116_1515 = (Microsoft_FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_116_1515, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1516))
in ((valid)::[], (aa)::(bb)::[], _116_1517))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1518))
in (_116_1519, Some ("\\/ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1520))
in (_116_1521)::[])))))))))
in (let mk_eq2_interp = (fun ( eq2 ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _116_1528 = (let _116_1527 = (let _116_1526 = (Microsoft_FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_116_1526)::[])
in ("Valid", _116_1527))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1528))
in (let _116_1535 = (let _116_1534 = (let _116_1533 = (let _116_1532 = (let _116_1531 = (let _116_1530 = (let _116_1529 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (_116_1529, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1530))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _116_1531))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1532))
in (_116_1533, Some ("Eq2 interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1534))
in (_116_1535)::[])))))))))))
in (let mk_imp_interp = (fun ( imp ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _116_1542 = (let _116_1541 = (let _116_1540 = (Microsoft_FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_116_1540)::[])
in ("Valid", _116_1541))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1542))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _116_1549 = (let _116_1548 = (let _116_1547 = (let _116_1546 = (let _116_1545 = (let _116_1544 = (let _116_1543 = (Microsoft_FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_116_1543, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1544))
in ((valid)::[], (aa)::(bb)::[], _116_1545))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1546))
in (_116_1547, Some ("==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1548))
in (_116_1549)::[])))))))))
in (let mk_iff_interp = (fun ( iff ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _116_1556 = (let _116_1555 = (let _116_1554 = (Microsoft_FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_116_1554)::[])
in ("Valid", _116_1555))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1556))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _116_1563 = (let _116_1562 = (let _116_1561 = (let _116_1560 = (let _116_1559 = (let _116_1558 = (let _116_1557 = (Microsoft_FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_116_1557, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1558))
in ((valid)::[], (aa)::(bb)::[], _116_1559))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1560))
in (_116_1561, Some ("<==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1562))
in (_116_1563)::[])))))))))
in (let mk_forall_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _116_1570 = (let _116_1569 = (let _116_1568 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_116_1568)::[])
in ("Valid", _116_1569))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1570))
in (let valid_b_x = (let _116_1573 = (let _116_1572 = (let _116_1571 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_116_1571)::[])
in ("Valid", _116_1572))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1573))
in (let _116_1586 = (let _116_1585 = (let _116_1584 = (let _116_1583 = (let _116_1582 = (let _116_1581 = (let _116_1580 = (let _116_1579 = (let _116_1578 = (let _116_1574 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_116_1574)::[])
in (let _116_1577 = (let _116_1576 = (let _116_1575 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_116_1575, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1576))
in (_116_1578, (xx)::[], _116_1577)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1579))
in (_116_1580, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1581))
in ((valid)::[], (aa)::(bb)::[], _116_1582))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1583))
in (_116_1584, Some ("forall interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1585))
in (_116_1586)::[]))))))))))
in (let mk_exists_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _116_1593 = (let _116_1592 = (let _116_1591 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_116_1591)::[])
in ("Valid", _116_1592))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1593))
in (let valid_b_x = (let _116_1596 = (let _116_1595 = (let _116_1594 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_116_1594)::[])
in ("Valid", _116_1595))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1596))
in (let _116_1609 = (let _116_1608 = (let _116_1607 = (let _116_1606 = (let _116_1605 = (let _116_1604 = (let _116_1603 = (let _116_1602 = (let _116_1601 = (let _116_1597 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_116_1597)::[])
in (let _116_1600 = (let _116_1599 = (let _116_1598 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_116_1598, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1599))
in (_116_1601, (xx)::[], _116_1600)))
in (Microsoft_FStar_ToSMT_Term.mkExists _116_1602))
in (_116_1603, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1604))
in ((valid)::[], (aa)::(bb)::[], _116_1605))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1606))
in (_116_1607, Some ("exists interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1608))
in (_116_1609)::[]))))))))))
in (let mk_foralltyp_interp = (fun ( for_all ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _116_1616 = (let _116_1615 = (let _116_1614 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_116_1614)::[])
in ("Valid", _116_1615))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1616))
in (let valid_a_b = (let _116_1619 = (let _116_1618 = (let _116_1617 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_116_1617)::[])
in ("Valid", _116_1618))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1619))
in (let _116_1632 = (let _116_1631 = (let _116_1630 = (let _116_1629 = (let _116_1628 = (let _116_1627 = (let _116_1626 = (let _116_1625 = (let _116_1624 = (let _116_1620 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_116_1620)::[])
in (let _116_1623 = (let _116_1622 = (let _116_1621 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_116_1621, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1622))
in (_116_1624, (bb)::[], _116_1623)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1625))
in (_116_1626, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1627))
in ((valid)::[], (kk)::(aa)::[], _116_1628))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1629))
in (_116_1630, Some ("ForallTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1631))
in (_116_1632)::[]))))))))))
in (let mk_existstyp_interp = (fun ( for_some ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _116_1639 = (let _116_1638 = (let _116_1637 = (Microsoft_FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_116_1637)::[])
in ("Valid", _116_1638))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1639))
in (let valid_a_b = (let _116_1642 = (let _116_1641 = (let _116_1640 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_116_1640)::[])
in ("Valid", _116_1641))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1642))
in (let _116_1655 = (let _116_1654 = (let _116_1653 = (let _116_1652 = (let _116_1651 = (let _116_1650 = (let _116_1649 = (let _116_1648 = (let _116_1647 = (let _116_1643 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_116_1643)::[])
in (let _116_1646 = (let _116_1645 = (let _116_1644 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_116_1644, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1645))
in (_116_1647, (bb)::[], _116_1646)))
in (Microsoft_FStar_ToSMT_Term.mkExists _116_1648))
in (_116_1649, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _116_1650))
in ((valid)::[], (kk)::(aa)::[], _116_1651))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1652))
in (_116_1653, Some ("ExistsTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1654))
in (_116_1655)::[]))))))))))
in (let prims = ((Microsoft_FStar_Absyn_Const.unit_lid, mk_unit))::((Microsoft_FStar_Absyn_Const.bool_lid, mk_bool))::((Microsoft_FStar_Absyn_Const.int_lid, mk_int))::((Microsoft_FStar_Absyn_Const.string_lid, mk_str))::((Microsoft_FStar_Absyn_Const.ref_lid, mk_ref))::((Microsoft_FStar_Absyn_Const.char_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.uint8_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.false_lid, mk_false_interp))::((Microsoft_FStar_Absyn_Const.and_lid, mk_and_interp))::((Microsoft_FStar_Absyn_Const.or_lid, mk_or_interp))::((Microsoft_FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp_interp))::((Microsoft_FStar_Absyn_Const.iff_lid, mk_iff_interp))::((Microsoft_FStar_Absyn_Const.forall_lid, mk_forall_interp))::((Microsoft_FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun ( t ) ( s ) ( tt ) -> (match ((Support.Microsoft.FStar.Util.find_opt (fun ( _52_2116 ) -> (match (_52_2116) with
| (l, _52_2115) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some ((_52_2119, f)) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun ( env ) ( se ) -> (let _52_2125 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _116_1798 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") _116_1798))
end
| false -> begin
()
end)
in (let nm = (match ((Microsoft_FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.Microsoft_FStar_Absyn_Syntax.str
end)
in (let _52_2133 = (encode_sigelt' env se)
in (match (_52_2133) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _116_1801 = (let _116_1800 = (let _116_1799 = (Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_116_1799))
in (_116_1800)::[])
in (_116_1801, e))
end
| _52_2136 -> begin
(let _116_1808 = (let _116_1807 = (let _116_1803 = (let _116_1802 = (Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_116_1802))
in (_116_1803)::g)
in (let _116_1806 = (let _116_1805 = (let _116_1804 = (Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_116_1804))
in (_116_1805)::[])
in (Support.List.append _116_1807 _116_1806)))
in (_116_1808, e))
end)
end)))))
and encode_sigelt' = (fun ( env ) ( se ) -> (let should_skip = (fun ( l ) -> ((((Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.pure_") || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.ex_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.st_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.all_")))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_52_2142, _52_2144, _52_2146, _52_2148, Microsoft_FStar_Absyn_Syntax.Effect::[], _52_2152)) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _52_2157, _52_2159, _52_2161, _52_2163, _52_2165)) when (should_skip lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _52_2170, _52_2172, _52_2174, _52_2176, _52_2178)) when (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.b2t_lid) -> begin
(let _52_2184 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_52_2184) with
| (tname, ttok, env) -> begin
(let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _116_1813 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _116_1813))
in (let decls = (let _116_1821 = (let _116_1820 = (let _116_1819 = (let _116_1818 = (let _116_1817 = (let _116_1816 = (let _116_1815 = (let _116_1814 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _116_1814))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_1815))
in ((valid_b2t_x)::[], (xx)::[], _116_1816))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1817))
in (_116_1818, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1819))
in (_116_1820)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_116_1821)
in (decls, env)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _52_2192, t, tags, _52_2196)) -> begin
(let _52_2202 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_52_2202) with
| (tname, ttok, env) -> begin
(let _52_2211 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((tps', body)) -> begin
((Support.List.append tps tps'), body)
end
| _52_2208 -> begin
(tps, t)
end)
in (match (_52_2211) with
| (tps, t) -> begin
(let _52_2218 = (encode_binders None tps env)
in (match (_52_2218) with
| (vars, guards, env', binder_decls, _52_2217) -> begin
(let tok_app = (let _116_1822 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _116_1822 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _116_1824 = (let _116_1823 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _116_1823))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1824))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _52_2224 -> begin
(let _116_1826 = (let _116_1825 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _116_1825))
in (_116_1826)::[])
end)
in (let decls = (let _116_1837 = (let _116_1830 = (let _116_1829 = (let _116_1828 = (let _116_1827 = (Support.List.map Support.Prims.snd vars)
in (tname, _116_1827, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_116_1828))
in (_116_1829)::(tok_decl)::[])
in (Support.List.append _116_1830 fresh_tok))
in (let _116_1836 = (let _116_1835 = (let _116_1834 = (let _116_1833 = (let _116_1832 = (let _116_1831 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _116_1831))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1832))
in (_116_1833, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1834))
in (_116_1835)::[])
in (Support.List.append _116_1837 _116_1836)))
in (let t = (whnf env t)
in (let _52_2236 = (match ((Support.All.pipe_right tags (Support.Microsoft.FStar.Util.for_some (fun ( _52_18 ) -> (match (_52_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _52_2231 -> begin
false
end))))) with
| true -> begin
(let _116_1840 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _116_1839 = (encode_formula t env')
in (_116_1840, _116_1839)))
end
| false -> begin
(let _116_1841 = (encode_typ_term t env')
in (app, _116_1841))
end)
in (match (_52_2236) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _116_1848 = (let _116_1847 = (let _116_1846 = (let _116_1845 = (let _116_1844 = (let _116_1843 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _116_1842 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_116_1843, _116_1842)))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1844))
in ((def)::[], vars, _116_1845))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1846))
in (_116_1847, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1848))
in (let kindingAx = (let _52_2240 = (let _116_1849 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _116_1849 env' app))
in (match (_52_2240) with
| (k, decls) -> begin
(let _116_1857 = (let _116_1856 = (let _116_1855 = (let _116_1854 = (let _116_1853 = (let _116_1852 = (let _116_1851 = (let _116_1850 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_116_1850, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1851))
in ((app)::[], vars, _116_1852))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1853))
in (_116_1854, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1855))
in (_116_1856)::[])
in (Support.List.append decls _116_1857))
end))
in (let g = (let _116_1858 = (primitive_type_axioms lid tname app)
in (Support.List.append (Support.List.append (Support.List.append (Support.List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _116_1858))
in (g, env))))
end))))))))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _52_2247)) -> begin
(let tt = (whnf env t)
in (let _52_2253 = (encode_free_var env lid t tt quals)
in (match (_52_2253) with
| (decls, env) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_smt_lemma t) && ((Support.All.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption)) || env.tcenv.Microsoft_FStar_Tc_Env.is_iface))) with
| true -> begin
(let _116_1860 = (let _116_1859 = (encode_smt_lemma env lid t)
in (Support.List.append decls _116_1859))
in (_116_1860, env))
end
| false -> begin
(decls, env)
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((l, f, _52_2257, _52_2259)) -> begin
(let _52_2264 = (encode_formula f env)
in (match (_52_2264) with
| (f, decls) -> begin
(let g = (let _116_1865 = (let _116_1864 = (let _116_1863 = (let _116_1862 = (let _116_1861 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "Assumption: %s" _116_1861))
in Some (_116_1862))
in (f, _116_1863))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1864))
in (_116_1865)::[])
in ((Support.List.append decls g), env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _52_2270, datas, quals, _52_2274)) when (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.precedes_lid) -> begin
(let _52_2280 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2280) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, _52_2283, _52_2285, _52_2287, _52_2289, _52_2291, _52_2293)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.char_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.Microsoft_FStar_Absyn_Syntax.str
in (let tsym = (Microsoft_FStar_ToSMT_Term.mkFreeV (tname, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((tname, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let _116_1867 = (let _116_1866 = (primitive_type_axioms t tname tsym)
in (decl)::_116_1866)
in (_116_1867, (push_free_tvar env t tname (Some (tsym))))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _52_2303, datas, quals, _52_2307)) -> begin
(let is_logical = (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_19 ) -> (match (_52_19) with
| (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _52_2314 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun ( c ) -> (match (is_logical) with
| true -> begin
(let _52_2324 = c
in (match (_52_2324) with
| (name, args, _52_2321, _52_2323) -> begin
(let _116_1873 = (let _116_1872 = (let _116_1871 = (Support.All.pipe_right args (Support.List.map Support.Prims.snd))
in (name, _116_1871, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_116_1872))
in (_116_1873)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun ( tapp ) ( vars ) -> (match ((((Support.List.length datas) = 0) || (Support.All.pipe_right datas (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (let _116_1879 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (Support.All.pipe_right _116_1879 Support.Option.isNone))))))) with
| true -> begin
[]
end
| false -> begin
(let _52_2331 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_2331) with
| (xxsym, xx) -> begin
(let _52_2374 = (Support.All.pipe_right datas (Support.List.fold_left (fun ( _52_2334 ) ( l ) -> (match (_52_2334) with
| (out, decls) -> begin
(let data_t = (Microsoft_FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _52_2344 = (match ((Microsoft_FStar_Absyn_Util.function_formals data_t)) with
| Some ((formals, res)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_52_2344) with
| (args, res) -> begin
(let indices = (match ((let _116_1882 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _116_1882.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_52_2346, indices)) -> begin
indices
end
| _52_2351 -> begin
[]
end)
in (let env = (Support.All.pipe_right args (Support.List.fold_left (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _116_1887 = (let _116_1886 = (let _116_1885 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_116_1885, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1886))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _116_1887))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _116_1890 = (let _116_1889 = (let _116_1888 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_116_1888, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1889))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _116_1890))
end)) env))
in (let _52_2362 = (encode_args indices env)
in (match (_52_2362) with
| (indices, decls') -> begin
(let _52_2363 = (match (((Support.List.length indices) <> (Support.List.length vars))) with
| true -> begin
(Support.All.failwith "Impossible")
end
| false -> begin
()
end)
in (let eqs = (let _116_1897 = (Support.List.map2 (fun ( v ) ( a ) -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _116_1894 = (let _116_1893 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_116_1893, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_1894))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(let _116_1896 = (let _116_1895 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_116_1895, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_1896))
end)) vars indices)
in (Support.All.pipe_right _116_1897 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _116_1902 = (let _116_1901 = (let _116_1900 = (let _116_1899 = (let _116_1898 = (mk_data_tester env l xx)
in (_116_1898, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _116_1899))
in (out, _116_1900))
in (Microsoft_FStar_ToSMT_Term.mkOr _116_1901))
in (_116_1902, (Support.List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_52_2374) with
| (data_ax, decls) -> begin
(let _52_2377 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2377) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _116_1903 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _116_1903 xx tapp))
in (let _116_1910 = (let _116_1909 = (let _116_1908 = (let _116_1907 = (let _116_1906 = (let _116_1905 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _116_1904 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _116_1905, _116_1904)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1906))
in (_116_1907, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1908))
in (_116_1909)::[])
in (Support.List.append decls _116_1910)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _52_2389 = (match ((let _116_1911 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _116_1911.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, res)) -> begin
(true, bs, res)
end
| _52_2385 -> begin
(false, [], k)
end)
in (match (_52_2389) with
| (is_kind_arrow, formals, res) -> begin
(let _52_2396 = (encode_binders None formals env)
in (match (_52_2396) with
| (vars, guards, env', binder_decls, _52_2395) -> begin
(let projection_axioms = (fun ( tapp ) ( vars ) -> (match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.find_opt (fun ( _52_20 ) -> (match (_52_20) with
| Microsoft_FStar_Absyn_Syntax.Projector (_52_2402) -> begin
true
end
| _52_2405 -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inl (a)))) -> begin
(let rec projectee = (fun ( i ) ( _52_21 ) -> (match (_52_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (_52_2420) -> begin
(projectee (i + 1) tl)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(match ((x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = "projectee")) with
| true -> begin
i
end
| false -> begin
(projectee (i + 1) tl)
end)
end)
end))
in (let projectee_pos = (projectee 0 formals)
in (let _52_2435 = (match ((Support.Microsoft.FStar.Util.first_N projectee_pos vars)) with
| (_52_2426, xx::suffix) -> begin
(xx, suffix)
end
| _52_2432 -> begin
(Support.All.failwith "impossible")
end)
in (match (_52_2435) with
| (xx, suffix) -> begin
(let dproj_app = (let _116_1925 = (let _116_1924 = (let _116_1923 = (mk_typ_projector_name d a)
in (let _116_1922 = (let _116_1921 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_116_1921)::[])
in (_116_1923, _116_1922)))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1924))
in (mk_ApplyT _116_1925 suffix))
in (let _116_1930 = (let _116_1929 = (let _116_1928 = (let _116_1927 = (let _116_1926 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _116_1926))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1927))
in (_116_1928, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1929))
in (_116_1930)::[]))
end))))
end
| _52_2438 -> begin
[]
end))
in (let pretype_axioms = (fun ( tapp ) ( vars ) -> (let _52_2444 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_2444) with
| (xxsym, xx) -> begin
(let _52_2447 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2447) with
| (ffsym, ff) -> begin
(let xx_has_type = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _116_1943 = (let _116_1942 = (let _116_1941 = (let _116_1940 = (let _116_1939 = (let _116_1938 = (let _116_1937 = (let _116_1936 = (let _116_1935 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _116_1935))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_1936))
in (xx_has_type, _116_1937))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1938))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _116_1939))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1940))
in (_116_1941, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1942))
in (_116_1943)::[]))
end))
end)))
in (let _52_2452 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2452) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _116_1945 = (let _116_1944 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _116_1944))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_1945))
in (let _52_2477 = (let tname_decl = (let _116_1949 = (let _116_1948 = (Support.All.pipe_right vars (Support.List.map (fun ( _52_2458 ) -> (match (_52_2458) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))))
in (let _116_1947 = (varops.next_id ())
in (tname, _116_1948, Microsoft_FStar_ToSMT_Term.Type_sort, _116_1947)))
in (constructor_or_logic_type_decl _116_1949))
in (let _52_2474 = (match (vars) with
| [] -> begin
(let _116_1953 = (let _116_1952 = (let _116_1951 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (Support.All.pipe_left (fun ( _116_1950 ) -> Some (_116_1950)) _116_1951))
in (push_free_tvar env t tname _116_1952))
in ([], _116_1953))
end
| _52_2462 -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _116_1954 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _116_1954))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match (((not (is_logical)) && (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_22 ) -> (match (_52_22) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _52_2469 -> begin
false
end)))))) with
| true -> begin
((ttok_app)::[])::((tapp)::[])::[]
end
| false -> begin
((ttok_app)::[])::[]
end)
in (let name_tok_corr = (let _116_1959 = (let _116_1958 = (let _116_1957 = (let _116_1956 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _116_1956))
in (Microsoft_FStar_ToSMT_Term.mkForall' _116_1957))
in (_116_1958, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1959))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_52_2474) with
| (tok_decls, env) -> begin
((Support.List.append tname_decl tok_decls), env)
end)))
in (match (_52_2477) with
| (decls, env) -> begin
(let kindingAx = (let _52_2480 = (encode_knd res env' tapp)
in (match (_52_2480) with
| (k, decls) -> begin
(let karr = (match (is_kind_arrow) with
| true -> begin
(let _116_1963 = (let _116_1962 = (let _116_1961 = (let _116_1960 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _116_1960))
in (_116_1961, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1962))
in (_116_1963)::[])
end
| false -> begin
[]
end)
in (let _116_1969 = (let _116_1968 = (let _116_1967 = (let _116_1966 = (let _116_1965 = (let _116_1964 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _116_1964))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_1965))
in (_116_1966, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_1967))
in (_116_1968)::[])
in (Support.List.append (Support.List.append decls karr) _116_1969)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _116_1970 = (projection_axioms tapp vars)
in (Support.List.append kindingAx _116_1970))
end
| false -> begin
(let _116_1977 = (let _116_1975 = (let _116_1973 = (let _116_1971 = (primitive_type_axioms t tname tapp)
in (Support.List.append kindingAx _116_1971))
in (let _116_1972 = (inversion_axioms tapp vars)
in (Support.List.append _116_1973 _116_1972)))
in (let _116_1974 = (projection_axioms tapp vars)
in (Support.List.append _116_1975 _116_1974)))
in (let _116_1976 = (pretype_axioms tapp vars)
in (Support.List.append _116_1977 _116_1976)))
end)
in (let g = (Support.List.append (Support.List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, _52_2487, _52_2489, _52_2491, _52_2493, _52_2495)) when (Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, t, _52_2501, quals, _52_2504, drange)) -> begin
(let _52_2511 = (new_term_constant_and_tok_from_lid env d)
in (match (_52_2511) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _52_2520 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(f, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_52_2520) with
| (formals, t_res) -> begin
(let _52_2523 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2523) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _52_2530 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_52_2530) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (Support.All.pipe_right names (Support.List.map (fun ( _52_23 ) -> (match (_52_23) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _116_1979 = (mk_typ_projector_name d a)
in (_116_1979, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _116_1980 = (mk_term_projector_name d x)
in (_116_1980, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _116_1982 = (let _116_1981 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _116_1981))
in (Support.All.pipe_right _116_1982 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _52_2544 = (encode_typ_pred None t env ddtok_tm)
in (match (_52_2544) with
| (tok_typing, decls3) -> begin
(let _52_2551 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_52_2551) with
| (vars', guards', env'', decls_formals, _52_2550) -> begin
(let _52_2556 = (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_52_2556) with
| (ty_pred', decls_pred) -> begin
(let guard' = (Microsoft_FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _52_2560 -> begin
(let _116_1984 = (let _116_1983 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _116_1983))
in (_116_1984)::[])
end)
in (let encode_elim = (fun ( _52_2563 ) -> (match (()) with
| () -> begin
(let _52_2566 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_52_2566) with
| (head, args) -> begin
(match ((let _116_1987 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _116_1987.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _52_2572 = (encode_args args env')
in (match (_52_2572) with
| (encoded_args, arg_decls) -> begin
(let _52_2596 = (Support.List.fold_left (fun ( _52_2576 ) ( arg ) -> (match (_52_2576) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _52_2584 = (let _116_1990 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _116_1990))
in (match (_52_2584) with
| (_52_2581, tv, env) -> begin
(let _116_1992 = (let _116_1991 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_116_1991)::eqns)
in (env, (tv)::arg_vars, _116_1992))
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _52_2591 = (let _116_1993 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _116_1993))
in (match (_52_2591) with
| (_52_2588, xv, env) -> begin
(let _116_1995 = (let _116_1994 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_116_1994)::eqns)
in (env, (xv)::arg_vars, _116_1995))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_52_2596) with
| (_52_2593, arg_vars, eqns) -> begin
(let arg_vars = (Support.List.rev arg_vars)
in (let ty = (Microsoft_FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (Support.List.map Microsoft_FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _116_2002 = (let _116_2001 = (let _116_2000 = (let _116_1999 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _116_1998 = (let _116_1997 = (let _116_1996 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards))
in (ty_pred, _116_1996))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_1997))
in ((ty_pred)::[], _116_1999, _116_1998)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2000))
in (_116_2001, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2002))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _116_2003 = (varops.fresh "x")
in (_116_2003, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _116_2012 = (let _116_2011 = (let _116_2010 = (let _116_2009 = (let _116_2004 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_116_2004)::[])
in (let _116_2008 = (let _116_2007 = (let _116_2006 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _116_2005 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_116_2006, _116_2005)))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_2007))
in (_116_2009, (x)::[], _116_2008)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2010))
in (_116_2011, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2012))))
end
| false -> begin
(let prec = (Support.All.pipe_right vars (Support.List.collect (fun ( v ) -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _116_2015 = (let _116_2014 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _116_2014 dapp))
in (_116_2015)::[])
end
| _52_2611 -> begin
(Support.All.failwith "unexpected sort")
end))))
in (let _116_2022 = (let _116_2021 = (let _116_2020 = (let _116_2019 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _116_2018 = (let _116_2017 = (let _116_2016 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _116_2016))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_2017))
in ((ty_pred)::[], _116_2019, _116_2018)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2020))
in (_116_2021, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2022)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _52_2615 -> begin
(let _52_2616 = (let _116_2025 = (let _116_2024 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _116_2023 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" _116_2024 _116_2023)))
in (Microsoft_FStar_Tc_Errors.warn drange _116_2025))
in ([], []))
end)
end))
end))
in (let _52_2620 = (encode_elim ())
in (match (_52_2620) with
| (decls2, elim) -> begin
(let g = (let _116_2050 = (let _116_2049 = (let _116_2034 = (let _116_2033 = (let _116_2032 = (let _116_2031 = (let _116_2030 = (let _116_2029 = (let _116_2028 = (let _116_2027 = (let _116_2026 = (Microsoft_FStar_Absyn_Print.sli d)
in (Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" _116_2026))
in Some (_116_2027))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _116_2028))
in Microsoft_FStar_ToSMT_Term.DeclFun (_116_2029))
in (_116_2030)::[])
in (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) _116_2031))
in (Support.List.append _116_2032 proxy_fresh))
in (Support.List.append _116_2033 decls_formals))
in (Support.List.append _116_2034 decls_pred))
in (let _116_2048 = (let _116_2047 = (let _116_2046 = (let _116_2038 = (let _116_2037 = (let _116_2036 = (let _116_2035 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _116_2035))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2036))
in (_116_2037, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2038))
in (let _116_2045 = (let _116_2044 = (let _116_2043 = (let _116_2042 = (let _116_2041 = (let _116_2040 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _116_2039 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _116_2040, _116_2039)))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2041))
in (_116_2042, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2043))
in (_116_2044)::[])
in (_116_2046)::_116_2045))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_116_2047)
in (Support.List.append _116_2049 _116_2048)))
in (Support.List.append _116_2050 elim))
in ((Support.List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _52_2624, _52_2626, _52_2628)) -> begin
(let _52_2633 = (encode_signature env ses)
in (match (_52_2633) with
| (g, env) -> begin
(let _52_2645 = (Support.All.pipe_right g (Support.List.partition (fun ( _52_24 ) -> (match (_52_24) with
| Microsoft_FStar_ToSMT_Term.Assume ((_52_2636, Some ("inversion axiom"))) -> begin
false
end
| _52_2642 -> begin
true
end))))
in (match (_52_2645) with
| (g', inversions) -> begin
(let _52_2654 = (Support.All.pipe_right g' (Support.List.partition (fun ( _52_25 ) -> (match (_52_25) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_52_2648) -> begin
true
end
| _52_2651 -> begin
false
end))))
in (match (_52_2654) with
| (decls, rest) -> begin
((Support.List.append (Support.List.append decls rest) inversions), env)
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((_52_2656, _52_2658, _52_2660, quals)) when (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_26 ) -> (match (_52_26) with
| (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _52_2672 -> begin
false
end)))) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((is_rec, bindings), _52_2677, _52_2679, quals)) -> begin
(let eta_expand = (fun ( binders ) ( formals ) ( body ) ( t ) -> (let nbinders = (Support.List.length binders)
in (let _52_2691 = (Support.Microsoft.FStar.Util.first_N nbinders formals)
in (match (_52_2691) with
| (formals, extra_formals) -> begin
(let subst = (Support.List.map2 (fun ( formal ) ( binder ) -> (match (((Support.Prims.fst formal), (Support.Prims.fst binder))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _116_2065 = (let _116_2064 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _116_2064))
in Support.Microsoft.FStar.Util.Inl (_116_2065))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _116_2067 = (let _116_2066 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _116_2066))
in Support.Microsoft.FStar.Util.Inr (_116_2067))
end
| _52_2705 -> begin
(Support.All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _116_2068 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (Support.All.pipe_right _116_2068 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _116_2074 = (let _116_2070 = (let _116_2069 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (Support.All.pipe_left Support.Prims.snd _116_2069))
in (body, _116_2070))
in (let _116_2073 = (let _116_2072 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (Support.All.pipe_left (fun ( _116_2071 ) -> Some (_116_2071)) _116_2072))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _116_2074 _116_2073 body.Microsoft_FStar_Absyn_Syntax.pos)))
in ((Support.List.append binders extra_formals), body))))
end))))
in (let destruct_bound_function = (fun ( flid ) ( t_norm ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _, _))) | (Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body))) -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let nformals = (Support.List.length formals)
in (let nbinders = (Support.List.length binders)
in (let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (match (((nformals < nbinders) && (Microsoft_FStar_Absyn_Util.is_total_comp c))) with
| true -> begin
(let _52_2743 = (Support.Microsoft.FStar.Util.first_N nformals binders)
in (match (_52_2743) with
| (bs0, rest) -> begin
(let tres = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tres)
end
| _52_2747 -> begin
(Support.All.failwith "impossible")
end)
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end
| false -> begin
(match ((nformals > nbinders)) with
| true -> begin
(let _52_2752 = (eta_expand binders formals body tres)
in (match (_52_2752) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end
| false -> begin
(binders, body, formals, tres)
end)
end))))
end
| _52_2754 -> begin
(let _116_2083 = (let _116_2082 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _116_2081 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _116_2082 _116_2081)))
in (Support.All.failwith _116_2083))
end)
end
| _52_2756 -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (let _52_2764 = (eta_expand [] formals e tres)
in (match (_52_2764) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _52_2766 -> begin
([], e, [], t_norm)
end)
end))
in (Support.All.try_with (fun ( _52_2768 ) -> (match (()) with
| () -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_27 ) -> (match (_52_27) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _52_2779 -> begin
false
end))))) with
| true -> begin
([], env)
end
| false -> begin
(match ((Support.All.pipe_right bindings (Support.Microsoft.FStar.Util.for_some (fun ( lb ) -> (Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp))))) with
| true -> begin
(let _116_2089 = (Support.All.pipe_right bindings (Support.List.collect (fun ( lb ) -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _116_2088 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _116_2088 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(raise (Let_rec_unencodeable))
end))))
in (_116_2089, env))
end
| false -> begin
(let _52_2799 = (Support.All.pipe_right bindings (Support.List.fold_left (fun ( _52_2786 ) ( lb ) -> (match (_52_2786) with
| (toks, typs, decls, env) -> begin
(let _52_2788 = (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(raise (Let_rec_unencodeable))
end
| false -> begin
()
end)
in (let t_norm = (let _116_2092 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.All.pipe_right _116_2092 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _52_2794 = (let _116_2093 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _116_2093 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_52_2794) with
| (tok, decl, env) -> begin
(let _116_2096 = (let _116_2095 = (let _116_2094 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_116_2094, tok))
in (_116_2095)::toks)
in (_116_2096, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_52_2799) with
| (toks, typs, decls, env) -> begin
(let toks = (Support.List.rev toks)
in (let decls = (Support.All.pipe_right (Support.List.rev decls) Support.List.flatten)
in (let typs = (Support.List.rev typs)
in (match (((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_28 ) -> (match (_52_28) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _52_2806 -> begin
false
end)))) || (Support.All.pipe_right typs (Support.Microsoft.FStar.Util.for_some (fun ( t ) -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (let _116_2099 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (Support.All.pipe_left Support.Prims.op_Negation _116_2099)))))))) with
| true -> begin
(decls, env)
end
| false -> begin
(match ((not (is_rec))) with
| true -> begin
(match ((bindings, typs, toks)) with
| ({Microsoft_FStar_Absyn_Syntax.lbname = _52_2814; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_2812; Microsoft_FStar_Absyn_Syntax.lbeff = _52_2810; Microsoft_FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _52_2830 = (destruct_bound_function flid t_norm e)
in (match (_52_2830) with
| (binders, body, formals, tres) -> begin
(let _52_2837 = (encode_binders None binders env)
in (match (_52_2837) with
| (vars, guards, env', binder_decls, _52_2836) -> begin
(let app = (match (vars) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _52_2840 -> begin
(let _116_2101 = (let _116_2100 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _116_2100))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_2101))
end)
in (let _52_2844 = (encode_exp body env')
in (match (_52_2844) with
| (body, decls2) -> begin
(let eqn = (let _116_2110 = (let _116_2109 = (let _116_2106 = (let _116_2105 = (let _116_2104 = (let _116_2103 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _116_2102 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_116_2103, _116_2102)))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_2104))
in ((app)::[], vars, _116_2105))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2106))
in (let _116_2108 = (let _116_2107 = (Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_116_2107))
in (_116_2109, _116_2108)))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2110))
in ((Support.List.append (Support.List.append (Support.List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _52_2847 -> begin
(Support.All.failwith "Impossible")
end)
end
| false -> begin
(let fuel = (let _116_2111 = (varops.fresh "fuel")
in (_116_2111, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _52_2864 = (Support.All.pipe_right toks (Support.List.fold_left (fun ( _52_2853 ) ( _52_2858 ) -> (match ((_52_2853, _52_2858)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _116_2116 = (let _116_2115 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (Support.All.pipe_left (fun ( _116_2114 ) -> Some (_116_2114)) _116_2115))
in (push_free_var env flid gtok _116_2116))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_52_2864) with
| (gtoks, env) -> begin
(let gtoks = (Support.List.rev gtoks)
in (let encode_one_binding = (fun ( env0 ) ( _52_2873 ) ( t_norm ) ( _52_2882 ) -> (match ((_52_2873, _52_2882)) with
| ((flid, f, ftok, g, gtok), {Microsoft_FStar_Absyn_Syntax.lbname = _52_2881; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_2879; Microsoft_FStar_Absyn_Syntax.lbeff = _52_2877; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _52_2887 = (destruct_bound_function flid t_norm e)
in (match (_52_2887) with
| (binders, body, formals, tres) -> begin
(let _52_2894 = (encode_binders None binders env)
in (match (_52_2894) with
| (vars, guards, env', binder_decls, _52_2893) -> begin
(let decl_g = (let _116_2127 = (let _116_2126 = (let _116_2125 = (Support.List.map Support.Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_116_2125)
in (g, _116_2126, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_116_2127))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _116_2130 = (let _116_2129 = (let _116_2128 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_116_2128)::vars_tm)
in (g, _116_2129))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_2130))
in (let gmax = (let _116_2133 = (let _116_2132 = (let _116_2131 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_116_2131)::vars_tm)
in (g, _116_2132))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_2133))
in (let _52_2904 = (encode_exp body env')
in (match (_52_2904) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _116_2142 = (let _116_2141 = (let _116_2138 = (let _116_2137 = (let _116_2136 = (let _116_2135 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _116_2134 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_116_2135, _116_2134)))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_2136))
in ((gsapp)::[], (fuel)::vars, _116_2137))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2138))
in (let _116_2140 = (let _116_2139 = (Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_116_2139))
in (_116_2141, _116_2140)))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2142))
in (let eqn_f = (let _116_2146 = (let _116_2145 = (let _116_2144 = (let _116_2143 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _116_2143))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2144))
in (_116_2145, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2146))
in (let eqn_g' = (let _116_2155 = (let _116_2154 = (let _116_2153 = (let _116_2152 = (let _116_2151 = (let _116_2150 = (let _116_2149 = (let _116_2148 = (let _116_2147 = (Microsoft_FStar_ToSMT_Term.n_fuel 0)
in (_116_2147)::vars_tm)
in (g, _116_2148))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_2149))
in (gsapp, _116_2150))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_2151))
in ((gsapp)::[], (fuel)::vars, _116_2152))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2153))
in (_116_2154, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2155))
in (let _52_2927 = (let _52_2914 = (encode_binders None formals env0)
in (match (_52_2914) with
| (vars, v_guards, env, binder_decls, _52_2913) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _116_2156 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _116_2156 ((fuel)::vars)))
in (let _116_2160 = (let _116_2159 = (let _116_2158 = (let _116_2157 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _116_2157))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2158))
in (_116_2159, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2160)))
in (let _52_2924 = (let _52_2921 = (encode_typ_pred None tres env gapp)
in (match (_52_2921) with
| (g_typing, d3) -> begin
(let _116_2168 = (let _116_2167 = (let _116_2166 = (let _116_2165 = (let _116_2164 = (let _116_2163 = (let _116_2162 = (let _116_2161 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_116_2161, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _116_2162))
in ((gapp)::[], (fuel)::vars, _116_2163))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2164))
in (_116_2165, None))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2166))
in (_116_2167)::[])
in (d3, _116_2168))
end))
in (match (_52_2924) with
| (aux_decls, typing_corr) -> begin
((Support.List.append binder_decls aux_decls), (Support.List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_52_2927) with
| (aux_decls, g_typing) -> begin
((Support.List.append (Support.List.append (Support.List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (Support.List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _52_2943 = (let _116_2171 = (Support.List.zip3 gtoks typs bindings)
in (Support.List.fold_left (fun ( _52_2931 ) ( _52_2935 ) -> (match ((_52_2931, _52_2935)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _52_2939 = (encode_one_binding env0 gtok ty bs)
in (match (_52_2939) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _116_2171))
in (match (_52_2943) with
| (decls, eqns, env0) -> begin
(let _52_2952 = (let _116_2173 = (Support.All.pipe_right decls Support.List.flatten)
in (Support.All.pipe_right _116_2173 (Support.List.partition (fun ( _52_29 ) -> (match (_52_29) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_52_2946) -> begin
true
end
| _52_2949 -> begin
false
end)))))
in (match (_52_2952) with
| (prefix_decls, rest) -> begin
(let eqns = (Support.List.rev eqns)
in ((Support.List.append (Support.List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end)
end))))
end))
end)
end)
end)) (fun ( _52_2767 ) -> (match (_52_2767) with
| Let_rec_unencodeable -> begin
(let msg = (let _116_2176 = (Support.All.pipe_right bindings (Support.List.map (fun ( lb ) -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (Support.All.pipe_right _116_2176 (Support.String.concat " and ")))
in (let decl = Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun ( env ) ( x ) ( t ) ( t_norm ) -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _52_2979 = (encode_free_var env x t t_norm [])
in (match (_52_2979) with
| (decls, env) -> begin
(let _52_2984 = (lookup_lid env x)
in (match (_52_2984) with
| (n, x', _52_2983) -> begin
((n, x'), decls, env)
end))
end))
end
| Some ((n, x, _52_2988)) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun ( env ) ( lid ) ( t ) -> (let _52_2996 = (encode_function_type_as_formula None t env)
in (match (_52_2996) with
| (form, decls) -> begin
(Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume ((form, Some ((Support.String.strcat "Lemma: " lid.Microsoft_FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun ( env ) ( lid ) ( tt ) ( t_norm ) ( quals ) -> (match (((let _116_2189 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (Support.All.pipe_left Support.Prims.op_Negation _116_2189)) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm))) with
| true -> begin
(let _52_3005 = (new_term_constant_and_tok_from_lid env lid)
in (match (_52_3005) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _52_3008)) -> begin
(Support.All.pipe_right binders (Support.List.map (fun ( _52_30 ) -> (match (_52_30) with
| (Support.Microsoft.FStar.Util.Inl (_52_3013), _52_3016) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_3019 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
end
| _52_3021 -> begin
[]
end)
in (let d = Microsoft_FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (let dd = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
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
(let encode_non_total_function_typ = (lid.Microsoft_FStar_Absyn_Syntax.nsstr <> "Prims")
in (let _52_3038 = (match ((Microsoft_FStar_Absyn_Util.function_formals t_norm)) with
| Some ((args, comp)) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _116_2191 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _116_2191))
end
| false -> begin
(args, (None, (Microsoft_FStar_Absyn_Util.comp_result comp)))
end)
end
| None -> begin
([], (None, t_norm))
end)
in (match (_52_3038) with
| (formals, (pre_opt, res_t)) -> begin
(let _52_3042 = (new_term_constant_and_tok_from_lid env lid)
in (match (_52_3042) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _52_3045 -> begin
(Microsoft_FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun ( guard ) ( encoded_res_t ) ( vapp ) ( vars ) -> (Support.All.pipe_right quals (Support.List.collect (fun ( _52_31 ) -> (match (_52_31) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _52_3061 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_52_3061) with
| (_52_3056, (xxsym, _52_3059)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _116_2208 = (let _116_2207 = (let _116_2206 = (let _116_2205 = (let _116_2204 = (let _116_2203 = (let _116_2202 = (let _116_2201 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _116_2201))
in (vapp, _116_2202))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_2203))
in ((vapp)::[], vars, _116_2204))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2205))
in (_116_2206, Some ("Discriminator equation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2207))
in (_116_2208)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _52_3074 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_52_3074) with
| (_52_3069, (xxsym, _52_3072)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _116_2210 = (let _116_2209 = (mk_term_projector_name d f)
in (_116_2209, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_2210))
in (let _116_2215 = (let _116_2214 = (let _116_2213 = (let _116_2212 = (let _116_2211 = (Microsoft_FStar_ToSMT_Term.mkEq (vapp, prim_app))
in ((vapp)::[], vars, _116_2211))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2212))
in (_116_2213, Some ("Projector equation")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2214))
in (_116_2215)::[])))
end))
end
| _52_3078 -> begin
[]
end)))))
in (let _52_3085 = (encode_binders None formals env)
in (match (_52_3085) with
| (vars, guards, env', decls1, _52_3084) -> begin
(let _52_3094 = (match (pre_opt) with
| None -> begin
(let _116_2216 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_116_2216, decls1))
end
| Some (p) -> begin
(let _52_3091 = (encode_formula p env')
in (match (_52_3091) with
| (g, ds) -> begin
(let _116_2217 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_116_2217, (Support.List.append decls1 ds)))
end))
end)
in (match (_52_3094) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _116_2219 = (let _116_2218 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _116_2218))
in (Microsoft_FStar_ToSMT_Term.mkApp _116_2219))
in (let _52_3125 = (let vname_decl = (let _116_2222 = (let _116_2221 = (Support.All.pipe_right formals (Support.List.map (fun ( _52_32 ) -> (match (_52_32) with
| (Support.Microsoft.FStar.Util.Inl (_52_3099), _52_3102) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_3105 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _116_2221, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_116_2222))
in (let _52_3112 = (let env = (let _52_3107 = env
in {bindings = _52_3107.bindings; depth = _52_3107.depth; tcenv = _52_3107.tcenv; warn = _52_3107.warn; cache = _52_3107.cache; nolabels = _52_3107.nolabels; use_zfuel_name = _52_3107.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((not ((head_normal env tt)))) with
| true -> begin
(encode_typ_pred None tt env vtok_tm)
end
| false -> begin
(encode_typ_pred None t_norm env vtok_tm)
end))
in (match (_52_3112) with
| (tok_typing, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _52_3122 = (match (formals) with
| [] -> begin
(let _116_2226 = (let _116_2225 = (let _116_2224 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Support.All.pipe_left (fun ( _116_2223 ) -> Some (_116_2223)) _116_2224))
in (push_free_var env lid vname _116_2225))
in ((Support.List.append decls2 ((tok_typing)::[])), _116_2226))
end
| _52_3116 -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _116_2227 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _116_2227))
in (let name_tok_corr = (let _116_2231 = (let _116_2230 = (let _116_2229 = (let _116_2228 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _116_2228))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2229))
in (_116_2230, None))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2231))
in ((Support.List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_52_3122) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_52_3125) with
| (decls2, env) -> begin
(let _52_3133 = (let res_t = (Microsoft_FStar_Absyn_Util.compress_typ res_t)
in (let _52_3129 = (encode_typ_term res_t env')
in (match (_52_3129) with
| (encoded_res_t, decls) -> begin
(let _116_2232 = (Microsoft_FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _116_2232, decls))
end)))
in (match (_52_3133) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _116_2236 = (let _116_2235 = (let _116_2234 = (let _116_2233 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _116_2233))
in (Microsoft_FStar_ToSMT_Term.mkForall _116_2234))
in (_116_2235, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2236))
in (let g = (let _116_2238 = (let _116_2237 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_116_2237)
in (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) _116_2238))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end)
end))
and encode_signature = (fun ( env ) ( ses ) -> (Support.All.pipe_right ses (Support.List.fold_left (fun ( _52_3140 ) ( se ) -> (match (_52_3140) with
| (g, env) -> begin
(let _52_3144 = (encode_sigelt env se)
in (match (_52_3144) with
| (g', env) -> begin
((Support.List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun ( env ) ( bindings ) -> (let encode_binding = (fun ( b ) ( _52_3151 ) -> (match (_52_3151) with
| (decls, env) -> begin
(match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t0)) -> begin
(let _52_3159 = (new_term_constant env x)
in (match (_52_3159) with
| (xxsym, xx, env') -> begin
(let t1 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.EtaArgs)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _52_3161 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _116_2253 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _116_2252 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _116_2251 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.fprint3 "Normalized %s : %s to %s\n" _116_2253 _116_2252 _116_2251))))
end
| false -> begin
()
end)
in (let _52_3165 = (encode_typ_pred None t1 env xx)
in (match (_52_3165) with
| (t, decls') -> begin
(let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _116_2257 = (let _116_2256 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _116_2255 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _116_2254 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" _116_2256 _116_2255 _116_2254))))
in Some (_116_2257))
end
| false -> begin
None
end)
in (let g = (Support.List.append (Support.List.append ((Microsoft_FStar_ToSMT_Term.DeclFun ((xxsym, [], Microsoft_FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((Microsoft_FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((Support.List.append decls g), env')))
end))))
end))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let _52_3175 = (new_typ_constant env a)
in (match (_52_3175) with
| (aasym, aa, env') -> begin
(let _52_3178 = (encode_knd k env aa)
in (match (_52_3178) with
| (k, decls') -> begin
(let g = (let _116_2263 = (let _116_2262 = (let _116_2261 = (let _116_2260 = (let _116_2259 = (let _116_2258 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_116_2258))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _116_2259))
in Microsoft_FStar_ToSMT_Term.DeclFun (_116_2260))
in (_116_2261)::[])
in (Support.List.append _116_2262 decls'))
in (Support.List.append _116_2263 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((Support.List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((x, t)) -> begin
(let t_norm = (whnf env t)
in (let _52_3187 = (encode_free_var env x t t_norm [])
in (match (_52_3187) with
| (g, env') -> begin
((Support.List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _52_3192 = (encode_sigelt env se)
in (match (_52_3192) with
| (g, env') -> begin
((Support.List.append decls g), env')
end))
end)
end))
in (Support.List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun ( labs ) -> (let prefix = (Support.All.pipe_right labs (Support.List.map (fun ( _52_3199 ) -> (match (_52_3199) with
| (l, _52_3196, _52_3198) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Support.Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (Support.All.pipe_right labs (Support.List.collect (fun ( _52_3206 ) -> (match (_52_3206) with
| (l, _52_3203, _52_3205) -> begin
(let _116_2271 = (Support.All.pipe_left (fun ( _116_2267 ) -> Microsoft_FStar_ToSMT_Term.Echo (_116_2267)) (Support.Prims.fst l))
in (let _116_2270 = (let _116_2269 = (let _116_2268 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_116_2268))
in (_116_2269)::[])
in (_116_2271)::_116_2270))
end))))
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun ( tcenv ) -> (let _116_2276 = (let _116_2275 = (let _116_2274 = (Support.Microsoft.FStar.Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _116_2274; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_116_2275)::[])
in (Support.ST.op_Colon_Equals last_env _116_2276)))

let get_env = (fun ( tcenv ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "No env; call init first!")
end
| e::_52_3212 -> begin
(let _52_3215 = e
in {bindings = _52_3215.bindings; depth = _52_3215.depth; tcenv = tcenv; warn = _52_3215.warn; cache = _52_3215.cache; nolabels = _52_3215.nolabels; use_zfuel_name = _52_3215.use_zfuel_name; encode_non_total_function_typ = _52_3215.encode_non_total_function_typ})
end))

let set_env = (fun ( env ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Empty env stack")
end
| _52_3221::tl -> begin
(Support.ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun ( _52_3223 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (Support.Microsoft.FStar.Util.smap_copy hd.cache)
in (let top = (let _52_3229 = hd
in {bindings = _52_3229.bindings; depth = _52_3229.depth; tcenv = _52_3229.tcenv; warn = _52_3229.warn; cache = refs; nolabels = _52_3229.nolabels; use_zfuel_name = _52_3229.use_zfuel_name; encode_non_total_function_typ = _52_3229.encode_non_total_function_typ})
in (Support.ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env = (fun ( _52_3232 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Popping an empty stack")
end
| _52_3236::tl -> begin
(Support.ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env = (fun ( _52_3238 ) -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun ( _52_3239 ) -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun ( _52_3240 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| hd::_52_3243::tl -> begin
(Support.ST.op_Colon_Equals last_env ((hd)::tl))
end
| _52_3248 -> begin
(Support.All.failwith "Impossible")
end)
end))

let init = (fun ( tcenv ) -> (let _52_3250 = (init_env tcenv)
in (let _52_3252 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun ( msg ) -> (let _52_3255 = (push_env ())
in (let _52_3257 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun ( msg ) -> (let _52_3260 = (let _116_2297 = (pop_env ())
in (Support.All.pipe_left Support.Prims.ignore _116_2297))
in (let _52_3262 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun ( msg ) -> (let _52_3265 = (mark_env ())
in (let _52_3267 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun ( msg ) -> (let _52_3270 = (reset_mark_env ())
in (let _52_3272 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun ( msg ) -> (let _52_3275 = (commit_mark_env ())
in (let _52_3277 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun ( tcenv ) ( se ) -> (let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _116_2311 = (let _116_2310 = (let _116_2309 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.String.strcat "encoding sigelt " _116_2309))
in Microsoft_FStar_ToSMT_Term.Caption (_116_2310))
in (_116_2311)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _52_3286 = (encode_sigelt env se)
in (match (_52_3286) with
| (decls, env) -> begin
(let _52_3287 = (set_env env)
in (let _116_2312 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _116_2312)))
end)))))

let encode_modul = (fun ( tcenv ) ( modul ) -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _52_3292 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _116_2317 = (Support.All.pipe_right (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name _116_2317))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _52_3299 = (encode_signature (let _52_3295 = env
in {bindings = _52_3295.bindings; depth = _52_3295.depth; tcenv = _52_3295.tcenv; warn = false; cache = _52_3295.cache; nolabels = _52_3295.nolabels; use_zfuel_name = _52_3295.use_zfuel_name; encode_non_total_function_typ = _52_3295.encode_non_total_function_typ}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_52_3299) with
| (decls, env) -> begin
(let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let msg = (Support.String.strcat "Externals for " name)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _52_3305 = (set_env (let _52_3303 = env
in {bindings = _52_3303.bindings; depth = _52_3303.depth; tcenv = _52_3303.tcenv; warn = true; cache = _52_3303.cache; nolabels = _52_3303.nolabels; use_zfuel_name = _52_3303.use_zfuel_name; encode_non_total_function_typ = _52_3303.encode_non_total_function_typ}))
in (let _52_3307 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun ( tcenv ) ( q ) -> (let _52_3312 = (let _116_2326 = (let _116_2325 = (let _116_2324 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _116_2324))
in (Support.Microsoft.FStar.Util.format1 "Starting query at %s" _116_2325))
in (push _116_2326))
in (let pop = (fun ( _52_3315 ) -> (match (()) with
| () -> begin
(let _116_2331 = (let _116_2330 = (let _116_2329 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _116_2329))
in (Support.Microsoft.FStar.Util.format1 "Ending query at %s" _116_2330))
in (pop _116_2331))
end))
in (let _52_3345 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun ( bs ) ( b ) -> (b)::bs) [])
in (let _52_3328 = (let _116_2335 = (Support.List.filter (fun ( _52_33 ) -> (match (_52_33) with
| Microsoft_FStar_Tc_Env.Binding_sig (_52_3322) -> begin
false
end
| _52_3325 -> begin
true
end)) bindings)
in (encode_env_bindings env _116_2335))
in (match (_52_3328) with
| (env_decls, env) -> begin
(let _52_3329 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _116_2336 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" _116_2336))
end
| false -> begin
()
end)
in (let _52_3334 = (encode_formula_with_labels q env)
in (match (_52_3334) with
| (phi, labels, qdecls) -> begin
(let _52_3337 = (encode_labels labels)
in (match (_52_3337) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Support.List.append (Support.List.append env_decls label_prefix) qdecls)
in (let qry = (let _116_2338 = (let _116_2337 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_116_2337, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2338))
in (let suffix = (Support.List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_52_3345) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume (({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.False, _52_3352)); Microsoft_FStar_ToSMT_Term.hash = _52_3349; Microsoft_FStar_ToSMT_Term.freevars = _52_3347}, _52_3357)) -> begin
(let _52_3360 = (pop ())
in ())
end
| _52_3363 when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
(let _52_3364 = (pop ())
in ())
end
| Microsoft_FStar_ToSMT_Term.Assume ((q, _52_3368)) -> begin
(let fresh = ((Support.String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _52_3372 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun ( p ) ( _52_3378 ) -> (match (_52_3378) with
| (n, i) -> begin
(let _116_2361 = (let _116_2360 = (let _116_2345 = (let _116_2344 = (Support.Microsoft.FStar.Util.string_of_int n)
in (let _116_2343 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _116_2344 _116_2343)))
in Microsoft_FStar_ToSMT_Term.Caption (_116_2345))
in (let _116_2359 = (let _116_2358 = (let _116_2350 = (let _116_2349 = (let _116_2348 = (let _116_2347 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _116_2346 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_116_2347, _116_2346)))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_2348))
in (_116_2349, None))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2350))
in (let _116_2357 = (let _116_2356 = (let _116_2355 = (let _116_2354 = (let _116_2353 = (let _116_2352 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _116_2351 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_116_2352, _116_2351)))
in (Microsoft_FStar_ToSMT_Term.mkEq _116_2353))
in (_116_2354, None))
in Microsoft_FStar_ToSMT_Term.Assume (_116_2355))
in (_116_2356)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_116_2358)::_116_2357))
in (_116_2360)::_116_2359))
in (Support.List.append _116_2361 suffix))
end))
in (let check = (fun ( p ) -> (let initial_config = (let _116_2365 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _116_2364 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_116_2365, _116_2364)))
in (let alt_configs = (let _116_2384 = (let _116_2383 = (match (((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel))) with
| true -> begin
(let _116_2368 = (let _116_2367 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _116_2366 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_116_2367, _116_2366)))
in (_116_2368)::[])
end
| false -> begin
[]
end)
in (let _116_2382 = (let _116_2381 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2) > (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _116_2371 = (let _116_2370 = ((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2)
in (let _116_2369 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_116_2370, _116_2369)))
in (_116_2371)::[])
end
| false -> begin
[]
end)
in (let _116_2380 = (let _116_2379 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) > (Support.ST.read Microsoft_FStar_Options.initial_fuel)) && ((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel)))) with
| true -> begin
(let _116_2374 = (let _116_2373 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _116_2372 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_116_2373, _116_2372)))
in (_116_2374)::[])
end
| false -> begin
[]
end)
in (let _116_2378 = (let _116_2377 = (match (((Support.ST.read Microsoft_FStar_Options.min_fuel) < (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _116_2376 = (let _116_2375 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (_116_2375, 1))
in (_116_2376)::[])
end
| false -> begin
[]
end)
in (_116_2377)::[])
in (_116_2379)::_116_2378))
in (_116_2381)::_116_2380))
in (_116_2383)::_116_2382))
in (Support.List.flatten _116_2384))
in (let report = (fun ( errs ) -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", Microsoft_FStar_Absyn_Syntax.dummyRange))::[]
end
| _52_3387 -> begin
errs
end)
in (let _52_3389 = (match ((Support.ST.read Microsoft_FStar_Options.print_fuels)) with
| true -> begin
(let _116_2392 = (let _116_2387 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Microsoft.FStar.Range.string_of_range _116_2387))
in (let _116_2391 = (let _116_2388 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (Support.All.pipe_right _116_2388 Support.Microsoft.FStar.Util.string_of_int))
in (let _116_2390 = (let _116_2389 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (Support.All.pipe_right _116_2389 Support.Microsoft.FStar.Util.string_of_int))
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _116_2392 _116_2391 _116_2390))))
end
| false -> begin
()
end)
in (Microsoft_FStar_Tc_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun ( p ) ( errs ) ( _52_34 ) -> (match (_52_34) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _116_2403 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _116_2403 (cb mi p [])))
end
| _52_3401 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _116_2405 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _116_2405 (fun ( _52_3407 ) -> (match (_52_3407) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _52_3410 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun ( _52_3413 ) ( p ) ( alt ) ( _52_3418 ) -> (match ((_52_3413, _52_3418)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
(match (ok) with
| true -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_fuels)) with
| true -> begin
(let _116_2413 = (let _116_2410 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Microsoft.FStar.Range.string_of_range _116_2410))
in (let _116_2412 = (Support.Microsoft.FStar.Util.string_of_int prev_fuel)
in (let _116_2411 = (Support.Microsoft.FStar.Util.string_of_int prev_ifuel)
in (Support.Microsoft.FStar.Util.fprint3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _116_2413 _116_2412 _116_2411))))
end
| false -> begin
()
end)
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _116_2414 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _116_2414 (cb initial_config p alt_configs))))))))
in (let process_query = (fun ( q ) -> (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let _52_3423 = (let _116_2420 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _116_2420 q))
in (match (_52_3423) with
| (b, cb) -> begin
(match (b) with
| true -> begin
(Microsoft_FStar_ToSMT_SplitQueryCases.handle_query cb check)
end
| false -> begin
(check q)
end)
end))
end
| false -> begin
(check q)
end))
in (let _52_3424 = (match ((Support.ST.read Microsoft_FStar_Options.admit_smt_queries)) with
| true -> begin
()
end
| false -> begin
(process_query qry)
end)
in (pop ())))))))
end)
end)))))

let is_trivial = (fun ( tcenv ) ( q ) -> (let env = (get_env tcenv)
in (let _52_3429 = (push "query")
in (let _52_3436 = (encode_formula_with_labels q env)
in (match (_52_3436) with
| (f, _52_3433, _52_3435) -> begin
(let _52_3437 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _52_3441)) -> begin
true
end
| _52_3445 -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = commit_mark; Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun ( _52_3446 ) -> ()); Microsoft_FStar_Tc_Env.push = (fun ( _52_3448 ) -> ()); Microsoft_FStar_Tc_Env.pop = (fun ( _52_3450 ) -> ()); Microsoft_FStar_Tc_Env.mark = (fun ( _52_3452 ) -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun ( _52_3454 ) -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun ( _52_3456 ) -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun ( _52_3458 ) ( _52_3460 ) -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun ( _52_3462 ) ( _52_3464 ) -> ()); Microsoft_FStar_Tc_Env.solve = (fun ( _52_3466 ) ( _52_3468 ) -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun ( _52_3470 ) ( _52_3472 ) -> false); Microsoft_FStar_Tc_Env.finish = (fun ( _52_3474 ) -> ()); Microsoft_FStar_Tc_Env.refresh = (fun ( _52_3475 ) -> ())}





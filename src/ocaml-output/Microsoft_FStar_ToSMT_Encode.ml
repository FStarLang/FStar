
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

let mk_typ_projector_name = (fun ( lid ) ( a ) -> (let _123_14 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _123_14)))

let mk_term_projector_name = (fun ( lid ) ( a ) -> (let a = (let _123_19 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _123_19; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _123_20 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _123_20))))

let primitive_projector_by_pos = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _52_62 ) -> (match (()) with
| () -> begin
(let _123_30 = (let _123_29 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" _123_29 lid.Microsoft_FStar_Absyn_Syntax.str))
in (Support.All.failwith _123_30))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _123_31 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _123_31.Microsoft_FStar_Absyn_Syntax.n)) with
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

let mk_term_projector_name_by_pos = (fun ( lid ) ( i ) -> (let _123_37 = (let _123_36 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _123_36))
in (Support.All.pipe_left escape _123_37)))

let mk_typ_projector = (fun ( lid ) ( a ) -> (let _123_43 = (let _123_42 = (mk_typ_projector_name lid a)
in (_123_42, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _123_43)))

let mk_term_projector = (fun ( lid ) ( a ) -> (let _123_49 = (let _123_48 = (mk_term_projector_name lid a)
in (_123_48, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _123_49)))

let mk_term_projector_by_pos = (fun ( lid ) ( i ) -> (let _123_55 = (let _123_54 = (mk_term_projector_name_by_pos lid i)
in (_123_54, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _123_55)))

let mk_data_tester = (fun ( env ) ( l ) ( x ) -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let is_Mkvarops_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun ( _52_101 ) -> (match (()) with
| () -> begin
(let _123_159 = (Support.Microsoft.FStar.Util.smap_create 100)
in (let _123_158 = (Support.Microsoft.FStar.Util.smap_create 100)
in (_123_159, _123_158)))
end))
in (let scopes = (let _123_161 = (let _123_160 = (new_scope ())
in (_123_160)::[])
in (Support.Microsoft.FStar.Util.mk_ref _123_161))
in (let mk_unique = (fun ( y ) -> (let y = (escape y)
in (let y = (match ((let _123_165 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _123_165 (fun ( _52_109 ) -> (match (_52_109) with
| (names, _52_108) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_52_112) -> begin
(let _52_114 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _123_167 = (let _123_166 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _123_166))
in (Support.String.strcat (Support.String.strcat y "__") _123_167)))
end)
in (let top_scope = (let _123_169 = (let _123_168 = (Support.ST.read scopes)
in (Support.List.hd _123_168))
in (Support.All.pipe_left Support.Prims.fst _123_169))
in (let _52_118 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun ( pp ) ( rn ) -> (let _123_175 = (let _123_174 = (Support.All.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.String.strcat _123_174 "__"))
in (Support.String.strcat _123_175 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun ( lid ) -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun ( _52_126 ) -> (match (()) with
| () -> begin
(let _52_127 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
end))
in (let fresh = (fun ( pfx ) -> (let _123_183 = (let _123_182 = (next_id ())
in (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int _123_182))
in (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx _123_183)))
in (let string_const = (fun ( s ) -> (match ((let _123_187 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _123_187 (fun ( _52_136 ) -> (match (_52_136) with
| (_52_134, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _123_188 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxString _123_188))
in (let top_scope = (let _123_190 = (let _123_189 = (Support.ST.read scopes)
in (Support.List.hd _123_189))
in (Support.All.pipe_left Support.Prims.snd _123_190))
in (let _52_143 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun ( _52_146 ) -> (match (()) with
| () -> begin
(let _123_195 = (let _123_194 = (new_scope ())
in (let _123_193 = (Support.ST.read scopes)
in (_123_194)::_123_193))
in (Support.ST.op_Colon_Equals scopes _123_195))
end))
in (let pop = (fun ( _52_148 ) -> (match (()) with
| () -> begin
(let _123_199 = (let _123_198 = (Support.ST.read scopes)
in (Support.List.tl _123_198))
in (Support.ST.op_Colon_Equals scopes _123_199))
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

let unmangle = (fun ( x ) -> (let _123_215 = (let _123_214 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _123_213 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_123_214, _123_213)))
in (Microsoft_FStar_Absyn_Util.mkbvd _123_215)))

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

let print_env = (fun ( e ) -> (let _123_301 = (Support.All.pipe_right e.bindings (Support.List.map (fun ( _52_2 ) -> (match (_52_2) with
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
in (Support.All.pipe_right _123_301 (Support.String.concat ", "))))

let lookup_binding = (fun ( env ) ( f ) -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun ( env ) ( t ) -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _123_311 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_123_311))
end
| false -> begin
None
end))

let fresh_fvar = (fun ( x ) ( s ) -> (let xsym = (varops.fresh x)
in (let _123_316 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _123_316))))

let gen_term_var = (fun ( env ) ( x ) -> (let ysym = (let _123_321 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@x" _123_321))
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
(let _123_336 = (let _123_335 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" _123_335))
in (Support.All.failwith _123_336))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun ( env ) ( x ) -> (let ysym = (let _123_341 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@a" _123_341))
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
(let _123_356 = (let _123_355 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" _123_355))
in (Support.All.failwith _123_356))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _123_367 = (let _52_295 = env
in (let _123_366 = (let _123_365 = (let _123_364 = (let _123_363 = (let _123_362 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _123_361 ) -> Some (_123_361)) _123_362))
in (x, fname, _123_363, None))
in Binding_fvar (_123_364))
in (_123_365)::env.bindings)
in {bindings = _123_366; depth = _52_295.depth; tcenv = _52_295.tcenv; warn = _52_295.warn; cache = _52_295.cache; nolabels = _52_295.nolabels; use_zfuel_name = _52_295.use_zfuel_name; encode_non_total_function_typ = _52_295.encode_non_total_function_typ}))
in (fname, ftok, _123_367)))))

let try_lookup_lid = (fun ( env ) ( a ) -> (lookup_binding env (fun ( _52_5 ) -> (match (_52_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _52_307 -> begin
None
end))))

let lookup_lid = (fun ( env ) ( a ) -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _123_378 = (let _123_377 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _123_377))
in (Support.All.failwith _123_378))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _52_317.depth; tcenv = _52_317.tcenv; warn = _52_317.warn; cache = _52_317.cache; nolabels = _52_317.nolabels; use_zfuel_name = _52_317.use_zfuel_name; encode_non_total_function_typ = _52_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun ( env ) ( x ) ( f ) -> (let _52_326 = (lookup_lid env x)
in (match (_52_326) with
| (t1, t2, _52_325) -> begin
(let t3 = (let _123_395 = (let _123_394 = (let _123_393 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_123_393)::[])
in (f, _123_394))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_395))
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
(match ((let _123_399 = (let _123_398 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (Support.All.pipe_right _123_398 Support.Prims.fst))
in (Support.Microsoft.FStar.Util.starts_with _123_399 "fuel"))) with
| true -> begin
(let _123_400 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _123_400 fuel))
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
(let _123_402 = (let _123_401 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _123_401))
in (Support.All.failwith _123_402))
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
in (let _123_417 = (let _52_392 = env
in (let _123_416 = (let _123_415 = (let _123_414 = (let _123_413 = (let _123_412 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _123_411 ) -> Some (_123_411)) _123_412))
in (x, fname, _123_413))
in Binding_ftvar (_123_414))
in (_123_415)::env.bindings)
in {bindings = _123_416; depth = _52_392.depth; tcenv = _52_392.tcenv; warn = _52_392.warn; cache = _52_392.cache; nolabels = _52_392.nolabels; use_zfuel_name = _52_392.use_zfuel_name; encode_non_total_function_typ = _52_392.encode_non_total_function_typ}))
in (fname, ftok, _123_417)))))

let lookup_tlid = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_6 ) -> (match (_52_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _52_403 -> begin
None
end)))) with
| None -> begin
(let _123_424 = (let _123_423 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _123_423))
in (Support.All.failwith _123_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _52_411.depth; tcenv = _52_411.tcenv; warn = _52_411.warn; cache = _52_411.cache; nolabels = _52_411.nolabels; use_zfuel_name = _52_411.use_zfuel_name; encode_non_total_function_typ = _52_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun ( env ) ( a ) -> (match ((let _123_435 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _123_435 Support.Prims.snd))) with
| None -> begin
(let _123_437 = (let _123_436 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _123_436))
in (Support.All.failwith _123_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun ( env ) ( a ) -> (let _123_440 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _123_440 Support.Prims.fst)))

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
(let pats = (Support.All.pipe_right pats (Support.List.map (fun ( p ) -> (match (p.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var ("HasType"), args)) -> begin
(Microsoft_FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _52_454 -> begin
p
end))))
in (let vars = ((fsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars
in (Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))))
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
(let _123_456 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _123_456 Support.Option.isNone))
end
| _52_492 -> begin
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

let trivial_post = (fun ( t ) -> (let _123_478 = (let _123_477 = (let _123_475 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_123_475)::[])
in (let _123_476 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_123_477, _123_476)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _123_478 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun ( e ) ( vars ) -> (Support.All.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _123_485 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _123_485))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _123_486 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _123_486))
end
| _52_509 -> begin
(let _123_487 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _123_487))
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
(let _123_500 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _123_500))
end
| _52_524 -> begin
(let _123_501 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _123_501))
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
| _52_543 -> begin
false
end))

let is_eta = (fun ( env ) ( vars ) ( t ) -> (let rec aux = (fun ( t ) ( xs ) -> (match ((t.Microsoft_FStar_ToSMT_Term.tm, xs)) with
| (Microsoft_FStar_ToSMT_Term.App ((app, f::{Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.FreeV (y); Microsoft_FStar_ToSMT_Term.hash = _52_554; Microsoft_FStar_ToSMT_Term.freevars = _52_552}::[])), x::xs) when ((is_app app) && (Microsoft_FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var (f), args)), _52_572) -> begin
(match ((((Support.List.length args) = (Support.List.length vars)) && (Support.List.forall2 (fun ( a ) ( v ) -> (match (a.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (fv) -> begin
(Microsoft_FStar_ToSMT_Term.fv_eq fv v)
end
| _52_579 -> begin
false
end)) args vars))) with
| true -> begin
(tok_of_name env f)
end
| false -> begin
None
end)
end
| (_52_581, []) -> begin
(let fvs = (Microsoft_FStar_ToSMT_Term.free_variables t)
in (match ((Support.All.pipe_right fvs (Support.List.for_all (fun ( fv ) -> (not ((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_ToSMT_Term.fv_eq fv) vars))))))) with
| true -> begin
Some (t)
end
| false -> begin
None
end))
end
| _52_587 -> begin
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
(let _123_557 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _123_557))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _123_558 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _123_558))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _123_559 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _123_559))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _123_563 = (let _123_562 = (let _123_561 = (let _123_560 = (Microsoft_FStar_ToSMT_Term.mkInteger' i)
in (Microsoft_FStar_ToSMT_Term.boxInt _123_560))
in (_123_561)::[])
in ("Int32.Int32", _123_562))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_563))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _52_609)) -> begin
(let _123_564 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_bytes bytes)
in (varops.string_const _123_564))
end
| c -> begin
(let _123_566 = (let _123_565 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" _123_565))
in (Support.All.failwith _123_566))
end))

let as_function_typ = (fun ( env ) ( t0 ) -> (let rec aux = (fun ( norm ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_52_620) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_623) -> begin
(let _123_575 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _123_575))
end
| _52_626 -> begin
(match (norm) with
| true -> begin
(let _123_576 = (whnf env t)
in (aux false _123_576))
end
| false -> begin
(let _123_579 = (let _123_578 = (Support.Microsoft.FStar.Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _123_577 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Support.Microsoft.FStar.Util.format2 "(%s) Expected a function typ; got %s" _123_578 _123_577)))
in (Support.All.failwith _123_579))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun ( k ) ( env ) -> (match ((let _123_611 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _123_611.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_52_631, k0)) -> begin
(let _52_635 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _123_613 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _123_612 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _123_613 _123_612)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _52_639)) -> begin
(let _123_615 = (let _123_614 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _123_614))
in (_123_615, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, kbody)) -> begin
(let tsym = (let _123_616 = (varops.fresh "t")
in (_123_616, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let t = (Microsoft_FStar_ToSMT_Term.mkFreeV tsym)
in (let _52_654 = (encode_binders None bs env)
in (match (_52_654) with
| (vars, guards, env', decls, _52_653) -> begin
(let app = (mk_ApplyT t vars)
in (let _52_658 = (encode_knd kbody env' app)
in (match (_52_658) with
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
| _52_677 -> begin
(let _123_625 = (let _123_624 = (let _123_623 = (Microsoft_FStar_ToSMT_Term.mk_PreKind app)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _123_623))
in (_123_624, body))
in (Microsoft_FStar_ToSMT_Term.mkAnd _123_625))
end)
in (let _123_627 = (let _123_626 = (Microsoft_FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _123_626))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_627)))))
end
| _52_680 -> begin
(Support.All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _123_629 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (Support.All.pipe_right _123_629 (Support.List.filter (fun ( _52_685 ) -> (match (_52_685) with
| (x, _52_684) -> begin
(x <> (Support.Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((k', sorts, _52_691)) -> begin
(let _123_632 = (let _123_631 = (let _123_630 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _123_630))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_631))
in (_123_632, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _123_633 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_123_633))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _123_635 = (let _123_634 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _123_634))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_635))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _123_644 = (let _123_643 = (let _123_642 = (let _123_641 = (let _123_640 = (let _123_639 = (let _123_638 = (let _123_637 = (let _123_636 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _123_636))
in (_123_637, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _123_638))
in (t_has_k, _123_639))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_640))
in ((t_has_k)::[], (tsym)::cvars, _123_641))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_642))
in (_123_643, Some ((Support.String.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_123_644))
in (let k_decls = (Support.List.append (Support.List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _52_703 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _52_706 -> begin
(let _123_646 = (let _123_645 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" _123_645))
in (Support.All.failwith _123_646))
end))
and encode_knd = (fun ( k ) ( env ) ( t ) -> (let _52_712 = (encode_knd_term k env)
in (match (_52_712) with
| (k, decls) -> begin
(let _123_650 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_123_650, decls))
end)))
and encode_binders = (fun ( fuel_opt ) ( bs ) ( env ) -> (let _52_716 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _123_654 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" _123_654))
end
| false -> begin
()
end)
in (let _52_766 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _52_723 ) ( b ) -> (match (_52_723) with
| (vars, guards, env, decls, names) -> begin
(let _52_760 = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = a; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _52_726}) -> begin
(let a = (unmangle a)
in (let _52_735 = (gen_typ_var env a)
in (match (_52_735) with
| (aasym, aa, env') -> begin
(let _52_736 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _123_658 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _123_657 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _123_658 aasym _123_657)))
end
| false -> begin
()
end)
in (let _52_740 = (encode_knd k env aa)
in (match (_52_740) with
| (guard_a_k, decls') -> begin
((aasym, Microsoft_FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', Support.Microsoft.FStar.Util.Inl (a))
end)))
end)))
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _52_742}) -> begin
(let x = (unmangle x)
in (let _52_751 = (gen_term_var env x)
in (match (_52_751) with
| (xxsym, xx, env') -> begin
(let _52_754 = (let _123_659 = (norm_t env t)
in (encode_typ_pred' fuel_opt _123_659 env xx))
in (match (_52_754) with
| (guard_x_t, decls') -> begin
((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', Support.Microsoft.FStar.Util.Inr (x))
end))
end)))
end)
in (match (_52_760) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (Support.List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_52_766) with
| (vars, guards, env, decls, names) -> begin
((Support.List.rev vars), (Support.List.rev guards), env, decls, (Support.List.rev names))
end))))
and encode_typ_pred' = (fun ( fuel_opt ) ( t ) ( env ) ( e ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _52_774 = (encode_typ_term t env)
in (match (_52_774) with
| (t, decls) -> begin
(let _123_664 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_123_664, decls))
end))))
and encode_typ_term = (fun ( t ) ( env ) -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _123_667 = (lookup_typ_var env a)
in (_123_667, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _123_668 = (lookup_free_tvar env fv)
in (_123_668, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
(match (((env.encode_non_total_function_typ && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _52_792 = (encode_binders None binders env)
in (match (_52_792) with
| (vars, guards, env', decls, _52_791) -> begin
(let fsym = (let _123_669 = (varops.fresh "f")
in (_123_669, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _52_798 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_52_798) with
| (pre_opt, res_t) -> begin
(let _52_801 = (encode_typ_pred' None res_t env' app)
in (match (_52_801) with
| (res_pred, decls') -> begin
(let _52_810 = (match (pre_opt) with
| None -> begin
(let _123_670 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_123_670, decls))
end
| Some (pre) -> begin
(let _52_807 = (encode_formula pre env')
in (match (_52_807) with
| (guard, decls0) -> begin
(let _123_671 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_123_671, (Support.List.append decls decls0)))
end))
end)
in (match (_52_810) with
| (guards, guard_decls) -> begin
(let t_interp = (let _123_673 = (let _123_672 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _123_672))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_673))
in (let cvars = (let _123_675 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (Support.All.pipe_right _123_675 (Support.List.filter (fun ( _52_815 ) -> (match (_52_815) with
| (x, _52_814) -> begin
(x <> (Support.Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _52_821)) -> begin
(let _123_678 = (let _123_677 = (let _123_676 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _123_676))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_677))
in (_123_678, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _123_679 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_123_679))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _123_681 = (let _123_680 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _123_680))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_681))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _123_683 = (let _123_682 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_123_682, Some ((Support.String.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_123_683))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let pre_typing = (let _123_690 = (let _123_689 = (let _123_688 = (let _123_687 = (let _123_686 = (let _123_685 = (let _123_684 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _123_684))
in (f_has_t, _123_685))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_686))
in ((f_has_t)::[], (fsym)::cvars, _123_687))
in (mkForall_fuel _123_688))
in (_123_689, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_690))
in (let t_interp = (let _123_694 = (let _123_693 = (let _123_692 = (let _123_691 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t, t_interp))
in ((f_has_t)::[], (fsym)::cvars, _123_691))
in (mkForall_fuel _123_692))
in (_123_693, Some ((Support.String.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_123_694))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _52_836 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))))
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
in (let t_kinding = (let _123_696 = (let _123_695 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_123_695, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_696))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _123_703 = (let _123_702 = (let _123_701 = (let _123_700 = (let _123_699 = (let _123_698 = (let _123_697 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _123_697))
in (f_has_t, _123_698))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_699))
in ((f_has_t)::[], (fsym)::[], _123_700))
in (mkForall_fuel _123_701))
in (_123_702, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_703))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_847) -> begin
(let _52_866 = (match ((Microsoft_FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, f)); Microsoft_FStar_Absyn_Syntax.tk = _52_856; Microsoft_FStar_Absyn_Syntax.pos = _52_854; Microsoft_FStar_Absyn_Syntax.fvs = _52_852; Microsoft_FStar_Absyn_Syntax.uvs = _52_850} -> begin
(x, f)
end
| _52_863 -> begin
(Support.All.failwith "impossible")
end)
in (match (_52_866) with
| (x, f) -> begin
(let _52_869 = (encode_typ_term x.Microsoft_FStar_Absyn_Syntax.sort env)
in (match (_52_869) with
| (base_t, decls) -> begin
(let _52_873 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_873) with
| (x, xtm, env') -> begin
(let _52_876 = (encode_formula f env')
in (match (_52_876) with
| (refinement, decls') -> begin
(let encoding = (let _123_705 = (let _123_704 = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t)
in (_123_704, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _123_705))
in (let cvars = (let _123_707 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (Support.All.pipe_right _123_707 (Support.List.filter (fun ( _52_881 ) -> (match (_52_881) with
| (y, _52_880) -> begin
(y <> x)
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_887, _52_889)) -> begin
(let _123_710 = (let _123_709 = (let _123_708 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _123_708))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_709))
in (_123_710, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _123_712 = (let _123_711 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _123_711))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_712))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _123_714 = (let _123_713 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (xfv)::cvars, _123_713))
in (mkForall_fuel _123_714))
in (let t_decls = (let _123_721 = (let _123_720 = (let _123_719 = (let _123_718 = (let _123_717 = (let _123_716 = (let _123_715 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_123_715))
in (assumption, _123_716))
in Microsoft_FStar_ToSMT_Term.Assume (_123_717))
in (_123_718)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_123_719)
in (tdecl)::_123_720)
in (Support.List.append (Support.List.append decls decls') _123_721))
in (let _52_902 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _123_722 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _123_722))
in (let _52_911 = (encode_knd k env ttm)
in (match (_52_911) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let is_full_app = (fun ( _52_918 ) -> (match (()) with
| () -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind head)
in (let _52_923 = (Microsoft_FStar_Absyn_Util.kind_formals kk)
in (match (_52_923) with
| (formals, _52_922) -> begin
((Support.List.length formals) = (Support.List.length args))
end)))
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_typ head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _52_930 = (encode_args args env)
in (match (_52_930) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _52_936 = (encode_args args env)
in (match (_52_936) with
| (args, decls) -> begin
(match ((is_full_app ())) with
| true -> begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _123_727 = (let _123_726 = (Support.List.map (fun ( _52_10 ) -> (match (_52_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (head, _123_726))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_727))
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
(let ttm = (let _123_728 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _123_728))
in (let _52_952 = (encode_knd k env ttm)
in (match (_52_952) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _52_955 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, body)) -> begin
(let _52_967 = (encode_binders None bs env)
in (match (_52_967) with
| (vars, guards, env, decls, _52_966) -> begin
(let _52_970 = (encode_typ_term body env)
in (match (_52_970) with
| (body, decls') -> begin
(let key_body = (let _123_732 = (let _123_731 = (let _123_730 = (let _123_729 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_123_729, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_730))
in ([], vars, _123_731))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_732))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_976, _52_978)) -> begin
(let _123_735 = (let _123_734 = (let _123_733 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _123_733))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_734))
in (_123_735, []))
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
in (let t = (let _123_737 = (let _123_736 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _123_736))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_737))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _123_744 = (let _123_743 = (let _123_742 = (let _123_741 = (let _123_740 = (let _123_739 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _123_738 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_123_739, _123_738)))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_740))
in ((app)::[], (Support.List.append vars cvars), _123_741))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_742))
in (_123_743, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_744))
in (let kinding = (let _52_993 = (let _123_745 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _123_745 env t))
in (match (_52_993) with
| (ktm, decls'') -> begin
(let _123_749 = (let _123_748 = (let _123_747 = (let _123_746 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_123_746, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_747))
in (_123_748)::[])
in (Support.List.append decls'' _123_749))
end))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _52_996 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _52_1000)) -> begin
(encode_typ_term t env)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_52_1004) -> begin
(let _123_750 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _123_750 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _123_755 = (let _123_754 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _123_753 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _123_752 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _123_751 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _123_754 _123_753 _123_752 _123_751)))))
in (Support.All.failwith _123_755))
end)))
and encode_exp = (fun ( e ) ( env ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_52_1015) -> begin
(let _123_758 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _123_758 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _52_1022)) -> begin
(let _123_759 = (lookup_free_var env v)
in (_123_759, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _123_760 = (encode_const c)
in (_123_760, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _52_1030)) -> begin
(let _52_1033 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _52_1037))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _52_1043)) -> begin
(let e = (let _123_761 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _123_761))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun ( _52_1052 ) -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _123_764 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_123_764, (decl)::[]))))
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _52_1056 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _123_765 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (Support.All.pipe_left Support.Prims.op_Negation _123_765))) with
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
(let _52_1068 = (Support.Microsoft.FStar.Util.first_N nformals bs)
in (match (_52_1068) with
| (bs0, rest) -> begin
(let res_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s (Microsoft_FStar_Absyn_Util.comp_result c))
end
| _52_1072 -> begin
(Support.All.failwith "Impossible")
end)
in (let e = (let _123_767 = (let _123_766 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _123_766))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _123_767 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end
| false -> begin
(let _52_1081 = (encode_binders None bs env)
in (match (_52_1081) with
| (vars, guards, envbody, decls, _52_1080) -> begin
(let _52_1084 = (encode_exp body envbody)
in (match (_52_1084) with
| (body, decls') -> begin
(let key_body = (let _123_771 = (let _123_770 = (let _123_769 = (let _123_768 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_123_768, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_769))
in ([], vars, _123_770))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_771))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_1090, _52_1092)) -> begin
(let _123_774 = (let _123_773 = (let _123_772 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _123_772))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_773))
in (_123_774, []))
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
in (let f = (let _123_776 = (let _123_775 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _123_775))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_776))
in (let app = (mk_ApplyE f vars)
in (let _52_1106 = (encode_typ_pred' None tfun env f)
in (match (_52_1106) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _123_778 = (let _123_777 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_123_777, Some ((Support.String.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_123_778))
in (let interp_f = (let _123_785 = (let _123_784 = (let _123_783 = (let _123_782 = (let _123_781 = (let _123_780 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _123_779 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_123_780, _123_779)))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_781))
in ((app)::[], (Support.List.append vars cvars), _123_782))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_783))
in (_123_784, Some ((Support.String.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_123_785))
in (let f_decls = (Support.List.append (Support.List.append (Support.List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _52_1110 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end))
end
| _52_1113 -> begin
(Support.All.failwith "Impossible")
end))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((l, _52_1124)); Microsoft_FStar_Absyn_Syntax.tk = _52_1121; Microsoft_FStar_Absyn_Syntax.pos = _52_1119; Microsoft_FStar_Absyn_Syntax.fvs = _52_1117; Microsoft_FStar_Absyn_Syntax.uvs = _52_1115}, (Support.Microsoft.FStar.Util.Inl (_52_1139), _52_1142)::(Support.Microsoft.FStar.Util.Inr (v1), _52_1136)::(Support.Microsoft.FStar.Util.Inr (v2), _52_1131)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals l.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
(let _52_1149 = (encode_exp v1 env)
in (match (_52_1149) with
| (v1, decls1) -> begin
(let _52_1152 = (encode_exp v2 env)
in (match (_52_1152) with
| (v2, decls2) -> begin
(let _123_786 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_123_786, (Support.List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_52_1162); Microsoft_FStar_Absyn_Syntax.tk = _52_1160; Microsoft_FStar_Absyn_Syntax.pos = _52_1158; Microsoft_FStar_Absyn_Syntax.fvs = _52_1156; Microsoft_FStar_Absyn_Syntax.uvs = _52_1154}, _52_1166)) -> begin
(let _123_787 = (whnf_e env e)
in (encode_exp _123_787 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args_e)) -> begin
(let _52_1175 = (encode_args args_e env)
in (match (_52_1175) with
| (args, decls) -> begin
(let encode_partial_app = (fun ( ht_opt ) -> (let _52_1180 = (encode_exp head env)
in (match (_52_1180) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (Support.List.append decls decls'))
end
| Some ((formals, c)) -> begin
(let _52_1189 = (Support.Microsoft.FStar.Util.first_N (Support.List.length args_e) formals)
in (match (_52_1189) with
| (formals, rest) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _123_790 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _123_790 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _52_1194 = (encode_typ_pred' None ty env app_tm)
in (match (_52_1194) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _123_792 = (let _123_791 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_123_791, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_792))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun ( fv ) -> (let _52_1201 = (lookup_free_var_sym env fv)
in (match (_52_1201) with
| (fname, fuel_args) -> begin
(let tm = (let _123_798 = (let _123_797 = (let _123_796 = (Support.List.map (fun ( _52_11 ) -> (match (_52_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (Support.List.append fuel_args _123_796))
in (fname, _123_797))
in (Microsoft_FStar_ToSMT_Term.mkApp' _123_798))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _52_1208 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _123_800 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _123_799 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _123_800 _123_799)))
end
| false -> begin
()
end)
in (let head_type = (let _123_803 = (let _123_802 = (let _123_801 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _123_801))
in (whnf env _123_802))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.unrefine _123_803))
in (let _52_1211 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _123_806 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _123_805 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _123_804 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _123_806 _123_805 _123_804))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _123_810 = (let _123_809 = (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _123_808 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _123_807 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" _123_809 _123_808 _123_807))))
in (Support.All.failwith _123_810))
end
| Some ((formals, c)) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _52_1220)) when ((Support.List.length formals) = (Support.List.length args)) -> begin
(encode_full_app fv)
end
| _52_1224 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (_52_1233); Microsoft_FStar_Absyn_Syntax.lbtyp = _52_1231; Microsoft_FStar_Absyn_Syntax.lbeff = _52_1229; Microsoft_FStar_Absyn_Syntax.lbdef = _52_1227}::[]), _52_1239)) -> begin
(Support.All.failwith "Impossible: already handled by encoding of Sig_let")
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (x); Microsoft_FStar_Absyn_Syntax.lbtyp = t1; Microsoft_FStar_Absyn_Syntax.lbeff = _52_1245; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let _52_1257 = (encode_exp e1 env)
in (match (_52_1257) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _52_1261 = (encode_exp e2 env')
in (match (_52_1261) with
| (ee2, decls2) -> begin
(ee2, (Support.List.append decls1 decls2))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_52_1263) -> begin
(let _52_1265 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = Microsoft_FStar_ToSMT_Term.DeclFun ((e, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _123_811 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_123_811, (decl_e)::[])))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _52_1275 = (encode_exp e env)
in (match (_52_1275) with
| (scr, decls) -> begin
(let _52_1315 = (Support.List.fold_right (fun ( _52_1279 ) ( _52_1282 ) -> (match ((_52_1279, _52_1282)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (Support.List.fold_right (fun ( _52_1286 ) ( _52_1289 ) -> (match ((_52_1286, _52_1289)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (Support.All.pipe_right projections (Support.List.fold_left (fun ( env ) ( _52_1295 ) -> (match (_52_1295) with
| (x, t) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v t)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _52_1309 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _52_1306 = (encode_exp w env)
in (match (_52_1306) with
| (w, decls2) -> begin
(let _123_822 = (let _123_821 = (let _123_820 = (let _123_819 = (let _123_818 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _123_818))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_819))
in (guard, _123_820))
in (Microsoft_FStar_ToSMT_Term.mkAnd _123_821))
in (_123_822, decls2))
end))
end)
in (match (_52_1309) with
| (guard, decls2) -> begin
(let _52_1312 = (encode_exp br env)
in (match (_52_1312) with
| (br, decls3) -> begin
(let _123_823 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_123_823, (Support.List.append (Support.List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (Microsoft_FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_52_1315) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (_52_1317) -> begin
(let _123_826 = (let _123_825 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _123_824 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" _123_825 _123_824)))
in (Support.All.failwith _123_826))
end))))
and encode_pat = (fun ( env ) ( pat ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _52_1324 -> begin
(let _123_829 = (encode_one_pat env pat)
in (_123_829)::[])
end))
and encode_one_pat = (fun ( env ) ( pat ) -> (let _52_1327 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _123_832 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" _123_832))
end
| false -> begin
()
end)
in (let _52_1331 = (Microsoft_FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_52_1331) with
| (vars, pat_exp_or_typ) -> begin
(let _52_1352 = (Support.All.pipe_right vars (Support.List.fold_left (fun ( _52_1334 ) ( v ) -> (match (_52_1334) with
| (env, vars) -> begin
(match (v) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_1342 = (gen_typ_var env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_1342) with
| (aa, _52_1340, env) -> begin
(env, ((v, (aa, Microsoft_FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_1349 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_1349) with
| (xx, _52_1347, env) -> begin
(env, ((v, (xx, Microsoft_FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_52_1352) with
| (env, vars) -> begin
(let rec mk_guard = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_1357) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
Microsoft_FStar_ToSMT_Term.mkTrue
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _123_840 = (let _123_839 = (encode_const c)
in (scrutinee, _123_839))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_840))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _52_1381, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( _52_1390 ) -> (match (_52_1390) with
| (arg, _52_1389) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _123_843 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _123_843)))
end))))
in (Microsoft_FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_1397) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_var (x)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((Support.Microsoft.FStar.Util.Inr (x), scrutinee))::[]
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((Support.Microsoft.FStar.Util.Inl (a), scrutinee))::[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_52_1414) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _52_1418, args)) -> begin
(let _123_851 = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( _52_1426 ) -> (match (_52_1426) with
| (arg, _52_1425) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _123_850 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _123_850)))
end))))
in (Support.All.pipe_right _123_851 Support.List.flatten))
end))
in (let pat_term = (fun ( _52_1429 ) -> (match (()) with
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
and encode_args = (fun ( l ) ( env ) -> (let _52_1459 = (Support.All.pipe_right l (Support.List.fold_left (fun ( _52_1439 ) ( x ) -> (match (_52_1439) with
| (tms, decls) -> begin
(match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1444) -> begin
(let _52_1448 = (encode_typ_term t env)
in (match (_52_1448) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inl (t))::tms, (Support.List.append decls decls'))
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1452) -> begin
(let _52_1456 = (encode_exp e env)
in (match (_52_1456) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inr (t))::tms, (Support.List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_52_1459) with
| (l, decls) -> begin
((Support.List.rev l), decls)
end)))
and encode_formula = (fun ( phi ) ( env ) -> (let _52_1465 = (encode_formula_with_labels phi env)
in (match (_52_1465) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _52_1468 -> begin
(Support.All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun ( induction_on ) ( t ) ( env ) -> (let v_or_t_pat = (fun ( p ) -> (match ((let _123_865 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _123_865.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1475, (Support.Microsoft.FStar.Util.Inl (_52_1482), _52_1485)::(Support.Microsoft.FStar.Util.Inr (e), _52_1479)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1491, (Support.Microsoft.FStar.Util.Inl (t), _52_1495)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _52_1501 -> begin
(Support.All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun ( p ) -> (match ((let _123_868 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _123_868.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1505, _52_1517::(Support.Microsoft.FStar.Util.Inr (hd), _52_1514)::(Support.Microsoft.FStar.Util.Inr (tl), _52_1509)::[])) -> begin
(let _123_870 = (v_or_t_pat hd)
in (let _123_869 = (lemma_pats tl)
in (_123_870)::_123_869))
end
| _52_1522 -> begin
[]
end))
in (let _52_1561 = (match ((let _123_871 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _123_871.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _52_1531; Microsoft_FStar_Absyn_Syntax.pos = _52_1529; Microsoft_FStar_Absyn_Syntax.fvs = _52_1527; Microsoft_FStar_Absyn_Syntax.uvs = _52_1525})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _52_1550)::(Support.Microsoft.FStar.Util.Inl (post), _52_1545)::(Support.Microsoft.FStar.Util.Inr (pats), _52_1540)::[] -> begin
(let _123_872 = (lemma_pats pats)
in (binders, pre, post, _123_872))
end
| _52_1554 -> begin
(Support.All.failwith "impos")
end)
end
| _52_1556 -> begin
(Support.All.failwith "Impos")
end)
in (match (_52_1561) with
| (binders, pre, post, patterns) -> begin
(let _52_1568 = (encode_binders None binders env)
in (match (_52_1568) with
| (vars, guards, env, decls, _52_1567) -> begin
(let _52_1584 = (let _123_874 = (Support.All.pipe_right patterns (Support.List.map (fun ( _52_12 ) -> (match (_52_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1573) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1578) -> begin
(encode_exp e (let _52_1580 = env
in {bindings = _52_1580.bindings; depth = _52_1580.depth; tcenv = _52_1580.tcenv; warn = _52_1580.warn; cache = _52_1580.cache; nolabels = _52_1580.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1580.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _123_874 Support.List.unzip))
in (match (_52_1584) with
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
(let _123_876 = (let _123_875 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _123_875 e))
in (_123_876)::pats)
end
| _52_1592 -> begin
(let rec aux = (fun ( tl ) ( vars ) -> (match (vars) with
| [] -> begin
(let _123_881 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_123_881)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _123_883 = (let _123_882 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _123_882 tl))
in (aux _123_883 vars))
end
| _52_1603 -> begin
pats
end))
in (let _123_884 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _123_884 vars)))
end)
end)
in (let env = (let _52_1605 = env
in {bindings = _52_1605.bindings; depth = _52_1605.depth; tcenv = _52_1605.tcenv; warn = _52_1605.warn; cache = _52_1605.cache; nolabels = true; use_zfuel_name = _52_1605.use_zfuel_name; encode_non_total_function_typ = _52_1605.encode_non_total_function_typ})
in (let _52_1610 = (let _123_885 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _123_885 env))
in (match (_52_1610) with
| (pre, decls'') -> begin
(let _52_1613 = (let _123_886 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _123_886 env))
in (match (_52_1613) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in (let _123_891 = (let _123_890 = (let _123_889 = (let _123_888 = (let _123_887 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_123_887, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_888))
in (pats, vars, _123_889))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_890))
in (_123_891, decls)))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun ( phi ) ( env ) -> (let enc = (fun ( f ) -> (fun ( l ) -> (let _52_1634 = (Support.Microsoft.FStar.Util.fold_map (fun ( decls ) ( x ) -> (match ((Support.Prims.fst x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _52_1626 = (encode_typ_term t env)
in (match (_52_1626) with
| (t, decls') -> begin
((Support.List.append decls decls'), t)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _52_1631 = (encode_exp e env)
in (match (_52_1631) with
| (e, decls') -> begin
((Support.List.append decls decls'), e)
end))
end)) [] l)
in (match (_52_1634) with
| (decls, args) -> begin
(let _123_909 = (f args)
in (_123_909, [], decls))
end))))
in (let enc_prop_c = (fun ( f ) -> (fun ( l ) -> (let _52_1654 = (Support.List.fold_right (fun ( t ) ( _52_1642 ) -> (match (_52_1642) with
| (phis, labs, decls) -> begin
(match ((Support.Prims.fst t)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _52_1648 = (encode_formula_with_labels t env)
in (match (_52_1648) with
| (phi, labs', decls') -> begin
((phi)::phis, (Support.List.append labs' labs), (Support.List.append decls' decls))
end))
end
| _52_1650 -> begin
(Support.All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_52_1654) with
| (phis, labs, decls) -> begin
(let _123_925 = (f phis)
in (_123_925, labs, decls))
end))))
in (let const_op = (fun ( f ) ( _52_1657 ) -> (f, [], []))
in (let un_op = (fun ( f ) ( l ) -> (let _123_939 = (Support.List.hd l)
in (Support.All.pipe_left f _123_939)))
in (let bin_op = (fun ( f ) ( _52_13 ) -> (match (_52_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _52_1668 -> begin
(Support.All.failwith "Impossible")
end))
in (let eq_op = (fun ( _52_14 ) -> (match (_52_14) with
| _52_1676::_52_1674::e1::e2::[] -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun ( _52_15 ) -> (match (_52_15) with
| (Support.Microsoft.FStar.Util.Inl (lhs), _52_1689)::(Support.Microsoft.FStar.Util.Inl (rhs), _52_1684)::[] -> begin
(let _52_1695 = (encode_formula_with_labels rhs env)
in (match (_52_1695) with
| (l1, labs1, decls1) -> begin
(match (l1.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _52_1698)) -> begin
(l1, labs1, decls1)
end
| _52_1702 -> begin
(let _52_1706 = (encode_formula_with_labels lhs env)
in (match (_52_1706) with
| (l2, labs2, decls2) -> begin
(let _123_953 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_123_953, (Support.List.append labs1 labs2), (Support.List.append decls1 decls2)))
end))
end)
end))
end
| _52_1708 -> begin
(Support.All.failwith "impossible")
end))
in (let mk_ite = (fun ( _52_16 ) -> (match (_52_16) with
| (Support.Microsoft.FStar.Util.Inl (guard), _52_1724)::(Support.Microsoft.FStar.Util.Inl (_then), _52_1719)::(Support.Microsoft.FStar.Util.Inl (_else), _52_1714)::[] -> begin
(let _52_1730 = (encode_formula_with_labels guard env)
in (match (_52_1730) with
| (g, labs1, decls1) -> begin
(let _52_1734 = (encode_formula_with_labels _then env)
in (match (_52_1734) with
| (t, labs2, decls2) -> begin
(let _52_1738 = (encode_formula_with_labels _else env)
in (match (_52_1738) with
| (e, labs3, decls3) -> begin
(let res = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (Support.List.append (Support.List.append labs1 labs2) labs3), (Support.List.append (Support.List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _52_1741 -> begin
(Support.All.failwith "impossible")
end))
in (let unboxInt_l = (fun ( f ) ( l ) -> (let _123_965 = (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _123_965)))
in (let connectives = (let _123_1026 = (let _123_974 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _123_974))
in (let _123_1025 = (let _123_1024 = (let _123_980 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _123_980))
in (let _123_1023 = (let _123_1022 = (let _123_1021 = (let _123_989 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _123_989))
in (let _123_1020 = (let _123_1019 = (let _123_1018 = (let _123_998 = (Support.All.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _123_998))
in (let _123_1017 = (let _123_1016 = (let _123_1004 = (Support.All.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _123_1004))
in (_123_1016)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_123_1018)::_123_1017))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_123_1019)
in (_123_1021)::_123_1020))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_123_1022)
in (_123_1024)::_123_1023))
in (_123_1026)::_123_1025))
in (let fallback = (fun ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((phi', msg, r, b))) -> begin
(let _52_1759 = (encode_formula_with_labels phi' env)
in (match (_52_1759) with
| (phi, labs, decls) -> begin
(match (env.nolabels) with
| true -> begin
(phi, [], decls)
end
| false -> begin
(let lvar = (let _123_1029 = (varops.fresh "label")
in (_123_1029, Microsoft_FStar_ToSMT_Term.Bool_sort))
in (let lterm = (Microsoft_FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (Microsoft_FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ih); Microsoft_FStar_Absyn_Syntax.tk = _52_1770; Microsoft_FStar_Absyn_Syntax.pos = _52_1768; Microsoft_FStar_Absyn_Syntax.fvs = _52_1766; Microsoft_FStar_Absyn_Syntax.uvs = _52_1764}, _52_1785::(Support.Microsoft.FStar.Util.Inr (l), _52_1782)::(Support.Microsoft.FStar.Util.Inl (phi), _52_1777)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals ih.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.using_IH) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let _52_1791 = (encode_exp l env)
in (match (_52_1791) with
| (e, decls) -> begin
(let _52_1794 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_52_1794) with
| (f, decls') -> begin
(f, [], (Support.List.append decls decls'))
end))
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.mkTrue, [], [])
end)
end
| _52_1796 -> begin
(let _52_1799 = (encode_typ_term phi env)
in (match (_52_1799) with
| (tt, decls) -> begin
(let _123_1030 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_123_1030, [], decls))
end))
end))
in (let encode_q_body = (fun ( env ) ( bs ) ( ps ) ( body ) -> (let _52_1811 = (encode_binders None bs env)
in (match (_52_1811) with
| (vars, guards, env, decls, _52_1810) -> begin
(let _52_1827 = (let _123_1040 = (Support.All.pipe_right ps (Support.List.map (fun ( _52_17 ) -> (match (_52_17) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1816) -> begin
(encode_typ_term t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1821) -> begin
(encode_exp e (let _52_1823 = env
in {bindings = _52_1823.bindings; depth = _52_1823.depth; tcenv = _52_1823.tcenv; warn = _52_1823.warn; cache = _52_1823.cache; nolabels = _52_1823.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1823.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _123_1040 Support.List.unzip))
in (match (_52_1827) with
| (pats, decls') -> begin
(let _52_1831 = (encode_formula_with_labels body env)
in (match (_52_1831) with
| (body, labs, decls'') -> begin
(let _123_1041 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _123_1041, body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'')))
end))
end))
end)))
in (let _52_1832 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _123_1042 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" _123_1042))
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
(match ((Support.All.pipe_right connectives (Support.List.tryFind (fun ( _52_1844 ) -> (match (_52_1844) with
| (l, _52_1843) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some ((_52_1847, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, pats, body))) -> begin
(let _52_1857 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _123_1059 = (Support.All.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" _123_1059))
end
| false -> begin
()
end)
in (let _52_1865 = (encode_q_body env vars pats body)
in (match (_52_1865) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _123_1062 = (let _123_1061 = (let _123_1060 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _123_1060))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1061))
in (_123_1062, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _52_1878 = (encode_q_body env vars pats body)
in (match (_52_1878) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _123_1065 = (let _123_1064 = (let _123_1063 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _123_1063))
in (Microsoft_FStar_ToSMT_Term.mkExists _123_1064))
in (_123_1065, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : Microsoft_FStar_Absyn_Syntax.lident  ->  string  ->  Microsoft_FStar_ToSMT_Term.decl list; is : Microsoft_FStar_Absyn_Syntax.lident  ->  bool}

let is_Mkprims_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkprims_t"))

let prims = (let _52_1884 = (fresh_fvar "a" Microsoft_FStar_ToSMT_Term.Type_sort)
in (match (_52_1884) with
| (asym, a) -> begin
(let _52_1887 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_1887) with
| (xsym, x) -> begin
(let _52_1890 = (fresh_fvar "y" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_1890) with
| (ysym, y) -> begin
(let deffun = (fun ( vars ) ( body ) ( x ) -> (Microsoft_FStar_ToSMT_Term.DefineFun ((x, vars, Microsoft_FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun ( vars ) ( body ) -> (fun ( x ) -> (let t1 = (let _123_1108 = (let _123_1107 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _123_1107))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1108))
in (let vname_decl = (let _123_1110 = (let _123_1109 = (Support.All.pipe_right vars (Support.List.map Support.Prims.snd))
in (x, _123_1109, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_123_1110))
in (let _123_1116 = (let _123_1115 = (let _123_1114 = (let _123_1113 = (let _123_1112 = (let _123_1111 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _123_1111))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1112))
in (_123_1113, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1114))
in (_123_1115)::[])
in (vname_decl)::_123_1116)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _123_1276 = (let _123_1125 = (let _123_1124 = (let _123_1123 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1123))
in (quant axy _123_1124))
in (Microsoft_FStar_Absyn_Const.op_Eq, _123_1125))
in (let _123_1275 = (let _123_1274 = (let _123_1132 = (let _123_1131 = (let _123_1130 = (let _123_1129 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _123_1129))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1130))
in (quant axy _123_1131))
in (Microsoft_FStar_Absyn_Const.op_notEq, _123_1132))
in (let _123_1273 = (let _123_1272 = (let _123_1141 = (let _123_1140 = (let _123_1139 = (let _123_1138 = (let _123_1137 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1136 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1137, _123_1136)))
in (Microsoft_FStar_ToSMT_Term.mkLT _123_1138))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1139))
in (quant xy _123_1140))
in (Microsoft_FStar_Absyn_Const.op_LT, _123_1141))
in (let _123_1271 = (let _123_1270 = (let _123_1150 = (let _123_1149 = (let _123_1148 = (let _123_1147 = (let _123_1146 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1145 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1146, _123_1145)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _123_1147))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1148))
in (quant xy _123_1149))
in (Microsoft_FStar_Absyn_Const.op_LTE, _123_1150))
in (let _123_1269 = (let _123_1268 = (let _123_1159 = (let _123_1158 = (let _123_1157 = (let _123_1156 = (let _123_1155 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1154 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1155, _123_1154)))
in (Microsoft_FStar_ToSMT_Term.mkGT _123_1156))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1157))
in (quant xy _123_1158))
in (Microsoft_FStar_Absyn_Const.op_GT, _123_1159))
in (let _123_1267 = (let _123_1266 = (let _123_1168 = (let _123_1167 = (let _123_1166 = (let _123_1165 = (let _123_1164 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1163 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1164, _123_1163)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _123_1165))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1166))
in (quant xy _123_1167))
in (Microsoft_FStar_Absyn_Const.op_GTE, _123_1168))
in (let _123_1265 = (let _123_1264 = (let _123_1177 = (let _123_1176 = (let _123_1175 = (let _123_1174 = (let _123_1173 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1172 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1173, _123_1172)))
in (Microsoft_FStar_ToSMT_Term.mkSub _123_1174))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _123_1175))
in (quant xy _123_1176))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _123_1177))
in (let _123_1263 = (let _123_1262 = (let _123_1184 = (let _123_1183 = (let _123_1182 = (let _123_1181 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _123_1181))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _123_1182))
in (quant qx _123_1183))
in (Microsoft_FStar_Absyn_Const.op_Minus, _123_1184))
in (let _123_1261 = (let _123_1260 = (let _123_1193 = (let _123_1192 = (let _123_1191 = (let _123_1190 = (let _123_1189 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1188 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1189, _123_1188)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _123_1190))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _123_1191))
in (quant xy _123_1192))
in (Microsoft_FStar_Absyn_Const.op_Addition, _123_1193))
in (let _123_1259 = (let _123_1258 = (let _123_1202 = (let _123_1201 = (let _123_1200 = (let _123_1199 = (let _123_1198 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1197 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1198, _123_1197)))
in (Microsoft_FStar_ToSMT_Term.mkMul _123_1199))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _123_1200))
in (quant xy _123_1201))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _123_1202))
in (let _123_1257 = (let _123_1256 = (let _123_1211 = (let _123_1210 = (let _123_1209 = (let _123_1208 = (let _123_1207 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1206 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1207, _123_1206)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _123_1208))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _123_1209))
in (quant xy _123_1210))
in (Microsoft_FStar_Absyn_Const.op_Division, _123_1211))
in (let _123_1255 = (let _123_1254 = (let _123_1220 = (let _123_1219 = (let _123_1218 = (let _123_1217 = (let _123_1216 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1215 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_123_1216, _123_1215)))
in (Microsoft_FStar_ToSMT_Term.mkMod _123_1217))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _123_1218))
in (quant xy _123_1219))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _123_1220))
in (let _123_1253 = (let _123_1252 = (let _123_1229 = (let _123_1228 = (let _123_1227 = (let _123_1226 = (let _123_1225 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _123_1224 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_123_1225, _123_1224)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _123_1226))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1227))
in (quant xy _123_1228))
in (Microsoft_FStar_Absyn_Const.op_And, _123_1229))
in (let _123_1251 = (let _123_1250 = (let _123_1238 = (let _123_1237 = (let _123_1236 = (let _123_1235 = (let _123_1234 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _123_1233 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_123_1234, _123_1233)))
in (Microsoft_FStar_ToSMT_Term.mkOr _123_1235))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1236))
in (quant xy _123_1237))
in (Microsoft_FStar_Absyn_Const.op_Or, _123_1238))
in (let _123_1249 = (let _123_1248 = (let _123_1245 = (let _123_1244 = (let _123_1243 = (let _123_1242 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _123_1242))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_1243))
in (quant qx _123_1244))
in (Microsoft_FStar_Absyn_Const.op_Negation, _123_1245))
in (_123_1248)::[])
in (_123_1250)::_123_1249))
in (_123_1252)::_123_1251))
in (_123_1254)::_123_1253))
in (_123_1256)::_123_1255))
in (_123_1258)::_123_1257))
in (_123_1260)::_123_1259))
in (_123_1262)::_123_1261))
in (_123_1264)::_123_1263))
in (_123_1266)::_123_1265))
in (_123_1268)::_123_1267))
in (_123_1270)::_123_1269))
in (_123_1272)::_123_1271))
in (_123_1274)::_123_1273))
in (_123_1276)::_123_1275))
in (let mk = (fun ( l ) ( v ) -> (let _123_1308 = (Support.All.pipe_right prims (Support.List.filter (fun ( _52_1910 ) -> (match (_52_1910) with
| (l', _52_1909) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (Support.All.pipe_right _123_1308 (Support.List.collect (fun ( _52_1914 ) -> (match (_52_1914) with
| (_52_1912, b) -> begin
(b v)
end))))))
in (let is = (fun ( l ) -> (Support.All.pipe_right prims (Support.Microsoft.FStar.Util.for_some (fun ( _52_1920 ) -> (match (_52_1920) with
| (l', _52_1919) -> begin
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
in (let mk_unit = (fun ( _52_1926 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let _123_1340 = (let _123_1331 = (let _123_1330 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_123_1330, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1331))
in (let _123_1339 = (let _123_1338 = (let _123_1337 = (let _123_1336 = (let _123_1335 = (let _123_1334 = (let _123_1333 = (let _123_1332 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _123_1332))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1333))
in ((typing_pred)::[], (xx)::[], _123_1334))
in (mkForall_fuel _123_1335))
in (_123_1336, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1337))
in (_123_1338)::[])
in (_123_1340)::_123_1339))))
in (let mk_bool = (fun ( _52_1931 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _123_1360 = (let _123_1350 = (let _123_1349 = (let _123_1348 = (let _123_1347 = (let _123_1346 = (let _123_1345 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _123_1345))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1346))
in ((typing_pred)::[], (xx)::[], _123_1347))
in (mkForall_fuel _123_1348))
in (_123_1349, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1350))
in (let _123_1359 = (let _123_1358 = (let _123_1357 = (let _123_1356 = (let _123_1355 = (let _123_1354 = (let _123_1351 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_123_1351)::[])
in (let _123_1353 = (let _123_1352 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _123_1352 tt))
in (_123_1354, (bb)::[], _123_1353)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1355))
in (_123_1356, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1357))
in (_123_1358)::[])
in (_123_1360)::_123_1359))))))
in (let mk_int = (fun ( _52_1938 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _123_1372 = (let _123_1371 = (let _123_1370 = (let _123_1369 = (let _123_1368 = (let _123_1367 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _123_1366 = (let _123_1365 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_123_1365)::[])
in (_123_1367)::_123_1366))
in (tt)::_123_1368)
in (tt)::_123_1369)
in ("Prims.Precedes", _123_1370))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1371))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _123_1372))
in (let precedes_y_x = (let _123_1373 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _123_1373))
in (let _123_1414 = (let _123_1379 = (let _123_1378 = (let _123_1377 = (let _123_1376 = (let _123_1375 = (let _123_1374 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _123_1374))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1375))
in ((typing_pred)::[], (xx)::[], _123_1376))
in (mkForall_fuel _123_1377))
in (_123_1378, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1379))
in (let _123_1413 = (let _123_1412 = (let _123_1386 = (let _123_1385 = (let _123_1384 = (let _123_1383 = (let _123_1380 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_123_1380)::[])
in (let _123_1382 = (let _123_1381 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _123_1381 tt))
in (_123_1383, (bb)::[], _123_1382)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1384))
in (_123_1385, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1386))
in (let _123_1411 = (let _123_1410 = (let _123_1409 = (let _123_1408 = (let _123_1407 = (let _123_1406 = (let _123_1405 = (let _123_1404 = (let _123_1403 = (let _123_1402 = (let _123_1401 = (let _123_1400 = (let _123_1389 = (let _123_1388 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _123_1387 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_123_1388, _123_1387)))
in (Microsoft_FStar_ToSMT_Term.mkGT _123_1389))
in (let _123_1399 = (let _123_1398 = (let _123_1392 = (let _123_1391 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _123_1390 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_123_1391, _123_1390)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _123_1392))
in (let _123_1397 = (let _123_1396 = (let _123_1395 = (let _123_1394 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _123_1393 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_123_1394, _123_1393)))
in (Microsoft_FStar_ToSMT_Term.mkLT _123_1395))
in (_123_1396)::[])
in (_123_1398)::_123_1397))
in (_123_1400)::_123_1399))
in (typing_pred_y)::_123_1401)
in (typing_pred)::_123_1402)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _123_1403))
in (_123_1404, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1405))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _123_1406))
in (mkForall_fuel _123_1407))
in (_123_1408, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1409))
in (_123_1410)::[])
in (_123_1412)::_123_1411))
in (_123_1414)::_123_1413)))))))))))
in (let mk_int_alias = (fun ( _52_1950 ) ( tt ) -> (let _123_1423 = (let _123_1422 = (let _123_1421 = (let _123_1420 = (let _123_1419 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _123_1419))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_1420))
in (_123_1421, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1422))
in (_123_1423)::[]))
in (let mk_str = (fun ( _52_1954 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _123_1443 = (let _123_1433 = (let _123_1432 = (let _123_1431 = (let _123_1430 = (let _123_1429 = (let _123_1428 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _123_1428))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1429))
in ((typing_pred)::[], (xx)::[], _123_1430))
in (mkForall_fuel _123_1431))
in (_123_1432, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1433))
in (let _123_1442 = (let _123_1441 = (let _123_1440 = (let _123_1439 = (let _123_1438 = (let _123_1437 = (let _123_1434 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_123_1434)::[])
in (let _123_1436 = (let _123_1435 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _123_1435 tt))
in (_123_1437, (bb)::[], _123_1436)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1438))
in (_123_1439, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1440))
in (_123_1441)::[])
in (_123_1443)::_123_1442))))))
in (let mk_ref = (fun ( reft_name ) ( _52_1962 ) -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _123_1450 = (let _123_1449 = (let _123_1448 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_123_1448)::[])
in (reft_name, _123_1449))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1450))
in (let refb = (let _123_1453 = (let _123_1452 = (let _123_1451 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_123_1451)::[])
in (reft_name, _123_1452))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1453))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _123_1472 = (let _123_1459 = (let _123_1458 = (let _123_1457 = (let _123_1456 = (let _123_1455 = (let _123_1454 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _123_1454))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1455))
in ((typing_pred)::[], (xx)::(aa)::[], _123_1456))
in (mkForall_fuel _123_1457))
in (_123_1458, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1459))
in (let _123_1471 = (let _123_1470 = (let _123_1469 = (let _123_1468 = (let _123_1467 = (let _123_1466 = (let _123_1465 = (let _123_1464 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _123_1463 = (let _123_1462 = (let _123_1461 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _123_1460 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_123_1461, _123_1460)))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_1462))
in (_123_1464, _123_1463)))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1465))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _123_1466))
in (mkForall_fuel' 2 _123_1467))
in (_123_1468, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1469))
in (_123_1470)::[])
in (_123_1472)::_123_1471))))))))))
in (let mk_false_interp = (fun ( _52_1972 ) ( false_tm ) -> (let valid = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _123_1479 = (let _123_1478 = (let _123_1477 = (Microsoft_FStar_ToSMT_Term.mkIff (Microsoft_FStar_ToSMT_Term.mkFalse, valid))
in (_123_1477, Some ("False interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1478))
in (_123_1479)::[])))
in (let mk_and_interp = (fun ( conj ) ( _52_1978 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _123_1486 = (let _123_1485 = (let _123_1484 = (Microsoft_FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_123_1484)::[])
in ("Valid", _123_1485))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1486))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _123_1493 = (let _123_1492 = (let _123_1491 = (let _123_1490 = (let _123_1489 = (let _123_1488 = (let _123_1487 = (Microsoft_FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_123_1487, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1488))
in ((valid)::[], (aa)::(bb)::[], _123_1489))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1490))
in (_123_1491, Some ("/\\ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1492))
in (_123_1493)::[])))))))))
in (let mk_or_interp = (fun ( disj ) ( _52_1989 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _123_1500 = (let _123_1499 = (let _123_1498 = (Microsoft_FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_123_1498)::[])
in ("Valid", _123_1499))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1500))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _123_1507 = (let _123_1506 = (let _123_1505 = (let _123_1504 = (let _123_1503 = (let _123_1502 = (let _123_1501 = (Microsoft_FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_123_1501, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1502))
in ((valid)::[], (aa)::(bb)::[], _123_1503))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1504))
in (_123_1505, Some ("\\/ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1506))
in (_123_1507)::[])))))))))
in (let mk_eq2_interp = (fun ( eq2 ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _123_1514 = (let _123_1513 = (let _123_1512 = (Microsoft_FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_123_1512)::[])
in ("Valid", _123_1513))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1514))
in (let _123_1521 = (let _123_1520 = (let _123_1519 = (let _123_1518 = (let _123_1517 = (let _123_1516 = (let _123_1515 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (_123_1515, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1516))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _123_1517))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1518))
in (_123_1519, Some ("Eq2 interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1520))
in (_123_1521)::[])))))))))))
in (let mk_imp_interp = (fun ( imp ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _123_1528 = (let _123_1527 = (let _123_1526 = (Microsoft_FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_123_1526)::[])
in ("Valid", _123_1527))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1528))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _123_1535 = (let _123_1534 = (let _123_1533 = (let _123_1532 = (let _123_1531 = (let _123_1530 = (let _123_1529 = (Microsoft_FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_123_1529, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1530))
in ((valid)::[], (aa)::(bb)::[], _123_1531))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1532))
in (_123_1533, Some ("==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1534))
in (_123_1535)::[])))))))))
in (let mk_iff_interp = (fun ( iff ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _123_1542 = (let _123_1541 = (let _123_1540 = (Microsoft_FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_123_1540)::[])
in ("Valid", _123_1541))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1542))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _123_1549 = (let _123_1548 = (let _123_1547 = (let _123_1546 = (let _123_1545 = (let _123_1544 = (let _123_1543 = (Microsoft_FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_123_1543, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1544))
in ((valid)::[], (aa)::(bb)::[], _123_1545))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1546))
in (_123_1547, Some ("<==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1548))
in (_123_1549)::[])))))))))
in (let mk_forall_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _123_1556 = (let _123_1555 = (let _123_1554 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_123_1554)::[])
in ("Valid", _123_1555))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1556))
in (let valid_b_x = (let _123_1559 = (let _123_1558 = (let _123_1557 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_123_1557)::[])
in ("Valid", _123_1558))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1559))
in (let _123_1572 = (let _123_1571 = (let _123_1570 = (let _123_1569 = (let _123_1568 = (let _123_1567 = (let _123_1566 = (let _123_1565 = (let _123_1564 = (let _123_1560 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_123_1560)::[])
in (let _123_1563 = (let _123_1562 = (let _123_1561 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_123_1561, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1562))
in (_123_1564, (xx)::[], _123_1563)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1565))
in (_123_1566, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1567))
in ((valid)::[], (aa)::(bb)::[], _123_1568))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1569))
in (_123_1570, Some ("forall interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1571))
in (_123_1572)::[]))))))))))
in (let mk_exists_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _123_1579 = (let _123_1578 = (let _123_1577 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_123_1577)::[])
in ("Valid", _123_1578))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1579))
in (let valid_b_x = (let _123_1582 = (let _123_1581 = (let _123_1580 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_123_1580)::[])
in ("Valid", _123_1581))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1582))
in (let _123_1595 = (let _123_1594 = (let _123_1593 = (let _123_1592 = (let _123_1591 = (let _123_1590 = (let _123_1589 = (let _123_1588 = (let _123_1587 = (let _123_1583 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_123_1583)::[])
in (let _123_1586 = (let _123_1585 = (let _123_1584 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_123_1584, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1585))
in (_123_1587, (xx)::[], _123_1586)))
in (Microsoft_FStar_ToSMT_Term.mkExists _123_1588))
in (_123_1589, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1590))
in ((valid)::[], (aa)::(bb)::[], _123_1591))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1592))
in (_123_1593, Some ("exists interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1594))
in (_123_1595)::[]))))))))))
in (let mk_foralltyp_interp = (fun ( for_all ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _123_1602 = (let _123_1601 = (let _123_1600 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_123_1600)::[])
in ("Valid", _123_1601))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1602))
in (let valid_a_b = (let _123_1605 = (let _123_1604 = (let _123_1603 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_123_1603)::[])
in ("Valid", _123_1604))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1605))
in (let _123_1618 = (let _123_1617 = (let _123_1616 = (let _123_1615 = (let _123_1614 = (let _123_1613 = (let _123_1612 = (let _123_1611 = (let _123_1610 = (let _123_1606 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_123_1606)::[])
in (let _123_1609 = (let _123_1608 = (let _123_1607 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_123_1607, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1608))
in (_123_1610, (bb)::[], _123_1609)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1611))
in (_123_1612, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1613))
in ((valid)::[], (kk)::(aa)::[], _123_1614))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1615))
in (_123_1616, Some ("ForallTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1617))
in (_123_1618)::[]))))))))))
in (let mk_existstyp_interp = (fun ( for_some ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _123_1625 = (let _123_1624 = (let _123_1623 = (Microsoft_FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_123_1623)::[])
in ("Valid", _123_1624))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1625))
in (let valid_a_b = (let _123_1628 = (let _123_1627 = (let _123_1626 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_123_1626)::[])
in ("Valid", _123_1627))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1628))
in (let _123_1641 = (let _123_1640 = (let _123_1639 = (let _123_1638 = (let _123_1637 = (let _123_1636 = (let _123_1635 = (let _123_1634 = (let _123_1633 = (let _123_1629 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_123_1629)::[])
in (let _123_1632 = (let _123_1631 = (let _123_1630 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_123_1630, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1631))
in (_123_1633, (bb)::[], _123_1632)))
in (Microsoft_FStar_ToSMT_Term.mkExists _123_1634))
in (_123_1635, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _123_1636))
in ((valid)::[], (kk)::(aa)::[], _123_1637))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1638))
in (_123_1639, Some ("ExistsTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1640))
in (_123_1641)::[]))))))))))
in (let prims = ((Microsoft_FStar_Absyn_Const.unit_lid, mk_unit))::((Microsoft_FStar_Absyn_Const.bool_lid, mk_bool))::((Microsoft_FStar_Absyn_Const.int_lid, mk_int))::((Microsoft_FStar_Absyn_Const.string_lid, mk_str))::((Microsoft_FStar_Absyn_Const.ref_lid, mk_ref))::((Microsoft_FStar_Absyn_Const.char_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.uint8_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.false_lid, mk_false_interp))::((Microsoft_FStar_Absyn_Const.and_lid, mk_and_interp))::((Microsoft_FStar_Absyn_Const.or_lid, mk_or_interp))::((Microsoft_FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp_interp))::((Microsoft_FStar_Absyn_Const.iff_lid, mk_iff_interp))::((Microsoft_FStar_Absyn_Const.forall_lid, mk_forall_interp))::((Microsoft_FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun ( t ) ( s ) ( tt ) -> (match ((Support.Microsoft.FStar.Util.find_opt (fun ( _52_2082 ) -> (match (_52_2082) with
| (l, _52_2081) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some ((_52_2085, f)) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun ( env ) ( se ) -> (let _52_2091 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _123_1784 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") _123_1784))
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
in (let _52_2099 = (encode_sigelt' env se)
in (match (_52_2099) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _123_1787 = (let _123_1786 = (let _123_1785 = (Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_123_1785))
in (_123_1786)::[])
in (_123_1787, e))
end
| _52_2102 -> begin
(let _123_1794 = (let _123_1793 = (let _123_1789 = (let _123_1788 = (Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_123_1788))
in (_123_1789)::g)
in (let _123_1792 = (let _123_1791 = (let _123_1790 = (Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_123_1790))
in (_123_1791)::[])
in (Support.List.append _123_1793 _123_1792)))
in (_123_1794, e))
end)
end)))))
and encode_sigelt' = (fun ( env ) ( se ) -> (let should_skip = (fun ( l ) -> ((((Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.pure_") || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.ex_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.st_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.all_")))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_52_2108, _52_2110, _52_2112, _52_2114, Microsoft_FStar_Absyn_Syntax.Effect::[], _52_2118)) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _52_2123, _52_2125, _52_2127, _52_2129, _52_2131)) when (should_skip lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _52_2136, _52_2138, _52_2140, _52_2142, _52_2144)) when (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.b2t_lid) -> begin
(let _52_2150 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_52_2150) with
| (tname, ttok, env) -> begin
(let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _123_1799 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _123_1799))
in (let decls = (let _123_1807 = (let _123_1806 = (let _123_1805 = (let _123_1804 = (let _123_1803 = (let _123_1802 = (let _123_1801 = (let _123_1800 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _123_1800))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_1801))
in ((valid_b2t_x)::[], (xx)::[], _123_1802))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1803))
in (_123_1804, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1805))
in (_123_1806)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_123_1807)
in (decls, env)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _52_2158, t, tags, _52_2162)) -> begin
(let _52_2168 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_52_2168) with
| (tname, ttok, env) -> begin
(let _52_2177 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((tps', body)) -> begin
((Support.List.append tps tps'), body)
end
| _52_2174 -> begin
(tps, t)
end)
in (match (_52_2177) with
| (tps, t) -> begin
(let _52_2184 = (encode_binders None tps env)
in (match (_52_2184) with
| (vars, guards, env', binder_decls, _52_2183) -> begin
(let tok_app = (let _123_1808 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _123_1808 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _123_1810 = (let _123_1809 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _123_1809))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1810))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _52_2190 -> begin
(let _123_1812 = (let _123_1811 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _123_1811))
in (_123_1812)::[])
end)
in (let decls = (let _123_1823 = (let _123_1816 = (let _123_1815 = (let _123_1814 = (let _123_1813 = (Support.List.map Support.Prims.snd vars)
in (tname, _123_1813, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_123_1814))
in (_123_1815)::(tok_decl)::[])
in (Support.List.append _123_1816 fresh_tok))
in (let _123_1822 = (let _123_1821 = (let _123_1820 = (let _123_1819 = (let _123_1818 = (let _123_1817 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _123_1817))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1818))
in (_123_1819, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1820))
in (_123_1821)::[])
in (Support.List.append _123_1823 _123_1822)))
in (let t = (whnf env t)
in (let _52_2202 = (match ((Support.All.pipe_right tags (Support.Microsoft.FStar.Util.for_some (fun ( _52_18 ) -> (match (_52_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _52_2197 -> begin
false
end))))) with
| true -> begin
(let _123_1826 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _123_1825 = (encode_formula t env')
in (_123_1826, _123_1825)))
end
| false -> begin
(let _123_1827 = (encode_typ_term t env')
in (app, _123_1827))
end)
in (match (_52_2202) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _123_1834 = (let _123_1833 = (let _123_1832 = (let _123_1831 = (let _123_1830 = (let _123_1829 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _123_1828 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_123_1829, _123_1828)))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1830))
in ((def)::[], vars, _123_1831))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1832))
in (_123_1833, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1834))
in (let kindingAx = (let _52_2206 = (let _123_1835 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _123_1835 env' app))
in (match (_52_2206) with
| (k, decls) -> begin
(let _123_1843 = (let _123_1842 = (let _123_1841 = (let _123_1840 = (let _123_1839 = (let _123_1838 = (let _123_1837 = (let _123_1836 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_123_1836, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1837))
in ((app)::[], vars, _123_1838))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1839))
in (_123_1840, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1841))
in (_123_1842)::[])
in (Support.List.append decls _123_1843))
end))
in (let g = (let _123_1844 = (primitive_type_axioms lid tname app)
in (Support.List.append (Support.List.append (Support.List.append (Support.List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _123_1844))
in (g, env))))
end))))))))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _52_2213)) -> begin
(let tt = (whnf env t)
in (let _52_2219 = (encode_free_var env lid t tt quals)
in (match (_52_2219) with
| (decls, env) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_smt_lemma t) && ((Support.All.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption)) || env.tcenv.Microsoft_FStar_Tc_Env.is_iface))) with
| true -> begin
(let _123_1846 = (let _123_1845 = (encode_smt_lemma env lid t)
in (Support.List.append decls _123_1845))
in (_123_1846, env))
end
| false -> begin
(decls, env)
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((l, f, _52_2223, _52_2225)) -> begin
(let _52_2230 = (encode_formula f env)
in (match (_52_2230) with
| (f, decls) -> begin
(let g = (let _123_1851 = (let _123_1850 = (let _123_1849 = (let _123_1848 = (let _123_1847 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "Assumption: %s" _123_1847))
in Some (_123_1848))
in (f, _123_1849))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1850))
in (_123_1851)::[])
in ((Support.List.append decls g), env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _52_2236, datas, quals, _52_2240)) when (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.precedes_lid) -> begin
(let _52_2246 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2246) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, _52_2249, _52_2251, _52_2253, _52_2255, _52_2257, _52_2259)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.char_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.Microsoft_FStar_Absyn_Syntax.str
in (let tsym = (Microsoft_FStar_ToSMT_Term.mkFreeV (tname, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((tname, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let _123_1853 = (let _123_1852 = (primitive_type_axioms t tname tsym)
in (decl)::_123_1852)
in (_123_1853, (push_free_tvar env t tname (Some (tsym))))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _52_2269, datas, quals, _52_2273)) -> begin
(let is_logical = (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_19 ) -> (match (_52_19) with
| (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _52_2280 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun ( c ) -> (match (is_logical) with
| true -> begin
(let _52_2290 = c
in (match (_52_2290) with
| (name, args, _52_2287, _52_2289) -> begin
(let _123_1859 = (let _123_1858 = (let _123_1857 = (Support.All.pipe_right args (Support.List.map Support.Prims.snd))
in (name, _123_1857, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_123_1858))
in (_123_1859)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun ( tapp ) ( vars ) -> (match ((((Support.List.length datas) = 0) || (Support.All.pipe_right datas (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (let _123_1865 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (Support.All.pipe_right _123_1865 Support.Option.isNone))))))) with
| true -> begin
[]
end
| false -> begin
(let _52_2297 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_2297) with
| (xxsym, xx) -> begin
(let _52_2340 = (Support.All.pipe_right datas (Support.List.fold_left (fun ( _52_2300 ) ( l ) -> (match (_52_2300) with
| (out, decls) -> begin
(let data_t = (Microsoft_FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _52_2310 = (match ((Microsoft_FStar_Absyn_Util.function_formals data_t)) with
| Some ((formals, res)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_52_2310) with
| (args, res) -> begin
(let indices = (match ((let _123_1868 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _123_1868.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_52_2312, indices)) -> begin
indices
end
| _52_2317 -> begin
[]
end)
in (let env = (Support.All.pipe_right args (Support.List.fold_left (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _123_1873 = (let _123_1872 = (let _123_1871 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_123_1871, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1872))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _123_1873))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _123_1876 = (let _123_1875 = (let _123_1874 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_123_1874, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1875))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _123_1876))
end)) env))
in (let _52_2328 = (encode_args indices env)
in (match (_52_2328) with
| (indices, decls') -> begin
(let _52_2329 = (match (((Support.List.length indices) <> (Support.List.length vars))) with
| true -> begin
(Support.All.failwith "Impossible")
end
| false -> begin
()
end)
in (let eqs = (let _123_1883 = (Support.List.map2 (fun ( v ) ( a ) -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _123_1880 = (let _123_1879 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_123_1879, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_1880))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(let _123_1882 = (let _123_1881 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_123_1881, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_1882))
end)) vars indices)
in (Support.All.pipe_right _123_1883 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _123_1888 = (let _123_1887 = (let _123_1886 = (let _123_1885 = (let _123_1884 = (mk_data_tester env l xx)
in (_123_1884, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _123_1885))
in (out, _123_1886))
in (Microsoft_FStar_ToSMT_Term.mkOr _123_1887))
in (_123_1888, (Support.List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_52_2340) with
| (data_ax, decls) -> begin
(let _52_2343 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2343) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _123_1889 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _123_1889 xx tapp))
in (let _123_1896 = (let _123_1895 = (let _123_1894 = (let _123_1893 = (let _123_1892 = (let _123_1891 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _123_1890 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _123_1891, _123_1890)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1892))
in (_123_1893, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1894))
in (_123_1895)::[])
in (Support.List.append decls _123_1896)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _52_2355 = (match ((let _123_1897 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _123_1897.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, res)) -> begin
(true, bs, res)
end
| _52_2351 -> begin
(false, [], k)
end)
in (match (_52_2355) with
| (is_kind_arrow, formals, res) -> begin
(let _52_2362 = (encode_binders None formals env)
in (match (_52_2362) with
| (vars, guards, env', binder_decls, _52_2361) -> begin
(let projection_axioms = (fun ( tapp ) ( vars ) -> (match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.find_opt (fun ( _52_20 ) -> (match (_52_20) with
| Microsoft_FStar_Absyn_Syntax.Projector (_52_2368) -> begin
true
end
| _52_2371 -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inl (a)))) -> begin
(let rec projectee = (fun ( i ) ( _52_21 ) -> (match (_52_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (_52_2386) -> begin
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
in (let _52_2401 = (match ((Support.Microsoft.FStar.Util.first_N projectee_pos vars)) with
| (_52_2392, xx::suffix) -> begin
(xx, suffix)
end
| _52_2398 -> begin
(Support.All.failwith "impossible")
end)
in (match (_52_2401) with
| (xx, suffix) -> begin
(let dproj_app = (let _123_1911 = (let _123_1910 = (let _123_1909 = (mk_typ_projector_name d a)
in (let _123_1908 = (let _123_1907 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_123_1907)::[])
in (_123_1909, _123_1908)))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1910))
in (mk_ApplyT _123_1911 suffix))
in (let _123_1916 = (let _123_1915 = (let _123_1914 = (let _123_1913 = (let _123_1912 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _123_1912))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1913))
in (_123_1914, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1915))
in (_123_1916)::[]))
end))))
end
| _52_2404 -> begin
[]
end))
in (let pretype_axioms = (fun ( tapp ) ( vars ) -> (let _52_2410 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_2410) with
| (xxsym, xx) -> begin
(let _52_2413 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2413) with
| (ffsym, ff) -> begin
(let xx_has_type = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _123_1929 = (let _123_1928 = (let _123_1927 = (let _123_1926 = (let _123_1925 = (let _123_1924 = (let _123_1923 = (let _123_1922 = (let _123_1921 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _123_1921))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_1922))
in (xx_has_type, _123_1923))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1924))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _123_1925))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1926))
in (_123_1927, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1928))
in (_123_1929)::[]))
end))
end)))
in (let _52_2418 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2418) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _123_1931 = (let _123_1930 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _123_1930))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_1931))
in (let _52_2443 = (let tname_decl = (let _123_1935 = (let _123_1934 = (Support.All.pipe_right vars (Support.List.map (fun ( _52_2424 ) -> (match (_52_2424) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))))
in (let _123_1933 = (varops.next_id ())
in (tname, _123_1934, Microsoft_FStar_ToSMT_Term.Type_sort, _123_1933)))
in (constructor_or_logic_type_decl _123_1935))
in (let _52_2440 = (match (vars) with
| [] -> begin
(let _123_1939 = (let _123_1938 = (let _123_1937 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (Support.All.pipe_left (fun ( _123_1936 ) -> Some (_123_1936)) _123_1937))
in (push_free_tvar env t tname _123_1938))
in ([], _123_1939))
end
| _52_2428 -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _123_1940 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _123_1940))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match (((not (is_logical)) && (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_22 ) -> (match (_52_22) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _52_2435 -> begin
false
end)))))) with
| true -> begin
((ttok_app)::[])::((tapp)::[])::[]
end
| false -> begin
((ttok_app)::[])::[]
end)
in (let name_tok_corr = (let _123_1945 = (let _123_1944 = (let _123_1943 = (let _123_1942 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _123_1942))
in (Microsoft_FStar_ToSMT_Term.mkForall' _123_1943))
in (_123_1944, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1945))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_52_2440) with
| (tok_decls, env) -> begin
((Support.List.append tname_decl tok_decls), env)
end)))
in (match (_52_2443) with
| (decls, env) -> begin
(let kindingAx = (let _52_2446 = (encode_knd res env' tapp)
in (match (_52_2446) with
| (k, decls) -> begin
(let karr = (match (is_kind_arrow) with
| true -> begin
(let _123_1949 = (let _123_1948 = (let _123_1947 = (let _123_1946 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _123_1946))
in (_123_1947, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1948))
in (_123_1949)::[])
end
| false -> begin
[]
end)
in (let _123_1955 = (let _123_1954 = (let _123_1953 = (let _123_1952 = (let _123_1951 = (let _123_1950 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _123_1950))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1951))
in (_123_1952, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1953))
in (_123_1954)::[])
in (Support.List.append (Support.List.append decls karr) _123_1955)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _123_1956 = (projection_axioms tapp vars)
in (Support.List.append kindingAx _123_1956))
end
| false -> begin
(let _123_1963 = (let _123_1961 = (let _123_1959 = (let _123_1957 = (primitive_type_axioms t tname tapp)
in (Support.List.append kindingAx _123_1957))
in (let _123_1958 = (inversion_axioms tapp vars)
in (Support.List.append _123_1959 _123_1958)))
in (let _123_1960 = (projection_axioms tapp vars)
in (Support.List.append _123_1961 _123_1960)))
in (let _123_1962 = (pretype_axioms tapp vars)
in (Support.List.append _123_1963 _123_1962)))
end)
in (let g = (Support.List.append (Support.List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, _52_2453, _52_2455, _52_2457, _52_2459, _52_2461)) when (Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, t, _52_2467, quals, _52_2470, drange)) -> begin
(let _52_2477 = (new_term_constant_and_tok_from_lid env d)
in (match (_52_2477) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _52_2486 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(f, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_52_2486) with
| (formals, t_res) -> begin
(let _52_2489 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2489) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _52_2496 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_52_2496) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (Support.All.pipe_right names (Support.List.map (fun ( _52_23 ) -> (match (_52_23) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _123_1965 = (mk_typ_projector_name d a)
in (_123_1965, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _123_1966 = (mk_term_projector_name d x)
in (_123_1966, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _123_1968 = (let _123_1967 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _123_1967))
in (Support.All.pipe_right _123_1968 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _52_2510 = (encode_typ_pred' None t env ddtok_tm)
in (match (_52_2510) with
| (tok_typing, decls3) -> begin
(let _52_2517 = (encode_binders (Some (s_fuel_tm)) formals env)
in (match (_52_2517) with
| (vars', guards', env'', decls_formals, _52_2516) -> begin
(let _52_2522 = (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred' (Some (fuel_tm)) t_res env'' dapp)))
in (match (_52_2522) with
| (ty_pred', decls_pred) -> begin
(let guard' = (Microsoft_FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _52_2526 -> begin
(let _123_1970 = (let _123_1969 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _123_1969))
in (_123_1970)::[])
end)
in (let encode_elim = (fun ( _52_2529 ) -> (match (()) with
| () -> begin
(let _52_2532 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_52_2532) with
| (head, args) -> begin
(match ((let _123_1973 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _123_1973.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _52_2538 = (encode_args args env')
in (match (_52_2538) with
| (encoded_args, arg_decls) -> begin
(let _52_2562 = (Support.List.fold_left (fun ( _52_2542 ) ( arg ) -> (match (_52_2542) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _52_2550 = (let _123_1976 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _123_1976))
in (match (_52_2550) with
| (_52_2547, tv, env) -> begin
(let _123_1978 = (let _123_1977 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_123_1977)::eqns)
in (env, (tv)::arg_vars, _123_1978))
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _52_2557 = (let _123_1979 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _123_1979))
in (match (_52_2557) with
| (_52_2554, xv, env) -> begin
(let _123_1981 = (let _123_1980 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_123_1980)::eqns)
in (env, (xv)::arg_vars, _123_1981))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_52_2562) with
| (_52_2559, arg_vars, eqns) -> begin
(let arg_vars = (Support.List.rev arg_vars)
in (let ty = (Microsoft_FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (Support.List.map Microsoft_FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _123_1988 = (let _123_1987 = (let _123_1986 = (let _123_1985 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _123_1984 = (let _123_1983 = (let _123_1982 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards))
in (ty_pred, _123_1982))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1983))
in ((ty_pred)::[], _123_1985, _123_1984)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1986))
in (_123_1987, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1988))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _123_1989 = (varops.fresh "x")
in (_123_1989, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _123_1998 = (let _123_1997 = (let _123_1996 = (let _123_1995 = (let _123_1990 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_123_1990)::[])
in (let _123_1994 = (let _123_1993 = (let _123_1992 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _123_1991 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_123_1992, _123_1991)))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_1993))
in (_123_1995, (x)::[], _123_1994)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_1996))
in (_123_1997, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_1998))))
end
| false -> begin
(let prec = (Support.All.pipe_right vars (Support.List.collect (fun ( v ) -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _123_2001 = (let _123_2000 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _123_2000 dapp))
in (_123_2001)::[])
end
| _52_2577 -> begin
(Support.All.failwith "unexpected sort")
end))))
in (let _123_2008 = (let _123_2007 = (let _123_2006 = (let _123_2005 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _123_2004 = (let _123_2003 = (let _123_2002 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _123_2002))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_2003))
in ((ty_pred)::[], _123_2005, _123_2004)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2006))
in (_123_2007, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2008)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _52_2581 -> begin
(let _52_2582 = (let _123_2011 = (let _123_2010 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _123_2009 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" _123_2010 _123_2009)))
in (Microsoft_FStar_Tc_Errors.warn drange _123_2011))
in ([], []))
end)
end))
end))
in (let _52_2586 = (encode_elim ())
in (match (_52_2586) with
| (decls2, elim) -> begin
(let g = (let _123_2036 = (let _123_2035 = (let _123_2020 = (let _123_2019 = (let _123_2018 = (let _123_2017 = (let _123_2016 = (let _123_2015 = (let _123_2014 = (let _123_2013 = (let _123_2012 = (Microsoft_FStar_Absyn_Print.sli d)
in (Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" _123_2012))
in Some (_123_2013))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _123_2014))
in Microsoft_FStar_ToSMT_Term.DeclFun (_123_2015))
in (_123_2016)::[])
in (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) _123_2017))
in (Support.List.append _123_2018 proxy_fresh))
in (Support.List.append _123_2019 decls_formals))
in (Support.List.append _123_2020 decls_pred))
in (let _123_2034 = (let _123_2033 = (let _123_2032 = (let _123_2024 = (let _123_2023 = (let _123_2022 = (let _123_2021 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _123_2021))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2022))
in (_123_2023, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2024))
in (let _123_2031 = (let _123_2030 = (let _123_2029 = (let _123_2028 = (let _123_2027 = (let _123_2026 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _123_2025 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _123_2026, _123_2025)))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2027))
in (_123_2028, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2029))
in (_123_2030)::[])
in (_123_2032)::_123_2031))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_123_2033)
in (Support.List.append _123_2035 _123_2034)))
in (Support.List.append _123_2036 elim))
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
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _52_2590, _52_2592, _52_2594)) -> begin
(let _52_2599 = (encode_signature env ses)
in (match (_52_2599) with
| (g, env) -> begin
(let _52_2611 = (Support.All.pipe_right g (Support.List.partition (fun ( _52_24 ) -> (match (_52_24) with
| Microsoft_FStar_ToSMT_Term.Assume ((_52_2602, Some ("inversion axiom"))) -> begin
false
end
| _52_2608 -> begin
true
end))))
in (match (_52_2611) with
| (g', inversions) -> begin
(let _52_2620 = (Support.All.pipe_right g' (Support.List.partition (fun ( _52_25 ) -> (match (_52_25) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_52_2614) -> begin
true
end
| _52_2617 -> begin
false
end))))
in (match (_52_2620) with
| (decls, rest) -> begin
((Support.List.append (Support.List.append decls rest) inversions), env)
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((_52_2622, _52_2624, _52_2626, quals)) when (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_26 ) -> (match (_52_26) with
| (Microsoft_FStar_Absyn_Syntax.Projector (_)) | (Microsoft_FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _52_2638 -> begin
false
end)))) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((is_rec, bindings), _52_2643, _52_2645, quals)) -> begin
(let eta_expand = (fun ( binders ) ( formals ) ( body ) ( t ) -> (let nbinders = (Support.List.length binders)
in (let _52_2657 = (Support.Microsoft.FStar.Util.first_N nbinders formals)
in (match (_52_2657) with
| (formals, extra_formals) -> begin
(let subst = (Support.List.map2 (fun ( formal ) ( binder ) -> (match (((Support.Prims.fst formal), (Support.Prims.fst binder))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _123_2051 = (let _123_2050 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _123_2050))
in Support.Microsoft.FStar.Util.Inl (_123_2051))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _123_2053 = (let _123_2052 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _123_2052))
in Support.Microsoft.FStar.Util.Inr (_123_2053))
end
| _52_2671 -> begin
(Support.All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _123_2054 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (Support.All.pipe_right _123_2054 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _123_2060 = (let _123_2056 = (let _123_2055 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (Support.All.pipe_left Support.Prims.snd _123_2055))
in (body, _123_2056))
in (let _123_2059 = (let _123_2058 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (Support.All.pipe_left (fun ( _123_2057 ) -> Some (_123_2057)) _123_2058))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _123_2060 _123_2059 body.Microsoft_FStar_Absyn_Syntax.pos)))
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
(let _52_2709 = (Support.Microsoft.FStar.Util.first_N nformals binders)
in (match (_52_2709) with
| (bs0, rest) -> begin
(let tres = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tres)
end
| _52_2713 -> begin
(Support.All.failwith "impossible")
end)
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end
| false -> begin
(match ((nformals > nbinders)) with
| true -> begin
(let _52_2718 = (eta_expand binders formals body tres)
in (match (_52_2718) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end
| false -> begin
(binders, body, formals, tres)
end)
end))))
end
| _52_2720 -> begin
(let _123_2069 = (let _123_2068 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _123_2067 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _123_2068 _123_2067)))
in (Support.All.failwith _123_2069))
end)
end
| _52_2722 -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (let _52_2730 = (eta_expand [] formals e tres)
in (match (_52_2730) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _52_2732 -> begin
([], e, [], t_norm)
end)
end))
in (Support.All.try_with (fun ( _52_2734 ) -> (match (()) with
| () -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_27 ) -> (match (_52_27) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _52_2745 -> begin
false
end))))) with
| true -> begin
([], env)
end
| false -> begin
(match ((Support.All.pipe_right bindings (Support.Microsoft.FStar.Util.for_some (fun ( lb ) -> (Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp))))) with
| true -> begin
(let _123_2075 = (Support.All.pipe_right bindings (Support.List.collect (fun ( lb ) -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _123_2074 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _123_2074 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(raise (Let_rec_unencodeable))
end))))
in (_123_2075, env))
end
| false -> begin
(let _52_2765 = (Support.All.pipe_right bindings (Support.List.fold_left (fun ( _52_2752 ) ( lb ) -> (match (_52_2752) with
| (toks, typs, decls, env) -> begin
(let _52_2754 = (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(raise (Let_rec_unencodeable))
end
| false -> begin
()
end)
in (let t_norm = (let _123_2078 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.All.pipe_right _123_2078 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _52_2760 = (let _123_2079 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _123_2079 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_52_2760) with
| (tok, decl, env) -> begin
(let _123_2082 = (let _123_2081 = (let _123_2080 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_123_2080, tok))
in (_123_2081)::toks)
in (_123_2082, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_52_2765) with
| (toks, typs, decls, env) -> begin
(let toks = (Support.List.rev toks)
in (let decls = (Support.All.pipe_right (Support.List.rev decls) Support.List.flatten)
in (let typs = (Support.List.rev typs)
in (match (((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_28 ) -> (match (_52_28) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _52_2772 -> begin
false
end)))) || (Support.All.pipe_right typs (Support.Microsoft.FStar.Util.for_some (fun ( t ) -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (let _123_2085 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (Support.All.pipe_left Support.Prims.op_Negation _123_2085)))))))) with
| true -> begin
(decls, env)
end
| false -> begin
(match ((not (is_rec))) with
| true -> begin
(match ((bindings, typs, toks)) with
| ({Microsoft_FStar_Absyn_Syntax.lbname = _52_2780; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_2778; Microsoft_FStar_Absyn_Syntax.lbeff = _52_2776; Microsoft_FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _52_2796 = (destruct_bound_function flid t_norm e)
in (match (_52_2796) with
| (binders, body, formals, tres) -> begin
(let _52_2803 = (encode_binders None binders env)
in (match (_52_2803) with
| (vars, guards, env', binder_decls, _52_2802) -> begin
(let app = (match (vars) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _52_2806 -> begin
(let _123_2087 = (let _123_2086 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _123_2086))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_2087))
end)
in (let _52_2810 = (encode_exp body env')
in (match (_52_2810) with
| (body, decls2) -> begin
(let eqn = (let _123_2096 = (let _123_2095 = (let _123_2092 = (let _123_2091 = (let _123_2090 = (let _123_2089 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _123_2088 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_123_2089, _123_2088)))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_2090))
in ((app)::[], vars, _123_2091))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2092))
in (let _123_2094 = (let _123_2093 = (Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_123_2093))
in (_123_2095, _123_2094)))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2096))
in ((Support.List.append (Support.List.append (Support.List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _52_2813 -> begin
(Support.All.failwith "Impossible")
end)
end
| false -> begin
(let fuel = (let _123_2097 = (varops.fresh "fuel")
in (_123_2097, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _52_2830 = (Support.All.pipe_right toks (Support.List.fold_left (fun ( _52_2819 ) ( _52_2824 ) -> (match ((_52_2819, _52_2824)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _123_2102 = (let _123_2101 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (Support.All.pipe_left (fun ( _123_2100 ) -> Some (_123_2100)) _123_2101))
in (push_free_var env flid gtok _123_2102))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_52_2830) with
| (gtoks, env) -> begin
(let gtoks = (Support.List.rev gtoks)
in (let encode_one_binding = (fun ( env0 ) ( _52_2839 ) ( t_norm ) ( _52_2848 ) -> (match ((_52_2839, _52_2848)) with
| ((flid, f, ftok, g, gtok), {Microsoft_FStar_Absyn_Syntax.lbname = _52_2847; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_2845; Microsoft_FStar_Absyn_Syntax.lbeff = _52_2843; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _52_2853 = (destruct_bound_function flid t_norm e)
in (match (_52_2853) with
| (binders, body, formals, tres) -> begin
(let _52_2860 = (encode_binders None binders env)
in (match (_52_2860) with
| (vars, guards, env', binder_decls, _52_2859) -> begin
(let decl_g = (let _123_2113 = (let _123_2112 = (let _123_2111 = (Support.List.map Support.Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_123_2111)
in (g, _123_2112, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_123_2113))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _123_2116 = (let _123_2115 = (let _123_2114 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_123_2114)::vars_tm)
in (g, _123_2115))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_2116))
in (let gmax = (let _123_2119 = (let _123_2118 = (let _123_2117 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_123_2117)::vars_tm)
in (g, _123_2118))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_2119))
in (let _52_2870 = (encode_exp body env')
in (match (_52_2870) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _123_2128 = (let _123_2127 = (let _123_2124 = (let _123_2123 = (let _123_2122 = (let _123_2121 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _123_2120 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_123_2121, _123_2120)))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_2122))
in ((gsapp)::[], (fuel)::vars, _123_2123))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2124))
in (let _123_2126 = (let _123_2125 = (Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_123_2125))
in (_123_2127, _123_2126)))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2128))
in (let eqn_f = (let _123_2132 = (let _123_2131 = (let _123_2130 = (let _123_2129 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _123_2129))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2130))
in (_123_2131, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2132))
in (let eqn_g' = (let _123_2141 = (let _123_2140 = (let _123_2139 = (let _123_2138 = (let _123_2137 = (let _123_2136 = (let _123_2135 = (let _123_2134 = (let _123_2133 = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (_123_2133)::vars_tm)
in (g, _123_2134))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_2135))
in (gsapp, _123_2136))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_2137))
in ((gsapp)::[], (fuel)::vars, _123_2138))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2139))
in (_123_2140, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2141))
in (let _52_2893 = (let _52_2880 = (encode_binders None formals env0)
in (match (_52_2880) with
| (vars, v_guards, env, binder_decls, _52_2879) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _123_2142 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _123_2142 ((fuel)::vars)))
in (let _123_2146 = (let _123_2145 = (let _123_2144 = (let _123_2143 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _123_2143))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2144))
in (_123_2145, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2146)))
in (let _52_2890 = (let _52_2887 = (encode_typ_pred' None tres env gapp)
in (match (_52_2887) with
| (g_typing, d3) -> begin
(let _123_2154 = (let _123_2153 = (let _123_2152 = (let _123_2151 = (let _123_2150 = (let _123_2149 = (let _123_2148 = (let _123_2147 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_123_2147, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _123_2148))
in ((gapp)::[], (fuel)::vars, _123_2149))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2150))
in (_123_2151, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2152))
in (_123_2153)::[])
in (d3, _123_2154))
end))
in (match (_52_2890) with
| (aux_decls, typing_corr) -> begin
((Support.List.append binder_decls aux_decls), (Support.List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_52_2893) with
| (aux_decls, g_typing) -> begin
((Support.List.append (Support.List.append (Support.List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (Support.List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _52_2909 = (let _123_2157 = (Support.List.zip3 gtoks typs bindings)
in (Support.List.fold_left (fun ( _52_2897 ) ( _52_2901 ) -> (match ((_52_2897, _52_2901)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _52_2905 = (encode_one_binding env0 gtok ty bs)
in (match (_52_2905) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _123_2157))
in (match (_52_2909) with
| (decls, eqns, env0) -> begin
(let _52_2918 = (let _123_2159 = (Support.All.pipe_right decls Support.List.flatten)
in (Support.All.pipe_right _123_2159 (Support.List.partition (fun ( _52_29 ) -> (match (_52_29) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_52_2912) -> begin
true
end
| _52_2915 -> begin
false
end)))))
in (match (_52_2918) with
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
end)) (fun ( _52_2733 ) -> (match (_52_2733) with
| Let_rec_unencodeable -> begin
(let msg = (let _123_2162 = (Support.All.pipe_right bindings (Support.List.map (fun ( lb ) -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (Support.All.pipe_right _123_2162 (Support.String.concat " and ")))
in (let decl = Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun ( env ) ( x ) ( t ) ( t_norm ) -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _52_2945 = (encode_free_var env x t t_norm [])
in (match (_52_2945) with
| (decls, env) -> begin
(let _52_2950 = (lookup_lid env x)
in (match (_52_2950) with
| (n, x', _52_2949) -> begin
((n, x'), decls, env)
end))
end))
end
| Some ((n, x, _52_2954)) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun ( env ) ( lid ) ( t ) -> (let _52_2962 = (encode_function_type_as_formula None t env)
in (match (_52_2962) with
| (form, decls) -> begin
(Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume ((form, Some ((Support.String.strcat "Lemma: " lid.Microsoft_FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun ( env ) ( lid ) ( tt ) ( t_norm ) ( quals ) -> (match (((let _123_2175 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (Support.All.pipe_left Support.Prims.op_Negation _123_2175)) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm))) with
| true -> begin
(let _52_2971 = (new_term_constant_and_tok_from_lid env lid)
in (match (_52_2971) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _52_2974)) -> begin
(Support.All.pipe_right binders (Support.List.map (fun ( _52_30 ) -> (match (_52_30) with
| (Support.Microsoft.FStar.Util.Inl (_52_2979), _52_2982) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_2985 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
end
| _52_2987 -> begin
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
in (let _52_3004 = (match ((Microsoft_FStar_Absyn_Util.function_formals t_norm)) with
| Some ((args, comp)) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _123_2177 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _123_2177))
end
| false -> begin
(args, (None, (Microsoft_FStar_Absyn_Util.comp_result comp)))
end)
end
| None -> begin
([], (None, t_norm))
end)
in (match (_52_3004) with
| (formals, (pre_opt, res_t)) -> begin
(let _52_3008 = (new_term_constant_and_tok_from_lid env lid)
in (match (_52_3008) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _52_3011 -> begin
(Microsoft_FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun ( vapp ) ( vars ) -> (Support.All.pipe_right quals (Support.List.collect (fun ( _52_31 ) -> (match (_52_31) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _52_3025 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_52_3025) with
| (_52_3020, (xxsym, _52_3023)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _123_2190 = (let _123_2189 = (let _123_2188 = (let _123_2187 = (let _123_2186 = (let _123_2185 = (let _123_2184 = (let _123_2183 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _123_2183))
in (vapp, _123_2184))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_2185))
in ((vapp)::[], vars, _123_2186))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2187))
in (_123_2188, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2189))
in (_123_2190)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _52_3038 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_52_3038) with
| (_52_3033, (xxsym, _52_3036)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _123_2199 = (let _123_2198 = (let _123_2197 = (let _123_2196 = (let _123_2195 = (let _123_2194 = (let _123_2193 = (let _123_2192 = (let _123_2191 = (mk_term_projector_name d f)
in (_123_2191, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_2192))
in (vapp, _123_2193))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_2194))
in ((vapp)::[], vars, _123_2195))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2196))
in (_123_2197, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2198))
in (_123_2199)::[]))
end))
end
| _52_3041 -> begin
[]
end)))))
in (let _52_3048 = (encode_binders None formals env)
in (match (_52_3048) with
| (vars, guards, env', decls1, _52_3047) -> begin
(let _52_3057 = (match (pre_opt) with
| None -> begin
(let _123_2200 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_123_2200, decls1))
end
| Some (p) -> begin
(let _52_3054 = (encode_formula p env')
in (match (_52_3054) with
| (g, ds) -> begin
(let _123_2201 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_123_2201, (Support.List.append decls1 ds)))
end))
end)
in (match (_52_3057) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _123_2203 = (let _123_2202 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _123_2202))
in (Microsoft_FStar_ToSMT_Term.mkApp _123_2203))
in (let _52_3088 = (let vname_decl = (let _123_2206 = (let _123_2205 = (Support.All.pipe_right formals (Support.List.map (fun ( _52_32 ) -> (match (_52_32) with
| (Support.Microsoft.FStar.Util.Inl (_52_3062), _52_3065) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_3068 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _123_2205, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_123_2206))
in (let _52_3075 = (let env = (let _52_3070 = env
in {bindings = _52_3070.bindings; depth = _52_3070.depth; tcenv = _52_3070.tcenv; warn = _52_3070.warn; cache = _52_3070.cache; nolabels = _52_3070.nolabels; use_zfuel_name = _52_3070.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((not ((head_normal env tt)))) with
| true -> begin
(encode_typ_pred' None tt env vtok_tm)
end
| false -> begin
(encode_typ_pred' None t_norm env vtok_tm)
end))
in (match (_52_3075) with
| (tok_typing, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _52_3085 = (match (formals) with
| [] -> begin
(let _123_2210 = (let _123_2209 = (let _123_2208 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Support.All.pipe_left (fun ( _123_2207 ) -> Some (_123_2207)) _123_2208))
in (push_free_var env lid vname _123_2209))
in ((Support.List.append decls2 ((tok_typing)::[])), _123_2210))
end
| _52_3079 -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _123_2211 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _123_2211))
in (let name_tok_corr = (let _123_2215 = (let _123_2214 = (let _123_2213 = (let _123_2212 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _123_2212))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2213))
in (_123_2214, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2215))
in ((Support.List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_52_3085) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_52_3088) with
| (decls2, env) -> begin
(let _52_3091 = (encode_typ_pred' None res_t env' vapp)
in (match (_52_3091) with
| (ty_pred, decls3) -> begin
(let typingAx = (let _123_2219 = (let _123_2218 = (let _123_2217 = (let _123_2216 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _123_2216))
in (Microsoft_FStar_ToSMT_Term.mkForall _123_2217))
in (_123_2218, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2219))
in (let g = (let _123_2221 = (let _123_2220 = (mk_disc_proj_axioms vapp vars)
in (typingAx)::_123_2220)
in (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) _123_2221))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end)
end))
and encode_signature = (fun ( env ) ( ses ) -> (Support.All.pipe_right ses (Support.List.fold_left (fun ( _52_3098 ) ( se ) -> (match (_52_3098) with
| (g, env) -> begin
(let _52_3102 = (encode_sigelt env se)
in (match (_52_3102) with
| (g', env) -> begin
((Support.List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun ( env ) ( bindings ) -> (let encode_binding = (fun ( b ) ( _52_3109 ) -> (match (_52_3109) with
| (decls, env) -> begin
(match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t0)) -> begin
(let _52_3117 = (new_term_constant env x)
in (match (_52_3117) with
| (xxsym, xx, env') -> begin
(let t1 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.EtaArgs)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _52_3119 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _123_2236 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _123_2235 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _123_2234 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.fprint3 "Normalized %s : %s to %s\n" _123_2236 _123_2235 _123_2234))))
end
| false -> begin
()
end)
in (let _52_3123 = (encode_typ_pred' None t1 env xx)
in (match (_52_3123) with
| (t, decls') -> begin
(let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _123_2240 = (let _123_2239 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _123_2238 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _123_2237 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" _123_2239 _123_2238 _123_2237))))
in Some (_123_2240))
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
(let _52_3133 = (new_typ_constant env a)
in (match (_52_3133) with
| (aasym, aa, env') -> begin
(let _52_3136 = (encode_knd k env aa)
in (match (_52_3136) with
| (k, decls') -> begin
(let g = (let _123_2246 = (let _123_2245 = (let _123_2244 = (let _123_2243 = (let _123_2242 = (let _123_2241 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_123_2241))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _123_2242))
in Microsoft_FStar_ToSMT_Term.DeclFun (_123_2243))
in (_123_2244)::[])
in (Support.List.append _123_2245 decls'))
in (Support.List.append _123_2246 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((Support.List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((x, t)) -> begin
(let t_norm = (whnf env t)
in (let _52_3145 = (encode_free_var env x t t_norm [])
in (match (_52_3145) with
| (g, env') -> begin
((Support.List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _52_3150 = (encode_sigelt env se)
in (match (_52_3150) with
| (g, env') -> begin
((Support.List.append decls g), env')
end))
end)
end))
in (Support.List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun ( labs ) -> (let prefix = (Support.All.pipe_right labs (Support.List.map (fun ( _52_3157 ) -> (match (_52_3157) with
| (l, _52_3154, _52_3156) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Support.Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (Support.All.pipe_right labs (Support.List.collect (fun ( _52_3164 ) -> (match (_52_3164) with
| (l, _52_3161, _52_3163) -> begin
(let _123_2254 = (Support.All.pipe_left (fun ( _123_2250 ) -> Microsoft_FStar_ToSMT_Term.Echo (_123_2250)) (Support.Prims.fst l))
in (let _123_2253 = (let _123_2252 = (let _123_2251 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_123_2251))
in (_123_2252)::[])
in (_123_2254)::_123_2253))
end))))
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun ( tcenv ) -> (let _123_2259 = (let _123_2258 = (let _123_2257 = (Support.Microsoft.FStar.Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _123_2257; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_123_2258)::[])
in (Support.ST.op_Colon_Equals last_env _123_2259)))

let get_env = (fun ( tcenv ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "No env; call init first!")
end
| e::_52_3170 -> begin
(let _52_3173 = e
in {bindings = _52_3173.bindings; depth = _52_3173.depth; tcenv = tcenv; warn = _52_3173.warn; cache = _52_3173.cache; nolabels = _52_3173.nolabels; use_zfuel_name = _52_3173.use_zfuel_name; encode_non_total_function_typ = _52_3173.encode_non_total_function_typ})
end))

let set_env = (fun ( env ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Empty env stack")
end
| _52_3179::tl -> begin
(Support.ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun ( _52_3181 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Empty env stack")
end
| hd::tl -> begin
(let _52_3186 = (Microsoft_FStar_ToSMT_Term.push ())
in (let refs = (Support.Microsoft.FStar.Util.smap_copy hd.cache)
in (let top = (let _52_3189 = hd
in {bindings = _52_3189.bindings; depth = _52_3189.depth; tcenv = _52_3189.tcenv; warn = _52_3189.warn; cache = refs; nolabels = _52_3189.nolabels; use_zfuel_name = _52_3189.use_zfuel_name; encode_non_total_function_typ = _52_3189.encode_non_total_function_typ})
in (Support.ST.op_Colon_Equals last_env ((top)::(hd)::tl)))))
end)
end))

let pop_env = (fun ( _52_3192 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Popping an empty stack")
end
| _52_3196::tl -> begin
(let _52_3198 = (Microsoft_FStar_ToSMT_Term.pop ())
in (Support.ST.op_Colon_Equals last_env tl))
end)
end))

let mark_env = (fun ( _52_3200 ) -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun ( _52_3201 ) -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun ( _52_3202 ) -> (match (()) with
| () -> begin
(let _52_3203 = (Microsoft_FStar_ToSMT_Term.commit_mark ())
in (match ((Support.ST.read last_env)) with
| hd::_52_3207::tl -> begin
(Support.ST.op_Colon_Equals last_env ((hd)::tl))
end
| _52_3212 -> begin
(Support.All.failwith "Impossible")
end))
end))

let init = (fun ( tcenv ) -> (let _52_3214 = (init_env tcenv)
in (let _52_3216 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun ( msg ) -> (let _52_3219 = (push_env ())
in (let _52_3221 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun ( msg ) -> (let _52_3224 = (let _123_2280 = (pop_env ())
in (Support.All.pipe_left Support.Prims.ignore _123_2280))
in (let _52_3226 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun ( msg ) -> (let _52_3229 = (mark_env ())
in (let _52_3231 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun ( msg ) -> (let _52_3234 = (reset_mark_env ())
in (let _52_3236 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun ( msg ) -> (let _52_3239 = (commit_mark_env ())
in (let _52_3241 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun ( tcenv ) ( se ) -> (let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _123_2294 = (let _123_2293 = (let _123_2292 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.String.strcat "encoding sigelt " _123_2292))
in Microsoft_FStar_ToSMT_Term.Caption (_123_2293))
in (_123_2294)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _52_3250 = (encode_sigelt env se)
in (match (_52_3250) with
| (decls, env) -> begin
(let _52_3251 = (set_env env)
in (let _123_2295 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _123_2295)))
end)))))

let encode_modul = (fun ( tcenv ) ( modul ) -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _52_3256 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _123_2300 = (Support.All.pipe_right (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name _123_2300))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _52_3263 = (encode_signature (let _52_3259 = env
in {bindings = _52_3259.bindings; depth = _52_3259.depth; tcenv = _52_3259.tcenv; warn = false; cache = _52_3259.cache; nolabels = _52_3259.nolabels; use_zfuel_name = _52_3259.use_zfuel_name; encode_non_total_function_typ = _52_3259.encode_non_total_function_typ}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_52_3263) with
| (decls, env) -> begin
(let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let msg = (Support.String.strcat "Externals for " name)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _52_3269 = (set_env (let _52_3267 = env
in {bindings = _52_3267.bindings; depth = _52_3267.depth; tcenv = _52_3267.tcenv; warn = true; cache = _52_3267.cache; nolabels = _52_3267.nolabels; use_zfuel_name = _52_3267.use_zfuel_name; encode_non_total_function_typ = _52_3267.encode_non_total_function_typ}))
in (let _52_3271 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun ( tcenv ) ( q ) -> (let _52_3276 = (let _123_2309 = (let _123_2308 = (let _123_2307 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _123_2307))
in (Support.Microsoft.FStar.Util.format1 "Starting query at %s" _123_2308))
in (push _123_2309))
in (let pop = (fun ( _52_3279 ) -> (match (()) with
| () -> begin
(let _123_2314 = (let _123_2313 = (let _123_2312 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _123_2312))
in (Support.Microsoft.FStar.Util.format1 "Ending query at %s" _123_2313))
in (pop _123_2314))
end))
in (let _52_3309 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun ( bs ) ( b ) -> (b)::bs) [])
in (let _52_3292 = (let _123_2318 = (Support.List.filter (fun ( _52_33 ) -> (match (_52_33) with
| Microsoft_FStar_Tc_Env.Binding_sig (_52_3286) -> begin
false
end
| _52_3289 -> begin
true
end)) bindings)
in (encode_env_bindings env _123_2318))
in (match (_52_3292) with
| (env_decls, env) -> begin
(let _52_3293 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _123_2319 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" _123_2319))
end
| false -> begin
()
end)
in (let _52_3298 = (encode_formula_with_labels q env)
in (match (_52_3298) with
| (phi, labels, qdecls) -> begin
(let _52_3301 = (encode_labels labels)
in (match (_52_3301) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Support.List.append (Support.List.append env_decls label_prefix) qdecls)
in (let qry = (let _123_2321 = (let _123_2320 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_123_2320, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2321))
in (let suffix = (Support.List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_52_3309) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume (({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.False, _52_3316)); Microsoft_FStar_ToSMT_Term.hash = _52_3313; Microsoft_FStar_ToSMT_Term.freevars = _52_3311}, _52_3321)) -> begin
(let _52_3324 = (pop ())
in ())
end
| _52_3327 when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
(let _52_3328 = (pop ())
in ())
end
| Microsoft_FStar_ToSMT_Term.Assume ((q, _52_3332)) -> begin
(let fresh = ((Support.String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _52_3336 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun ( p ) ( _52_3342 ) -> (match (_52_3342) with
| (n, i) -> begin
(let _123_2343 = (let _123_2342 = (let _123_2327 = (let _123_2326 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" _123_2326))
in Microsoft_FStar_ToSMT_Term.Caption (_123_2327))
in (let _123_2341 = (let _123_2340 = (let _123_2332 = (let _123_2331 = (let _123_2330 = (let _123_2329 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _123_2328 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_123_2329, _123_2328)))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_2330))
in (_123_2331, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2332))
in (let _123_2339 = (let _123_2338 = (let _123_2337 = (let _123_2336 = (let _123_2335 = (let _123_2334 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _123_2333 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_123_2334, _123_2333)))
in (Microsoft_FStar_ToSMT_Term.mkEq _123_2335))
in (_123_2336, None))
in Microsoft_FStar_ToSMT_Term.Assume (_123_2337))
in (_123_2338)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_123_2340)::_123_2339))
in (_123_2342)::_123_2341))
in (Support.List.append _123_2343 suffix))
end))
in (let check = (fun ( p ) -> (let initial_config = (let _123_2347 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _123_2346 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_123_2347, _123_2346)))
in (let alt_configs = (let _123_2366 = (let _123_2365 = (match (((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel))) with
| true -> begin
(let _123_2350 = (let _123_2349 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _123_2348 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_123_2349, _123_2348)))
in (_123_2350)::[])
end
| false -> begin
[]
end)
in (let _123_2364 = (let _123_2363 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2) > (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _123_2353 = (let _123_2352 = ((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2)
in (let _123_2351 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_123_2352, _123_2351)))
in (_123_2353)::[])
end
| false -> begin
[]
end)
in (let _123_2362 = (let _123_2361 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) > (Support.ST.read Microsoft_FStar_Options.initial_fuel)) && ((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel)))) with
| true -> begin
(let _123_2356 = (let _123_2355 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _123_2354 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_123_2355, _123_2354)))
in (_123_2356)::[])
end
| false -> begin
[]
end)
in (let _123_2360 = (let _123_2359 = (match (((Support.ST.read Microsoft_FStar_Options.min_fuel) < (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _123_2358 = (let _123_2357 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (_123_2357, 1))
in (_123_2358)::[])
end
| false -> begin
[]
end)
in (_123_2359)::[])
in (_123_2361)::_123_2360))
in (_123_2363)::_123_2362))
in (_123_2365)::_123_2364))
in (Support.List.flatten _123_2366))
in (let report = (fun ( _52_3350 ) -> (match (_52_3350) with
| (ok, errs) -> begin
(match (ok) with
| true -> begin
()
end
| false -> begin
(let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", Microsoft_FStar_Absyn_Syntax.dummyRange))::[]
end
| _52_3353 -> begin
errs
end)
in (Microsoft_FStar_Tc_Errors.add_errors tcenv errs))
end)
end))
in (let rec try_alt_configs = (fun ( p ) ( errs ) ( _52_34 ) -> (match (_52_34) with
| [] -> begin
(report (false, errs))
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _123_2378 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _123_2378 (cb p [])))
end
| _52_3365 -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(let _123_2380 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _123_2380 (fun ( _52_3371 ) -> (match (_52_3371) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb p tl (ok, errs'))
end
| _52_3374 -> begin
(cb p tl (ok, errs))
end)
end))))
end))
and cb = (fun ( p ) ( alt ) ( _52_3379 ) -> (match (_52_3379) with
| (ok, errs) -> begin
(match (ok) with
| true -> begin
()
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _123_2384 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _123_2384 (cb p alt_configs))))))))
in (let process_query = (fun ( q ) -> (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let _52_3384 = (let _123_2390 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _123_2390 q))
in (match (_52_3384) with
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
in (let _52_3385 = (match ((Support.ST.read Microsoft_FStar_Options.admit_smt_queries)) with
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
in (let _52_3390 = (push "query")
in (let _52_3397 = (encode_formula_with_labels q env)
in (match (_52_3397) with
| (f, _52_3394, _52_3396) -> begin
(let _52_3398 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _52_3402)) -> begin
true
end
| _52_3406 -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = commit_mark; Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun ( _52_3407 ) -> ()); Microsoft_FStar_Tc_Env.push = (fun ( _52_3409 ) -> ()); Microsoft_FStar_Tc_Env.pop = (fun ( _52_3411 ) -> ()); Microsoft_FStar_Tc_Env.mark = (fun ( _52_3413 ) -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun ( _52_3415 ) -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun ( _52_3417 ) -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun ( _52_3419 ) ( _52_3421 ) -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun ( _52_3423 ) ( _52_3425 ) -> ()); Microsoft_FStar_Tc_Env.solve = (fun ( _52_3427 ) ( _52_3429 ) -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun ( _52_3431 ) ( _52_3433 ) -> false); Microsoft_FStar_Tc_Env.finish = (fun ( _52_3435 ) -> ()); Microsoft_FStar_Tc_Env.refresh = (fun ( _52_3436 ) -> ())}





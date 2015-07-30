
let add_fuel = (fun ( x ) ( tl ) -> (match ((Support.ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
tl
end
| false -> begin
(x)::tl
end))

let withenv = (fun ( c ) ( _50_39 ) -> (match (_50_39) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun ( args ) -> (Support.List.filter (fun ( _50_1 ) -> (match (_50_1) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
false
end
| _ -> begin
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

let mk_typ_projector_name = (fun ( lid ) ( a ) -> (let _65_21240 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.Prims.pipe_left escape _65_21240)))

let mk_term_projector_name = (fun ( lid ) ( a ) -> (let a = (let _65_21245 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _65_21245; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _65_21246 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.Prims.pipe_left escape _65_21246))))

let primitive_projector_by_pos = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _50_61 ) -> (match (()) with
| () -> begin
(let _65_21256 = (let _65_21255 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" _65_21255 lid.Microsoft_FStar_Absyn_Syntax.str))
in (failwith (_65_21256)))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _65_21257 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _65_21257.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _)) -> begin
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
| _ -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun ( lid ) ( i ) -> (let _65_21263 = (let _65_21262 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _65_21262))
in (Support.Prims.pipe_left escape _65_21263)))

let mk_typ_projector = (fun ( lid ) ( a ) -> (let _65_21269 = (let _65_21268 = (mk_typ_projector_name lid a)
in (_65_21268, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _65_21269)))

let mk_term_projector = (fun ( lid ) ( a ) -> (let _65_21275 = (let _65_21274 = (mk_term_projector_name lid a)
in (_65_21274, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _65_21275)))

let mk_term_projector_by_pos = (fun ( lid ) ( i ) -> (let _65_21281 = (let _65_21280 = (mk_term_projector_name_by_pos lid i)
in (_65_21280, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _65_21281)))

let mk_data_tester = (fun ( env ) ( l ) ( x ) -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let is_Mkvarops_t = (fun ( _ ) -> (failwith ("Not yet implemented")))

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun ( _50_100 ) -> (match (()) with
| () -> begin
(let _65_21385 = (Support.Microsoft.FStar.Util.smap_create 100)
in (let _65_21384 = (Support.Microsoft.FStar.Util.smap_create 100)
in (_65_21385, _65_21384)))
end))
in (let scopes = (let _65_21387 = (let _65_21386 = (new_scope ())
in (_65_21386)::[])
in (Support.Microsoft.FStar.Util.mk_ref _65_21387))
in (let mk_unique = (fun ( y ) -> (let y = (escape y)
in (let y = (match ((let _65_21391 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _65_21391 (fun ( _50_108 ) -> (match (_50_108) with
| (names, _) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_) -> begin
(let _50_113 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _65_21393 = (let _65_21392 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _65_21392))
in (Support.String.strcat (Support.String.strcat y "__") _65_21393)))
end)
in (let top_scope = (let _65_21395 = (let _65_21394 = (Support.ST.read scopes)
in (Support.List.hd _65_21394))
in (Support.Prims.pipe_left Support.Prims.fst _65_21395))
in (let _50_117 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun ( pp ) ( rn ) -> (let _65_21401 = (let _65_21400 = (Support.Prims.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.String.strcat _65_21400 "__"))
in (Support.String.strcat _65_21401 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun ( lid ) -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun ( _50_125 ) -> (match (()) with
| () -> begin
(let _50_126 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
end))
in (let fresh = (fun ( pfx ) -> (let _65_21409 = (let _65_21408 = (next_id ())
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int _65_21408))
in (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx _65_21409)))
in (let string_const = (fun ( s ) -> (match ((let _65_21413 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _65_21413 (fun ( _50_135 ) -> (match (_50_135) with
| (_, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _65_21414 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxString _65_21414))
in (let top_scope = (let _65_21416 = (let _65_21415 = (Support.ST.read scopes)
in (Support.List.hd _65_21415))
in (Support.Prims.pipe_left Support.Prims.snd _65_21416))
in (let _50_142 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun ( _50_145 ) -> (match (()) with
| () -> begin
(let _65_21421 = (let _65_21420 = (new_scope ())
in (let _65_21419 = (Support.ST.read scopes)
in (_65_21420)::_65_21419))
in (Support.ST.op_Colon_Equals scopes _65_21421))
end))
in (let pop = (fun ( _50_147 ) -> (match (()) with
| () -> begin
(let _65_21425 = (let _65_21424 = (Support.ST.read scopes)
in (Support.List.tl _65_21424))
in (Support.ST.op_Colon_Equals scopes _65_21425))
end))
in (let mark = (fun ( _50_149 ) -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun ( _50_151 ) -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun ( _50_153 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _50_166 = (Support.Microsoft.FStar.Util.smap_fold hd1 (fun ( key ) ( value ) ( v ) -> (Support.Microsoft.FStar.Util.smap_add next1 key value)) ())
in (let _50_171 = (Support.Microsoft.FStar.Util.smap_fold hd2 (fun ( key ) ( value ) ( v ) -> (Support.Microsoft.FStar.Util.smap_add next2 key value)) ())
in (Support.ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _ -> begin
(failwith ("Impossible"))
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun ( x ) -> (let _65_21441 = (let _65_21440 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _65_21439 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_65_21440, _65_21439)))
in (Microsoft_FStar_Absyn_Util.mkbvd _65_21441)))

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

let binder_of_eithervar = (fun ( v ) -> (v, None))

type env_t =
{bindings : binding list; depth : int; tcenv : Microsoft_FStar_Tc_Env.env; warn : bool; cache : (string * Microsoft_FStar_ToSMT_Term.sort list * Microsoft_FStar_ToSMT_Term.decl list) Support.Microsoft.FStar.Util.smap; nolabels : bool; use_zfuel_name : bool; encode_non_total_function_typ : bool}

let is_Mkenv_t = (fun ( _ ) -> (failwith ("Not yet implemented")))

let print_env = (fun ( e ) -> (let _65_21499 = (Support.Prims.pipe_right e.bindings (Support.List.map (fun ( _50_2 ) -> (match (_50_2) with
| Binding_var ((x, t)) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Binding_tvar ((a, t)) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Binding_fvar ((l, s, t, _)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| Binding_ftvar ((l, s, t)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end))))
in (Support.Prims.pipe_right _65_21499 (Support.String.concat ", "))))

let lookup_binding = (fun ( env ) ( f ) -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun ( env ) ( t ) -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _65_21509 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_65_21509))
end
| false -> begin
None
end))

let fresh_fvar = (fun ( x ) ( s ) -> (let xsym = (varops.fresh x)
in (let _65_21514 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _65_21514))))

let gen_term_var = (fun ( env ) ( x ) -> (let ysym = (let _65_21519 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@x" _65_21519))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _50_228 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _50_228.tcenv; warn = _50_228.warn; cache = _50_228.cache; nolabels = _50_228.nolabels; use_zfuel_name = _50_228.use_zfuel_name; encode_non_total_function_typ = _50_228.encode_non_total_function_typ})))))

let new_term_constant = (fun ( env ) ( x ) -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _50_234 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _50_234.depth; tcenv = _50_234.tcenv; warn = _50_234.warn; cache = _50_234.cache; nolabels = _50_234.nolabels; use_zfuel_name = _50_234.use_zfuel_name; encode_non_total_function_typ = _50_234.encode_non_total_function_typ})))))

let push_term_var = (fun ( env ) ( x ) ( t ) -> (let _50_239 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _50_239.depth; tcenv = _50_239.tcenv; warn = _50_239.warn; cache = _50_239.cache; nolabels = _50_239.nolabels; use_zfuel_name = _50_239.use_zfuel_name; encode_non_total_function_typ = _50_239.encode_non_total_function_typ}))

let lookup_term_var = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _50_3 ) -> (match (_50_3) with
| Binding_var ((b, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _ -> begin
None
end)))) with
| None -> begin
(let _65_21534 = (let _65_21533 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" _65_21533))
in (failwith (_65_21534)))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun ( env ) ( x ) -> (let ysym = (let _65_21539 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@a" _65_21539))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _50_259 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _50_259.tcenv; warn = _50_259.warn; cache = _50_259.cache; nolabels = _50_259.nolabels; use_zfuel_name = _50_259.use_zfuel_name; encode_non_total_function_typ = _50_259.encode_non_total_function_typ})))))

let new_typ_constant = (fun ( env ) ( x ) -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _50_265 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _50_265.depth; tcenv = _50_265.tcenv; warn = _50_265.warn; cache = _50_265.cache; nolabels = _50_265.nolabels; use_zfuel_name = _50_265.use_zfuel_name; encode_non_total_function_typ = _50_265.encode_non_total_function_typ})))))

let push_typ_var = (fun ( env ) ( x ) ( t ) -> (let _50_270 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _50_270.depth; tcenv = _50_270.tcenv; warn = _50_270.warn; cache = _50_270.cache; nolabels = _50_270.nolabels; use_zfuel_name = _50_270.use_zfuel_name; encode_non_total_function_typ = _50_270.encode_non_total_function_typ}))

let lookup_typ_var = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _50_4 ) -> (match (_50_4) with
| Binding_tvar ((b, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _ -> begin
None
end)))) with
| None -> begin
(let _65_21554 = (let _65_21553 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" _65_21553))
in (failwith (_65_21554)))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _65_21565 = (let _50_290 = env
in (let _65_21564 = (let _65_21563 = (let _65_21562 = (let _65_21561 = (let _65_21560 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.Prims.pipe_left (fun ( _65_21559 ) -> Some (_65_21559)) _65_21560))
in (x, fname, _65_21561, None))
in Binding_fvar (_65_21562))
in (_65_21563)::env.bindings)
in {bindings = _65_21564; depth = _50_290.depth; tcenv = _50_290.tcenv; warn = _50_290.warn; cache = _50_290.cache; nolabels = _50_290.nolabels; use_zfuel_name = _50_290.use_zfuel_name; encode_non_total_function_typ = _50_290.encode_non_total_function_typ}))
in (fname, ftok, _65_21565)))))

let try_lookup_lid = (fun ( env ) ( a ) -> (lookup_binding env (fun ( _50_5 ) -> (match (_50_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _ -> begin
None
end))))

let lookup_lid = (fun ( env ) ( a ) -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _65_21576 = (let _65_21575 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _65_21575))
in (failwith (_65_21576)))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _50_312 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _50_312.depth; tcenv = _50_312.tcenv; warn = _50_312.warn; cache = _50_312.cache; nolabels = _50_312.nolabels; use_zfuel_name = _50_312.use_zfuel_name; encode_non_total_function_typ = _50_312.encode_non_total_function_typ}))

let push_zfuel_name = (fun ( env ) ( x ) ( f ) -> (let _50_321 = (lookup_lid env x)
in (match (_50_321) with
| (t1, t2, _) -> begin
(let t3 = (let _65_21593 = (let _65_21592 = (let _65_21591 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_65_21591)::[])
in (f, _65_21592))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21593))
in (let _50_323 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _50_323.depth; tcenv = _50_323.tcenv; warn = _50_323.warn; cache = _50_323.cache; nolabels = _50_323.nolabels; use_zfuel_name = _50_323.use_zfuel_name; encode_non_total_function_typ = _50_323.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun ( env ) ( a ) -> (let _50_330 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_330) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _ -> begin
(match (sym) with
| Some (t) -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((_, fuel::[])) -> begin
(match ((let _65_21597 = (let _65_21596 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (Support.Prims.pipe_right _65_21596 Support.Prims.fst))
in (Support.Microsoft.FStar.Util.starts_with _65_21597 "fuel"))) with
| true -> begin
(let _65_21598 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _65_21598 fuel))
end
| false -> begin
t
end)
end
| _ -> begin
t
end)
end
| _ -> begin
(let _65_21600 = (let _65_21599 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _65_21599))
in (failwith (_65_21600)))
end)
end)
end)))

let lookup_free_var_name = (fun ( env ) ( a ) -> (let _50_354 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_354) with
| (x, _, _) -> begin
x
end)))

let lookup_free_var_sym = (fun ( env ) ( a ) -> (let _50_360 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_360) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((g, zf)); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}) when env.use_zfuel_name -> begin
(g, zf)
end
| _ -> begin
(match (sym) with
| None -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((g, fuel::[])) -> begin
(g, (fuel)::[])
end
| _ -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _65_21615 = (let _50_387 = env
in (let _65_21614 = (let _65_21613 = (let _65_21612 = (let _65_21611 = (let _65_21610 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.Prims.pipe_left (fun ( _65_21609 ) -> Some (_65_21609)) _65_21610))
in (x, fname, _65_21611))
in Binding_ftvar (_65_21612))
in (_65_21613)::env.bindings)
in {bindings = _65_21614; depth = _50_387.depth; tcenv = _50_387.tcenv; warn = _50_387.warn; cache = _50_387.cache; nolabels = _50_387.nolabels; use_zfuel_name = _50_387.use_zfuel_name; encode_non_total_function_typ = _50_387.encode_non_total_function_typ}))
in (fname, ftok, _65_21615)))))

let lookup_tlid = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _50_6 ) -> (match (_50_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _ -> begin
None
end)))) with
| None -> begin
(let _65_21622 = (let _65_21621 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _65_21621))
in (failwith (_65_21622)))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _50_406 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _50_406.depth; tcenv = _50_406.tcenv; warn = _50_406.warn; cache = _50_406.cache; nolabels = _50_406.nolabels; use_zfuel_name = _50_406.use_zfuel_name; encode_non_total_function_typ = _50_406.encode_non_total_function_typ}))

let lookup_free_tvar = (fun ( env ) ( a ) -> (match ((let _65_21633 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _65_21633 Support.Prims.snd))) with
| None -> begin
(let _65_21635 = (let _65_21634 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _65_21634))
in (failwith (_65_21635)))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun ( env ) ( a ) -> (let _65_21638 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _65_21638 Support.Prims.fst)))

let tok_of_name = (fun ( env ) ( nm ) -> (Support.Microsoft.FStar.Util.find_map env.bindings (fun ( _50_7 ) -> (match (_50_7) with
| (Binding_fvar ((_, nm', tok, _))) | (Binding_ftvar ((_, nm', tok))) when (nm = nm') -> begin
tok
end
| _ -> begin
None
end))))

let mkForall_fuel' = (fun ( n ) ( _50_436 ) -> (match (_50_436) with
| (pats, vars, body) -> begin
(let fallback = (fun ( _50_438 ) -> (match (()) with
| () -> begin
(Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in (match ((Support.ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
(fallback ())
end
| false -> begin
(let _50_441 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_50_441) with
| (fsym, fterm) -> begin
(let pats = (Support.Prims.pipe_right pats (Support.List.map (fun ( p ) -> (match (p.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var ("HasType"), args)) -> begin
(Microsoft_FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _ -> begin
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
(let _65_21654 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _65_21654 Support.Option.isNone))
end
| _ -> begin
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

let trivial_post = (fun ( t ) -> (let _65_21676 = (let _65_21675 = (let _65_21673 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_65_21673)::[])
in (let _65_21674 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_65_21675, _65_21674)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _65_21676 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun ( e ) ( vars ) -> (Support.Prims.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _65_21683 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _65_21683))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _65_21684 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _65_21684))
end
| _ -> begin
(let _65_21685 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _65_21685))
end)) e)))

let mk_ApplyE_args = (fun ( e ) ( args ) -> (Support.Prims.pipe_right args (Support.List.fold_left (fun ( out ) ( arg ) -> (match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyET out t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))

let mk_ApplyT = (fun ( t ) ( vars ) -> (Support.Prims.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _65_21698 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _65_21698))
end
| _ -> begin
(let _65_21699 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _65_21699))
end)) t)))

let mk_ApplyT_args = (fun ( t ) ( args ) -> (Support.Prims.pipe_right args (Support.List.fold_left (fun ( out ) ( arg ) -> (match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTT out t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))

let is_app = (fun ( _50_8 ) -> (match (_50_8) with
| (Microsoft_FStar_ToSMT_Term.Var ("ApplyTT")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyTE")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyET")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _ -> begin
false
end))

let is_eta = (fun ( env ) ( vars ) ( t ) -> (let rec aux = (fun ( t ) ( xs ) -> (match ((t.Microsoft_FStar_ToSMT_Term.tm, xs)) with
| (Microsoft_FStar_ToSMT_Term.App ((app, f::{Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.FreeV (y); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}::[])), x::xs) when ((is_app app) && (Microsoft_FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var (f), args)), _) -> begin
(match ((((Support.List.length args) = (Support.List.length vars)) && (Support.List.forall2 (fun ( a ) ( v ) -> (match (a.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (fv) -> begin
(Microsoft_FStar_ToSMT_Term.fv_eq fv v)
end
| _ -> begin
false
end)) args vars))) with
| true -> begin
(tok_of_name env f)
end
| false -> begin
None
end)
end
| (_, []) -> begin
(let fvs = (Microsoft_FStar_ToSMT_Term.free_variables t)
in (match ((Support.Prims.pipe_right fvs (Support.List.for_all (fun ( fv ) -> (not ((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_ToSMT_Term.fv_eq fv) vars))))))) with
| true -> begin
Some (t)
end
| false -> begin
None
end))
end
| _ -> begin
None
end))
in (aux t (Support.List.rev vars))))

type label =
(Microsoft_FStar_ToSMT_Term.fv * string * Support.Microsoft.FStar.Range.range)

type labels =
label list

type pattern =
{pat_vars : (Microsoft_FStar_Absyn_Syntax.either_var * Microsoft_FStar_ToSMT_Term.fv) list; pat_term : unit  ->  (Microsoft_FStar_ToSMT_Term.term * Microsoft_FStar_ToSMT_Term.decls_t); guard : Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term; projections : Microsoft_FStar_ToSMT_Term.term  ->  (Microsoft_FStar_Absyn_Syntax.either_var * Microsoft_FStar_ToSMT_Term.term) list}

let is_Mkpattern = (fun ( _ ) -> (failwith ("Not yet implemented")))

exception Let_rec_unencodeable

let is_Let_rec_unencodeable = (fun ( _discr_ ) -> (match (_discr_) with
| Let_rec_unencodeable -> begin
true
end
| _ -> begin
false
end))

let encode_const = (fun ( _50_9 ) -> (match (_50_9) with
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
(let _65_21755 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _65_21755))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _65_21756 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _65_21756))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _65_21757 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _65_21757))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _65_21761 = (let _65_21760 = (let _65_21759 = (let _65_21758 = (Microsoft_FStar_ToSMT_Term.mkInteger' i)
in (Microsoft_FStar_ToSMT_Term.boxInt _65_21758))
in (_65_21759)::[])
in ("Int32.Int32", _65_21760))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21761))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _)) -> begin
(let _65_21762 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_bytes bytes)
in (varops.string_const _65_21762))
end
| c -> begin
(let _65_21764 = (let _65_21763 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" _65_21763))
in (failwith (_65_21764)))
end))

let as_function_typ = (fun ( env ) ( t0 ) -> (let rec aux = (fun ( norm ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
(let _65_21773 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _65_21773))
end
| _ -> begin
(match (norm) with
| true -> begin
(let _65_21774 = (whnf env t)
in (aux false _65_21774))
end
| false -> begin
(let _65_21777 = (let _65_21776 = (Support.Microsoft.FStar.Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _65_21775 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Support.Microsoft.FStar.Util.format2 "(%s) Expected a function typ; got %s" _65_21776 _65_21775)))
in (failwith (_65_21777)))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun ( k ) ( env ) -> (match ((let _65_21809 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _65_21809.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k0)) -> begin
(let _50_630 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _65_21811 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _65_21810 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _65_21811 _65_21810)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _)) -> begin
(let _65_21813 = (let _65_21812 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _65_21812))
in (_65_21813, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, kbody)) -> begin
(let tsym = (let _65_21814 = (varops.fresh "t")
in (_65_21814, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let t = (Microsoft_FStar_ToSMT_Term.mkFreeV tsym)
in (let _50_649 = (encode_binders None bs env)
in (match (_50_649) with
| (vars, guards, env', decls, _) -> begin
(let app = (mk_ApplyT t vars)
in (let _50_653 = (encode_knd kbody env' app)
in (match (_50_653) with
| (kbody, decls') -> begin
(let k_interp = (let _65_21818 = (let _65_21817 = (let _65_21816 = (let _65_21815 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_65_21815, kbody))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_21816))
in ((app)::[], vars, _65_21817))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_21818))
in (let cvars = (let _65_21820 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (Support.Prims.pipe_right _65_21820 (Support.List.filter (fun ( _50_658 ) -> (match (_50_658) with
| (x, _) -> begin
(x <> (Support.Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((k', sorts, _)) -> begin
(let _65_21823 = (let _65_21822 = (let _65_21821 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _65_21821))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21822))
in (_65_21823, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _65_21824 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_65_21824))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _65_21826 = (let _65_21825 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _65_21825))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21826))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _65_21835 = (let _65_21834 = (let _65_21833 = (let _65_21832 = (let _65_21831 = (let _65_21830 = (let _65_21829 = (let _65_21828 = (let _65_21827 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _65_21827))
in (_65_21828, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _65_21829))
in (t_has_k, _65_21830))
in (Microsoft_FStar_ToSMT_Term.mkIff _65_21831))
in ((t_has_k)::[], (tsym)::cvars, _65_21832))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_21833))
in (_65_21834, Some ((Support.String.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21835))
in (let k_decls = (Support.List.append (Support.List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _50_676 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end))))
end)))
end))))
end
| _ -> begin
(let _65_21837 = (let _65_21836 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" _65_21836))
in (failwith (_65_21837)))
end))
and encode_knd = (fun ( k ) ( env ) ( t ) -> (let _50_685 = (encode_knd_term k env)
in (match (_50_685) with
| (k, decls) -> begin
(let _65_21841 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_65_21841, decls))
end)))
and encode_binders = (fun ( fuel_opt ) ( bs ) ( env ) -> (let _50_689 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _65_21845 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" _65_21845))
end
| false -> begin
()
end)
in (let _50_739 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _50_696 ) ( b ) -> (match (_50_696) with
| (vars, guards, env, decls, names) -> begin
(let _50_733 = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = a; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _}) -> begin
(let a = (unmangle a)
in (let _50_708 = (gen_typ_var env a)
in (match (_50_708) with
| (aasym, aa, env') -> begin
(let _50_709 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _65_21849 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _65_21848 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _65_21849 aasym _65_21848)))
end
| false -> begin
()
end)
in (let _50_713 = (encode_knd k env aa)
in (match (_50_713) with
| (guard_a_k, decls') -> begin
((aasym, Microsoft_FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', Support.Microsoft.FStar.Util.Inl (a))
end)))
end)))
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _}) -> begin
(let x = (unmangle x)
in (let _50_724 = (gen_term_var env x)
in (match (_50_724) with
| (xxsym, xx, env') -> begin
(let _50_727 = (let _65_21850 = (norm_t env t)
in (encode_typ_pred' fuel_opt _65_21850 env xx))
in (match (_50_727) with
| (guard_x_t, decls') -> begin
((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', Support.Microsoft.FStar.Util.Inr (x))
end))
end)))
end)
in (match (_50_733) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (Support.List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_50_739) with
| (vars, guards, env, decls, names) -> begin
((Support.List.rev vars), (Support.List.rev guards), env, decls, (Support.List.rev names))
end))))
and encode_typ_pred' = (fun ( fuel_opt ) ( t ) ( env ) ( e ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _50_747 = (encode_typ_term t env)
in (match (_50_747) with
| (t, decls) -> begin
(let _65_21855 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_65_21855, decls))
end))))
and encode_typ_term = (fun ( t ) ( env ) -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _65_21858 = (lookup_typ_var env a)
in (_65_21858, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _65_21859 = (lookup_free_tvar env fv)
in (_65_21859, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
(match (((env.encode_non_total_function_typ && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _50_765 = (encode_binders None binders env)
in (match (_50_765) with
| (vars, guards, env', decls, _) -> begin
(let fsym = (let _65_21860 = (varops.fresh "f")
in (_65_21860, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _50_771 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_50_771) with
| (pre_opt, res_t) -> begin
(let _50_774 = (encode_typ_pred' None res_t env' app)
in (match (_50_774) with
| (res_pred, decls') -> begin
(let _50_783 = (match (pre_opt) with
| None -> begin
(let _65_21861 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_65_21861, decls))
end
| Some (pre) -> begin
(let _50_780 = (encode_formula pre env')
in (match (_50_780) with
| (guard, decls0) -> begin
(let _65_21862 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_65_21862, (Support.List.append decls decls0)))
end))
end)
in (match (_50_783) with
| (guards, guard_decls) -> begin
(let t_interp = (let _65_21864 = (let _65_21863 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _65_21863))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_21864))
in (let cvars = (let _65_21866 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (Support.Prims.pipe_right _65_21866 (Support.List.filter (fun ( _50_788 ) -> (match (_50_788) with
| (x, _) -> begin
(x <> (Support.Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _)) -> begin
(let _65_21869 = (let _65_21868 = (let _65_21867 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _65_21867))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21868))
in (_65_21869, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _65_21870 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_65_21870))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _65_21872 = (let _65_21871 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _65_21871))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21872))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _65_21874 = (let _65_21873 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_65_21873, Some ((Support.String.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21874))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let pre_typing = (let _65_21881 = (let _65_21880 = (let _65_21879 = (let _65_21878 = (let _65_21877 = (let _65_21876 = (let _65_21875 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _65_21875))
in (f_has_t, _65_21876))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_21877))
in ((f_has_t)::[], (fsym)::cvars, _65_21878))
in (mkForall_fuel _65_21879))
in (_65_21880, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21881))
in (let t_interp = (let _65_21885 = (let _65_21884 = (let _65_21883 = (let _65_21882 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t, t_interp))
in ((f_has_t)::[], (fsym)::cvars, _65_21882))
in (mkForall_fuel _65_21883))
in (_65_21884, Some ((Support.String.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21885))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _50_809 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
in (let t_kinding = (let _65_21887 = (let _65_21886 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_65_21886, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21887))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _65_21894 = (let _65_21893 = (let _65_21892 = (let _65_21891 = (let _65_21890 = (let _65_21889 = (let _65_21888 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _65_21888))
in (f_has_t, _65_21889))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_21890))
in ((f_has_t)::[], (fsym)::[], _65_21891))
in (mkForall_fuel _65_21892))
in (_65_21893, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21894))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
(let _50_839 = (match ((Microsoft_FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, f)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(x, f)
end
| _ -> begin
(failwith ("impossible"))
end)
in (match (_50_839) with
| (x, f) -> begin
(let _50_842 = (encode_typ_term x.Microsoft_FStar_Absyn_Syntax.sort env)
in (match (_50_842) with
| (base_t, decls) -> begin
(let _50_846 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_846) with
| (x, xtm, env') -> begin
(let _50_849 = (encode_formula f env')
in (match (_50_849) with
| (refinement, decls') -> begin
(let encoding = (let _65_21896 = (let _65_21895 = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t)
in (_65_21895, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _65_21896))
in (let cvars = (let _65_21898 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (Support.Prims.pipe_right _65_21898 (Support.List.filter (fun ( _50_854 ) -> (match (_50_854) with
| (y, _) -> begin
(y <> x)
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _65_21901 = (let _65_21900 = (let _65_21899 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _65_21899))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21900))
in (_65_21901, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _65_21903 = (let _65_21902 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _65_21902))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21903))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _65_21905 = (let _65_21904 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (xfv)::cvars, _65_21904))
in (mkForall_fuel _65_21905))
in (let t_decls = (let _65_21912 = (let _65_21911 = (let _65_21910 = (let _65_21909 = (let _65_21908 = (let _65_21907 = (let _65_21906 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_65_21906))
in (assumption, _65_21907))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21908))
in (_65_21909)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_65_21910)
in (tdecl)::_65_21911)
in (Support.List.append (Support.List.append decls decls') _65_21912))
in (let _50_875 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _65_21913 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _65_21913))
in (let _50_884 = (encode_knd k env ttm)
in (match (_50_884) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let is_full_app = (fun ( _50_891 ) -> (match (()) with
| () -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind head)
in (let _50_896 = (Microsoft_FStar_Absyn_Util.kind_formals kk)
in (match (_50_896) with
| (formals, _) -> begin
((Support.List.length formals) = (Support.List.length args))
end)))
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_typ head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _50_903 = (encode_args args env)
in (match (_50_903) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _50_909 = (encode_args args env)
in (match (_50_909) with
| (args, decls) -> begin
(match ((is_full_app ())) with
| true -> begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _65_21918 = (let _65_21917 = (Support.List.map (fun ( _50_10 ) -> (match (_50_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (head, _65_21917))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21918))
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
(let ttm = (let _65_21919 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _65_21919))
in (let _50_925 = (encode_knd k env ttm)
in (match (_50_925) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _ -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, body)) -> begin
(let _50_940 = (encode_binders None bs env)
in (match (_50_940) with
| (vars, guards, env, decls, _) -> begin
(let _50_943 = (encode_typ_term body env)
in (match (_50_943) with
| (body, decls') -> begin
(let key_body = (let _65_21923 = (let _65_21922 = (let _65_21921 = (let _65_21920 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_65_21920, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_21921))
in ([], vars, _65_21922))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_21923))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _65_21926 = (let _65_21925 = (let _65_21924 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _65_21924))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21925))
in (_65_21926, []))
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
in (let t = (let _65_21928 = (let _65_21927 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _65_21927))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21928))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _65_21935 = (let _65_21934 = (let _65_21933 = (let _65_21932 = (let _65_21931 = (let _65_21930 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _65_21929 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_65_21930, _65_21929)))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_21931))
in ((app)::[], (Support.List.append vars cvars), _65_21932))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_21933))
in (_65_21934, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21935))
in (let kinding = (let _50_966 = (let _65_21936 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _65_21936 env t))
in (match (_50_966) with
| (ktm, decls'') -> begin
(let _65_21940 = (let _65_21939 = (let _65_21938 = (let _65_21937 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_65_21937, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21938))
in (_65_21939)::[])
in (Support.List.append decls'' _65_21940))
end))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _50_969 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(encode_typ_term t env)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_) -> begin
(let _65_21941 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _65_21941 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _65_21946 = (let _65_21945 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _65_21944 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _65_21943 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _65_21942 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _65_21945 _65_21944 _65_21943 _65_21942)))))
in (failwith (_65_21946)))
end)))
and encode_exp = (fun ( e ) ( env ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(let _65_21949 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _65_21949 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _)) -> begin
(let _65_21950 = (lookup_free_var env v)
in (_65_21950, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _65_21951 = (encode_const c)
in (_65_21951, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _)) -> begin
(let _50_1006 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)) -> begin
(let e = (let _65_21952 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _65_21952))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun ( _50_1025 ) -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _65_21955 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_65_21955, (decl)::[]))))
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _50_1029 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _65_21956 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (Support.Prims.pipe_left Support.Prims.op_Negation _65_21956))) with
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
(let _50_1041 = (Support.Microsoft.FStar.Util.first_N nformals bs)
in (match (_50_1041) with
| (bs0, rest) -> begin
(let res_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s (Microsoft_FStar_Absyn_Util.comp_result c))
end
| _ -> begin
(failwith ("Impossible"))
end)
in (let e = (let _65_21958 = (let _65_21957 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _65_21957))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _65_21958 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end
| false -> begin
(let _50_1054 = (encode_binders None bs env)
in (match (_50_1054) with
| (vars, guards, envbody, decls, _) -> begin
(let _50_1057 = (encode_exp body envbody)
in (match (_50_1057) with
| (body, decls') -> begin
(let key_body = (let _65_21962 = (let _65_21961 = (let _65_21960 = (let _65_21959 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_65_21959, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_21960))
in ([], vars, _65_21961))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_21962))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _65_21965 = (let _65_21964 = (let _65_21963 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _65_21963))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21964))
in (_65_21965, []))
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
in (let f = (let _65_21967 = (let _65_21966 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _65_21966))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_21967))
in (let app = (mk_ApplyE f vars)
in (let _50_1079 = (encode_typ_pred' None tfun env f)
in (match (_50_1079) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _65_21969 = (let _65_21968 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_65_21968, Some ((Support.String.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21969))
in (let interp_f = (let _65_21976 = (let _65_21975 = (let _65_21974 = (let _65_21973 = (let _65_21972 = (let _65_21971 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _65_21970 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_65_21971, _65_21970)))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_21972))
in ((app)::[], (Support.List.append vars cvars), _65_21973))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_21974))
in (_65_21975, Some ((Support.String.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21976))
in (let f_decls = (Support.List.append (Support.List.append (Support.List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _50_1083 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end))
end
| _ -> begin
(failwith ("Impossible"))
end))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((l, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl (_), _)::(Support.Microsoft.FStar.Util.Inr (v1), _)::(Support.Microsoft.FStar.Util.Inr (v2), _)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals l.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
(let _50_1122 = (encode_exp v1 env)
in (match (_50_1122) with
| (v1, decls1) -> begin
(let _50_1125 = (encode_exp v2 env)
in (match (_50_1125) with
| (v2, decls2) -> begin
(let _65_21977 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_65_21977, (Support.List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _65_21978 = (whnf_e env e)
in (encode_exp _65_21978 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args_e)) -> begin
(let _50_1148 = (encode_args args_e env)
in (match (_50_1148) with
| (args, decls) -> begin
(let encode_partial_app = (fun ( ht_opt ) -> (let _50_1153 = (encode_exp head env)
in (match (_50_1153) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (Support.List.append decls decls'))
end
| Some ((formals, c)) -> begin
(let _50_1162 = (Support.Microsoft.FStar.Util.first_N (Support.List.length args_e) formals)
in (match (_50_1162) with
| (formals, rest) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _65_21981 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _65_21981 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _50_1167 = (encode_typ_pred' None ty env app_tm)
in (match (_50_1167) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _65_21983 = (let _65_21982 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_65_21982, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21983))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun ( fv ) -> (let _50_1174 = (lookup_free_var_sym env fv)
in (match (_50_1174) with
| (fname, fuel_args) -> begin
(let tm = (let _65_21989 = (let _65_21988 = (let _65_21987 = (Support.List.map (fun ( _50_11 ) -> (match (_50_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (Support.List.append fuel_args _65_21987))
in (fname, _65_21988))
in (Microsoft_FStar_ToSMT_Term.mkApp' _65_21989))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _50_1181 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _65_21991 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _65_21990 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _65_21991 _65_21990)))
end
| false -> begin
()
end)
in (let head_type = (let _65_21994 = (let _65_21993 = (let _65_21992 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _65_21992))
in (whnf env _65_21993))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.unrefine _65_21994))
in (let _50_1184 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _65_21997 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _65_21996 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _65_21995 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _65_21997 _65_21996 _65_21995))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _65_22001 = (let _65_22000 = (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _65_21999 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _65_21998 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" _65_22000 _65_21999 _65_21998))))
in (failwith (_65_22001)))
end
| Some ((formals, c)) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) when ((Support.List.length formals) = (Support.List.length args)) -> begin
(encode_full_app fv)
end
| _ -> begin
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
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (_); Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = _}::[]), _)) -> begin
(failwith ("Impossible: already handled by encoding of Sig_let"))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (x); Microsoft_FStar_Absyn_Syntax.lbtyp = t1; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let _50_1230 = (encode_exp e1 env)
in (match (_50_1230) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _50_1234 = (encode_exp e2 env')
in (match (_50_1234) with
| (ee2, decls2) -> begin
(ee2, (Support.List.append decls1 decls2))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_) -> begin
(let _50_1238 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = Microsoft_FStar_ToSMT_Term.DeclFun ((e, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _65_22002 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_65_22002, (decl_e)::[])))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _50_1248 = (encode_exp e env)
in (match (_50_1248) with
| (scr, decls) -> begin
(let _50_1288 = (Support.List.fold_right (fun ( _50_1252 ) ( _50_1255 ) -> (match ((_50_1252, _50_1255)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (Support.List.fold_right (fun ( _50_1259 ) ( _50_1262 ) -> (match ((_50_1259, _50_1262)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (Support.Prims.pipe_right projections (Support.List.fold_left (fun ( env ) ( _50_1268 ) -> (match (_50_1268) with
| (x, t) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v t)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _50_1282 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _50_1279 = (encode_exp w env)
in (match (_50_1279) with
| (w, decls2) -> begin
(let _65_22013 = (let _65_22012 = (let _65_22011 = (let _65_22010 = (let _65_22009 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _65_22009))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_22010))
in (guard, _65_22011))
in (Microsoft_FStar_ToSMT_Term.mkAnd _65_22012))
in (_65_22013, decls2))
end))
end)
in (match (_50_1282) with
| (guard, decls2) -> begin
(let _50_1285 = (encode_exp br env)
in (match (_50_1285) with
| (br, decls3) -> begin
(let _65_22014 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_65_22014, (Support.List.append (Support.List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (Microsoft_FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_50_1288) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (_) -> begin
(let _65_22017 = (let _65_22016 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _65_22015 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" _65_22016 _65_22015)))
in (failwith (_65_22017)))
end))))
and encode_pat = (fun ( env ) ( pat ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _ -> begin
(let _65_22020 = (encode_one_pat env pat)
in (_65_22020)::[])
end))
and encode_one_pat = (fun ( env ) ( pat ) -> (let _50_1300 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _65_22023 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" _65_22023))
end
| false -> begin
()
end)
in (let _50_1304 = (Microsoft_FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_50_1304) with
| (vars, pat_exp_or_typ) -> begin
(let _50_1325 = (Support.Prims.pipe_right vars (Support.List.fold_left (fun ( _50_1307 ) ( v ) -> (match (_50_1307) with
| (env, vars) -> begin
(match (v) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _50_1315 = (gen_typ_var env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_1315) with
| (aa, _, env) -> begin
(env, ((v, (aa, Microsoft_FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _50_1322 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_1322) with
| (xx, _, env) -> begin
(env, ((v, (xx, Microsoft_FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_50_1325) with
| (env, vars) -> begin
(let rec mk_guard = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
Microsoft_FStar_ToSMT_Term.mkTrue
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _65_22031 = (let _65_22030 = (encode_const c)
in (scrutinee, _65_22030))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_22031))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (Support.Prims.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _65_22034 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _65_22034))))))
in (Microsoft_FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((Support.Microsoft.FStar.Util.Inr (x), scrutinee))::[]
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((Support.Microsoft.FStar.Util.Inl (a), scrutinee))::[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _, args)) -> begin
(let _65_22042 = (Support.Prims.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _65_22041 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _65_22041))))))
in (Support.Prims.pipe_right _65_22042 Support.List.flatten))
end))
in (let pat_term = (fun ( _50_1399 ) -> (match (()) with
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
and encode_args = (fun ( l ) ( env ) -> (let _50_1429 = (Support.Prims.pipe_right l (Support.List.fold_left (fun ( _50_1409 ) ( x ) -> (match (_50_1409) with
| (tms, decls) -> begin
(match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let _50_1418 = (encode_typ_term t env)
in (match (_50_1418) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inl (t))::tms, (Support.List.append decls decls'))
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(let _50_1426 = (encode_exp e env)
in (match (_50_1426) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inr (t))::tms, (Support.List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_50_1429) with
| (l, decls) -> begin
((Support.List.rev l), decls)
end)))
and encode_formula = (fun ( phi ) ( env ) -> (let _50_1435 = (encode_formula_with_labels phi env)
in (match (_50_1435) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _ -> begin
(failwith ("Unexpected labels in formula"))
end)
end)))
and encode_function_type_as_formula = (fun ( induction_on ) ( t ) ( env ) -> (let v_or_t_pat = (fun ( p ) -> (match ((let _65_22056 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _65_22056.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, (Support.Microsoft.FStar.Util.Inl (_), _)::(Support.Microsoft.FStar.Util.Inr (e), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, (Support.Microsoft.FStar.Util.Inl (t), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _ -> begin
(failwith ("Unexpected pattern term"))
end))
in (let rec lemma_pats = (fun ( p ) -> (match ((let _65_22059 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _65_22059.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, _::(Support.Microsoft.FStar.Util.Inr (hd), _)::(Support.Microsoft.FStar.Util.Inr (tl), _)::[])) -> begin
(let _65_22061 = (v_or_t_pat hd)
in (let _65_22060 = (lemma_pats tl)
in (_65_22061)::_65_22060))
end
| _ -> begin
[]
end))
in (let _50_1531 = (match ((let _65_22062 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _65_22062.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _)::(Support.Microsoft.FStar.Util.Inl (post), _)::(Support.Microsoft.FStar.Util.Inr (pats), _)::[] -> begin
(let _65_22063 = (lemma_pats pats)
in (binders, pre, post, _65_22063))
end
| _ -> begin
(failwith ("impos"))
end)
end
| _ -> begin
(failwith ("Impos"))
end)
in (match (_50_1531) with
| (binders, pre, post, patterns) -> begin
(let _50_1538 = (encode_binders None binders env)
in (match (_50_1538) with
| (vars, guards, env, decls, _) -> begin
(let _50_1554 = (let _65_22065 = (Support.Prims.pipe_right patterns (Support.List.map (fun ( _50_12 ) -> (match (_50_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _50_1550 = env
in {bindings = _50_1550.bindings; depth = _50_1550.depth; tcenv = _50_1550.tcenv; warn = _50_1550.warn; cache = _50_1550.cache; nolabels = _50_1550.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1550.encode_non_total_function_typ}))
end))))
in (Support.Prims.pipe_right _65_22065 Support.List.unzip))
in (match (_50_1554) with
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
(let _65_22067 = (let _65_22066 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _65_22066 e))
in (_65_22067)::pats)
end
| _ -> begin
(let rec aux = (fun ( tl ) ( vars ) -> (match (vars) with
| [] -> begin
(let _65_22072 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_65_22072)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _65_22074 = (let _65_22073 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _65_22073 tl))
in (aux _65_22074 vars))
end
| _ -> begin
pats
end))
in (let _65_22075 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _65_22075 vars)))
end)
end)
in (let env = (let _50_1575 = env
in {bindings = _50_1575.bindings; depth = _50_1575.depth; tcenv = _50_1575.tcenv; warn = _50_1575.warn; cache = _50_1575.cache; nolabels = true; use_zfuel_name = _50_1575.use_zfuel_name; encode_non_total_function_typ = _50_1575.encode_non_total_function_typ})
in (let _50_1580 = (let _65_22076 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _65_22076 env))
in (match (_50_1580) with
| (pre, decls'') -> begin
(let _50_1583 = (let _65_22077 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _65_22077 env))
in (match (_50_1583) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in (let _65_22082 = (let _65_22081 = (let _65_22080 = (let _65_22079 = (let _65_22078 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_65_22078, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22079))
in (pats, vars, _65_22080))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22081))
in (_65_22082, decls)))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun ( phi ) ( env ) -> (let enc = (fun ( f ) -> (fun ( l ) -> (let _50_1604 = (Support.Microsoft.FStar.Util.fold_map (fun ( decls ) ( x ) -> (match ((Support.Prims.fst x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _50_1596 = (encode_typ_term t env)
in (match (_50_1596) with
| (t, decls') -> begin
((Support.List.append decls decls'), t)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _50_1601 = (encode_exp e env)
in (match (_50_1601) with
| (e, decls') -> begin
((Support.List.append decls decls'), e)
end))
end)) [] l)
in (match (_50_1604) with
| (decls, args) -> begin
(let _65_22100 = (f args)
in (_65_22100, [], decls))
end))))
in (let enc_prop_c = (fun ( f ) -> (fun ( l ) -> (let _50_1624 = (Support.List.fold_right (fun ( t ) ( _50_1612 ) -> (match (_50_1612) with
| (phis, labs, decls) -> begin
(match ((Support.Prims.fst t)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _50_1618 = (encode_formula_with_labels t env)
in (match (_50_1618) with
| (phi, labs', decls') -> begin
((phi)::phis, (Support.List.append labs' labs), (Support.List.append decls' decls))
end))
end
| _ -> begin
(failwith ("Expected a formula"))
end)
end)) l ([], [], []))
in (match (_50_1624) with
| (phis, labs, decls) -> begin
(let _65_22116 = (f phis)
in (_65_22116, labs, decls))
end))))
in (let const_op = (fun ( f ) ( _50_1627 ) -> (f, [], []))
in (let un_op = (fun ( f ) ( l ) -> (let _65_22130 = (Support.List.hd l)
in (Support.Prims.pipe_left f _65_22130)))
in (let bin_op = (fun ( f ) ( _50_13 ) -> (match (_50_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _ -> begin
(failwith ("Impossible"))
end))
in (let tri_op = (fun ( f ) ( _50_14 ) -> (match (_50_14) with
| t1::t2::t3::[] -> begin
(f (t1, t2, t3))
end
| _ -> begin
(failwith ("Impossible"))
end))
in (let eq_op = (fun ( _50_15 ) -> (match (_50_15) with
| _::_::e1::e2::[] -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun ( _50_16 ) -> (match (_50_16) with
| (Support.Microsoft.FStar.Util.Inl (lhs), _)::(Support.Microsoft.FStar.Util.Inl (rhs), _)::[] -> begin
(let _50_1674 = (encode_formula_with_labels rhs env)
in (match (_50_1674) with
| (l1, labs1, decls1) -> begin
(match (l1.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _)) -> begin
(l1, labs1, decls1)
end
| _ -> begin
(let _50_1685 = (encode_formula_with_labels lhs env)
in (match (_50_1685) with
| (l2, labs2, decls2) -> begin
(let _65_22153 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_65_22153, (Support.List.append labs1 labs2), (Support.List.append decls1 decls2)))
end))
end)
end))
end
| _ -> begin
(failwith ("impossible"))
end))
in (let mk_ite = (fun ( _50_17 ) -> (match (_50_17) with
| (Support.Microsoft.FStar.Util.Inl (guard), _)::(Support.Microsoft.FStar.Util.Inl (_then), _)::(Support.Microsoft.FStar.Util.Inl (_else), _)::[] -> begin
(let _50_1709 = (encode_formula_with_labels guard env)
in (match (_50_1709) with
| (g, labs1, decls1) -> begin
(let _50_1713 = (encode_formula_with_labels _then env)
in (match (_50_1713) with
| (t, labs2, decls2) -> begin
(let _50_1717 = (encode_formula_with_labels _else env)
in (match (_50_1717) with
| (e, labs3, decls3) -> begin
(let res = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (Support.List.append (Support.List.append labs1 labs2) labs3), (Support.List.append (Support.List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _ -> begin
(failwith ("impossible"))
end))
in (let unboxInt_l = (fun ( f ) ( l ) -> (let _65_22165 = (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _65_22165)))
in (let connectives = (let _65_22226 = (let _65_22174 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _65_22174))
in (let _65_22225 = (let _65_22224 = (let _65_22180 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _65_22180))
in (let _65_22223 = (let _65_22222 = (let _65_22221 = (let _65_22189 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _65_22189))
in (let _65_22220 = (let _65_22219 = (let _65_22218 = (let _65_22198 = (Support.Prims.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _65_22198))
in (let _65_22217 = (let _65_22216 = (let _65_22204 = (Support.Prims.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _65_22204))
in (_65_22216)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_65_22218)::_65_22217))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_65_22219)
in (_65_22221)::_65_22220))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_65_22222)
in (_65_22224)::_65_22223))
in (_65_22226)::_65_22225))
in (let fallback = (fun ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((phi', msg, r, b))) -> begin
(let _50_1738 = (encode_formula_with_labels phi' env)
in (match (_50_1738) with
| (phi, labs, decls) -> begin
(match (env.nolabels) with
| true -> begin
(phi, [], decls)
end
| false -> begin
(let lvar = (let _65_22229 = (varops.fresh "label")
in (_65_22229, Microsoft_FStar_ToSMT_Term.Bool_sort))
in (let lterm = (Microsoft_FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (Microsoft_FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ih); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inr (l), _)::(Support.Microsoft.FStar.Util.Inl (phi), _)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals ih.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.using_IH) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let _50_1770 = (encode_exp l env)
in (match (_50_1770) with
| (e, decls) -> begin
(let _50_1773 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_50_1773) with
| (f, decls') -> begin
(f, [], (Support.List.append decls decls'))
end))
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.mkTrue, [], [])
end)
end
| _ -> begin
(let _50_1778 = (encode_typ_term phi env)
in (match (_50_1778) with
| (tt, decls) -> begin
(let _65_22230 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_65_22230, [], decls))
end))
end))
in (let encode_q_body = (fun ( env ) ( bs ) ( ps ) ( body ) -> (let _50_1790 = (encode_binders None bs env)
in (match (_50_1790) with
| (vars, guards, env, decls, _) -> begin
(let _50_1806 = (let _65_22240 = (Support.Prims.pipe_right ps (Support.List.map (fun ( _50_18 ) -> (match (_50_18) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_typ_term t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _50_1802 = env
in {bindings = _50_1802.bindings; depth = _50_1802.depth; tcenv = _50_1802.tcenv; warn = _50_1802.warn; cache = _50_1802.cache; nolabels = _50_1802.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1802.encode_non_total_function_typ}))
end))))
in (Support.Prims.pipe_right _65_22240 Support.List.unzip))
in (match (_50_1806) with
| (pats, decls') -> begin
(let _50_1810 = (encode_formula_with_labels body env)
in (match (_50_1810) with
| (body, labs, decls'') -> begin
(let _65_22241 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _65_22241, body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'')))
end))
end))
end)))
in (let _50_1811 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _65_22242 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" _65_22242))
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
(match ((Support.Prims.pipe_right connectives (Support.List.tryFind (fun ( _50_1823 ) -> (match (_50_1823) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some ((_, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, pats, body))) -> begin
(let _50_1836 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _65_22258 = (Support.Prims.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" _65_22258))
end
| false -> begin
()
end)
in (let _50_1844 = (encode_q_body env vars pats body)
in (match (_50_1844) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _65_22261 = (let _65_22260 = (let _65_22259 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _65_22259))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22260))
in (_65_22261, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _50_1857 = (encode_q_body env vars pats body)
in (match (_50_1857) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _65_22264 = (let _65_22263 = (let _65_22262 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _65_22262))
in (Microsoft_FStar_ToSMT_Term.mkExists _65_22263))
in (_65_22264, labs, decls))
end))
end)))))))))))))))))

type prims_t =
{mk : Microsoft_FStar_Absyn_Syntax.lident  ->  string  ->  Microsoft_FStar_ToSMT_Term.decl list; is : Microsoft_FStar_Absyn_Syntax.lident  ->  bool}

let is_Mkprims_t = (fun ( _ ) -> (failwith ("Not yet implemented")))

let prims = (let _50_1863 = (fresh_fvar "a" Microsoft_FStar_ToSMT_Term.Type_sort)
in (match (_50_1863) with
| (asym, a) -> begin
(let _50_1866 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_50_1866) with
| (xsym, x) -> begin
(let _50_1869 = (fresh_fvar "y" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_50_1869) with
| (ysym, y) -> begin
(let deffun = (fun ( vars ) ( body ) ( x ) -> (Microsoft_FStar_ToSMT_Term.DefineFun ((x, vars, Microsoft_FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun ( vars ) ( body ) -> (fun ( x ) -> (let t1 = (let _65_22307 = (let _65_22306 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _65_22306))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22307))
in (let vname_decl = (let _65_22309 = (let _65_22308 = (Support.Prims.pipe_right vars (Support.List.map Support.Prims.snd))
in (x, _65_22308, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_65_22309))
in (let _65_22315 = (let _65_22314 = (let _65_22313 = (let _65_22312 = (let _65_22311 = (let _65_22310 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _65_22310))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22311))
in (_65_22312, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22313))
in (_65_22314)::[])
in (vname_decl)::_65_22315)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _65_22475 = (let _65_22324 = (let _65_22323 = (let _65_22322 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22322))
in (quant axy _65_22323))
in (Microsoft_FStar_Absyn_Const.op_Eq, _65_22324))
in (let _65_22474 = (let _65_22473 = (let _65_22331 = (let _65_22330 = (let _65_22329 = (let _65_22328 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _65_22328))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22329))
in (quant axy _65_22330))
in (Microsoft_FStar_Absyn_Const.op_notEq, _65_22331))
in (let _65_22472 = (let _65_22471 = (let _65_22340 = (let _65_22339 = (let _65_22338 = (let _65_22337 = (let _65_22336 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22335 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22336, _65_22335)))
in (Microsoft_FStar_ToSMT_Term.mkLT _65_22337))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22338))
in (quant xy _65_22339))
in (Microsoft_FStar_Absyn_Const.op_LT, _65_22340))
in (let _65_22470 = (let _65_22469 = (let _65_22349 = (let _65_22348 = (let _65_22347 = (let _65_22346 = (let _65_22345 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22344 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22345, _65_22344)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _65_22346))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22347))
in (quant xy _65_22348))
in (Microsoft_FStar_Absyn_Const.op_LTE, _65_22349))
in (let _65_22468 = (let _65_22467 = (let _65_22358 = (let _65_22357 = (let _65_22356 = (let _65_22355 = (let _65_22354 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22353 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22354, _65_22353)))
in (Microsoft_FStar_ToSMT_Term.mkGT _65_22355))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22356))
in (quant xy _65_22357))
in (Microsoft_FStar_Absyn_Const.op_GT, _65_22358))
in (let _65_22466 = (let _65_22465 = (let _65_22367 = (let _65_22366 = (let _65_22365 = (let _65_22364 = (let _65_22363 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22362 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22363, _65_22362)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _65_22364))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22365))
in (quant xy _65_22366))
in (Microsoft_FStar_Absyn_Const.op_GTE, _65_22367))
in (let _65_22464 = (let _65_22463 = (let _65_22376 = (let _65_22375 = (let _65_22374 = (let _65_22373 = (let _65_22372 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22371 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22372, _65_22371)))
in (Microsoft_FStar_ToSMT_Term.mkSub _65_22373))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _65_22374))
in (quant xy _65_22375))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _65_22376))
in (let _65_22462 = (let _65_22461 = (let _65_22383 = (let _65_22382 = (let _65_22381 = (let _65_22380 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _65_22380))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _65_22381))
in (quant qx _65_22382))
in (Microsoft_FStar_Absyn_Const.op_Minus, _65_22383))
in (let _65_22460 = (let _65_22459 = (let _65_22392 = (let _65_22391 = (let _65_22390 = (let _65_22389 = (let _65_22388 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22387 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22388, _65_22387)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _65_22389))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _65_22390))
in (quant xy _65_22391))
in (Microsoft_FStar_Absyn_Const.op_Addition, _65_22392))
in (let _65_22458 = (let _65_22457 = (let _65_22401 = (let _65_22400 = (let _65_22399 = (let _65_22398 = (let _65_22397 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22396 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22397, _65_22396)))
in (Microsoft_FStar_ToSMT_Term.mkMul _65_22398))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _65_22399))
in (quant xy _65_22400))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _65_22401))
in (let _65_22456 = (let _65_22455 = (let _65_22410 = (let _65_22409 = (let _65_22408 = (let _65_22407 = (let _65_22406 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22405 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22406, _65_22405)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _65_22407))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _65_22408))
in (quant xy _65_22409))
in (Microsoft_FStar_Absyn_Const.op_Division, _65_22410))
in (let _65_22454 = (let _65_22453 = (let _65_22419 = (let _65_22418 = (let _65_22417 = (let _65_22416 = (let _65_22415 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22414 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_65_22415, _65_22414)))
in (Microsoft_FStar_ToSMT_Term.mkMod _65_22416))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _65_22417))
in (quant xy _65_22418))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _65_22419))
in (let _65_22452 = (let _65_22451 = (let _65_22428 = (let _65_22427 = (let _65_22426 = (let _65_22425 = (let _65_22424 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _65_22423 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_65_22424, _65_22423)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _65_22425))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22426))
in (quant xy _65_22427))
in (Microsoft_FStar_Absyn_Const.op_And, _65_22428))
in (let _65_22450 = (let _65_22449 = (let _65_22437 = (let _65_22436 = (let _65_22435 = (let _65_22434 = (let _65_22433 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _65_22432 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_65_22433, _65_22432)))
in (Microsoft_FStar_ToSMT_Term.mkOr _65_22434))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22435))
in (quant xy _65_22436))
in (Microsoft_FStar_Absyn_Const.op_Or, _65_22437))
in (let _65_22448 = (let _65_22447 = (let _65_22444 = (let _65_22443 = (let _65_22442 = (let _65_22441 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _65_22441))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_22442))
in (quant qx _65_22443))
in (Microsoft_FStar_Absyn_Const.op_Negation, _65_22444))
in (_65_22447)::[])
in (_65_22449)::_65_22448))
in (_65_22451)::_65_22450))
in (_65_22453)::_65_22452))
in (_65_22455)::_65_22454))
in (_65_22457)::_65_22456))
in (_65_22459)::_65_22458))
in (_65_22461)::_65_22460))
in (_65_22463)::_65_22462))
in (_65_22465)::_65_22464))
in (_65_22467)::_65_22466))
in (_65_22469)::_65_22468))
in (_65_22471)::_65_22470))
in (_65_22473)::_65_22472))
in (_65_22475)::_65_22474))
in (let mk = (fun ( l ) ( v ) -> (let _65_22506 = (Support.Prims.pipe_right prims (Support.List.filter (fun ( _50_1889 ) -> (match (_50_1889) with
| (l', _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (Support.Prims.pipe_right _65_22506 (Support.List.collect (fun ( _50_1893 ) -> (match (_50_1893) with
| (_, b) -> begin
(b v)
end))))))
in (let is = (fun ( l ) -> (Support.Prims.pipe_right prims (Support.Microsoft.FStar.Util.for_some (fun ( _50_1899 ) -> (match (_50_1899) with
| (l', _) -> begin
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
in (let mk_unit = (fun ( _50_1905 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let _65_22537 = (let _65_22528 = (let _65_22527 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_65_22527, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22528))
in (let _65_22536 = (let _65_22535 = (let _65_22534 = (let _65_22533 = (let _65_22532 = (let _65_22531 = (let _65_22530 = (let _65_22529 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _65_22529))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22530))
in ((typing_pred)::[], (xx)::[], _65_22531))
in (mkForall_fuel _65_22532))
in (_65_22533, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22534))
in (_65_22535)::[])
in (_65_22537)::_65_22536))))
in (let mk_bool = (fun ( _50_1910 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _65_22557 = (let _65_22547 = (let _65_22546 = (let _65_22545 = (let _65_22544 = (let _65_22543 = (let _65_22542 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _65_22542))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22543))
in ((typing_pred)::[], (xx)::[], _65_22544))
in (mkForall_fuel _65_22545))
in (_65_22546, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22547))
in (let _65_22556 = (let _65_22555 = (let _65_22554 = (let _65_22553 = (let _65_22552 = (let _65_22551 = (let _65_22548 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_65_22548)::[])
in (let _65_22550 = (let _65_22549 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _65_22549 tt))
in (_65_22551, (bb)::[], _65_22550)))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22552))
in (_65_22553, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22554))
in (_65_22555)::[])
in (_65_22557)::_65_22556))))))
in (let mk_int = (fun ( _50_1917 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _65_22569 = (let _65_22568 = (let _65_22567 = (let _65_22566 = (let _65_22565 = (let _65_22564 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _65_22563 = (let _65_22562 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_65_22562)::[])
in (_65_22564)::_65_22563))
in (tt)::_65_22565)
in (tt)::_65_22566)
in ("Prims.Precedes", _65_22567))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22568))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _65_22569))
in (let precedes_y_x = (let _65_22570 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _65_22570))
in (let _65_22611 = (let _65_22576 = (let _65_22575 = (let _65_22574 = (let _65_22573 = (let _65_22572 = (let _65_22571 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _65_22571))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22572))
in ((typing_pred)::[], (xx)::[], _65_22573))
in (mkForall_fuel _65_22574))
in (_65_22575, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22576))
in (let _65_22610 = (let _65_22609 = (let _65_22583 = (let _65_22582 = (let _65_22581 = (let _65_22580 = (let _65_22577 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_65_22577)::[])
in (let _65_22579 = (let _65_22578 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _65_22578 tt))
in (_65_22580, (bb)::[], _65_22579)))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22581))
in (_65_22582, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22583))
in (let _65_22608 = (let _65_22607 = (let _65_22606 = (let _65_22605 = (let _65_22604 = (let _65_22603 = (let _65_22602 = (let _65_22601 = (let _65_22600 = (let _65_22599 = (let _65_22598 = (let _65_22597 = (let _65_22586 = (let _65_22585 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _65_22584 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_65_22585, _65_22584)))
in (Microsoft_FStar_ToSMT_Term.mkGT _65_22586))
in (let _65_22596 = (let _65_22595 = (let _65_22589 = (let _65_22588 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _65_22587 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_65_22588, _65_22587)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _65_22589))
in (let _65_22594 = (let _65_22593 = (let _65_22592 = (let _65_22591 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _65_22590 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_65_22591, _65_22590)))
in (Microsoft_FStar_ToSMT_Term.mkLT _65_22592))
in (_65_22593)::[])
in (_65_22595)::_65_22594))
in (_65_22597)::_65_22596))
in (typing_pred_y)::_65_22598)
in (typing_pred)::_65_22599)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _65_22600))
in (_65_22601, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22602))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _65_22603))
in (mkForall_fuel _65_22604))
in (_65_22605, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22606))
in (_65_22607)::[])
in (_65_22609)::_65_22608))
in (_65_22611)::_65_22610)))))))))))
in (let mk_int_alias = (fun ( _50_1929 ) ( tt ) -> (let _65_22620 = (let _65_22619 = (let _65_22618 = (let _65_22617 = (let _65_22616 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _65_22616))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_22617))
in (_65_22618, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22619))
in (_65_22620)::[]))
in (let mk_str = (fun ( _50_1933 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _65_22640 = (let _65_22630 = (let _65_22629 = (let _65_22628 = (let _65_22627 = (let _65_22626 = (let _65_22625 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _65_22625))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22626))
in ((typing_pred)::[], (xx)::[], _65_22627))
in (mkForall_fuel _65_22628))
in (_65_22629, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22630))
in (let _65_22639 = (let _65_22638 = (let _65_22637 = (let _65_22636 = (let _65_22635 = (let _65_22634 = (let _65_22631 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_65_22631)::[])
in (let _65_22633 = (let _65_22632 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _65_22632 tt))
in (_65_22634, (bb)::[], _65_22633)))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22635))
in (_65_22636, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22637))
in (_65_22638)::[])
in (_65_22640)::_65_22639))))))
in (let mk_ref = (fun ( reft_name ) ( _50_1941 ) -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _65_22647 = (let _65_22646 = (let _65_22645 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_65_22645)::[])
in (reft_name, _65_22646))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22647))
in (let refb = (let _65_22650 = (let _65_22649 = (let _65_22648 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_65_22648)::[])
in (reft_name, _65_22649))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22650))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _65_22669 = (let _65_22656 = (let _65_22655 = (let _65_22654 = (let _65_22653 = (let _65_22652 = (let _65_22651 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _65_22651))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22652))
in ((typing_pred)::[], (xx)::(aa)::[], _65_22653))
in (mkForall_fuel _65_22654))
in (_65_22655, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22656))
in (let _65_22668 = (let _65_22667 = (let _65_22666 = (let _65_22665 = (let _65_22664 = (let _65_22663 = (let _65_22662 = (let _65_22661 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _65_22660 = (let _65_22659 = (let _65_22658 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _65_22657 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_65_22658, _65_22657)))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_22659))
in (_65_22661, _65_22660)))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22662))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _65_22663))
in (mkForall_fuel' 2 _65_22664))
in (_65_22665, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22666))
in (_65_22667)::[])
in (_65_22669)::_65_22668))))))))))
in (let prims = ((Microsoft_FStar_Absyn_Const.unit_lid, mk_unit))::((Microsoft_FStar_Absyn_Const.bool_lid, mk_bool))::((Microsoft_FStar_Absyn_Const.int_lid, mk_int))::((Microsoft_FStar_Absyn_Const.string_lid, mk_str))::((Microsoft_FStar_Absyn_Const.ref_lid, mk_ref))::((Microsoft_FStar_Absyn_Const.char_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.uint8_lid, mk_int_alias))::[]
in (fun ( t ) ( s ) ( tt ) -> (match ((Support.Microsoft.FStar.Util.find_opt (fun ( _50_1958 ) -> (match (_50_1958) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some ((_, f)) -> begin
(f s tt)
end)))))))))))))

let rec encode_sigelt = (fun ( env ) ( se ) -> (let _50_1967 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _65_22762 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") _65_22762))
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
in (let _50_1975 = (encode_sigelt' env se)
in (match (_50_1975) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _65_22765 = (let _65_22764 = (let _65_22763 = (Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_65_22763))
in (_65_22764)::[])
in (_65_22765, e))
end
| _ -> begin
(let _65_22772 = (let _65_22771 = (let _65_22767 = (let _65_22766 = (Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_65_22766))
in (_65_22767)::g)
in (let _65_22770 = (let _65_22769 = (let _65_22768 = (Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_65_22768))
in (_65_22769)::[])
in (Support.List.append _65_22771 _65_22770)))
in (_65_22772, e))
end)
end)))))
and encode_sigelt' = (fun ( env ) ( se ) -> (let should_skip = (fun ( l ) -> ((((Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.pure_") || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.ex_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.st_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.all_")))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_, _, _, _, Microsoft_FStar_Absyn_Syntax.Effect::[], _)) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _, _, _, _, _)) when (should_skip lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _, _, _, _, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.b2t_lid) -> begin
(let _50_2026 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2026) with
| (tname, ttok, env) -> begin
(let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _65_22777 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _65_22777))
in (let decls = (let _65_22785 = (let _65_22784 = (let _65_22783 = (let _65_22782 = (let _65_22781 = (let _65_22780 = (let _65_22779 = (let _65_22778 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _65_22778))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_22779))
in ((valid_b2t_x)::[], (xx)::[], _65_22780))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22781))
in (_65_22782, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22783))
in (_65_22784)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_65_22785)
in (decls, env)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _, t, tags, _)) -> begin
(let _50_2044 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2044) with
| (tname, ttok, env) -> begin
(let _50_2053 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((tps', body)) -> begin
((Support.List.append tps tps'), body)
end
| _ -> begin
(tps, t)
end)
in (match (_50_2053) with
| (tps, t) -> begin
(let _50_2060 = (encode_binders None tps env)
in (match (_50_2060) with
| (vars, guards, env', binder_decls, _) -> begin
(let tok_app = (let _65_22786 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _65_22786 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _65_22788 = (let _65_22787 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _65_22787))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22788))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _ -> begin
(let _65_22790 = (let _65_22789 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _65_22789))
in (_65_22790)::[])
end)
in (let decls = (let _65_22801 = (let _65_22794 = (let _65_22793 = (let _65_22792 = (let _65_22791 = (Support.List.map Support.Prims.snd vars)
in (tname, _65_22791, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_65_22792))
in (_65_22793)::(tok_decl)::[])
in (Support.List.append _65_22794 fresh_tok))
in (let _65_22800 = (let _65_22799 = (let _65_22798 = (let _65_22797 = (let _65_22796 = (let _65_22795 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _65_22795))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22796))
in (_65_22797, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22798))
in (_65_22799)::[])
in (Support.List.append _65_22801 _65_22800)))
in (let t = (whnf env t)
in (let _50_2078 = (match ((Support.Prims.pipe_right tags (Support.Microsoft.FStar.Util.for_some (fun ( _50_19 ) -> (match (_50_19) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _ -> begin
false
end))))) with
| true -> begin
(let _65_22804 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _65_22803 = (encode_formula t env')
in (_65_22804, _65_22803)))
end
| false -> begin
(let _65_22805 = (encode_typ_term t env')
in (app, _65_22805))
end)
in (match (_50_2078) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _65_22812 = (let _65_22811 = (let _65_22810 = (let _65_22809 = (let _65_22808 = (let _65_22807 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _65_22806 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_65_22807, _65_22806)))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22808))
in ((def)::[], vars, _65_22809))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22810))
in (_65_22811, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22812))
in (let kindingAx = (let _50_2082 = (let _65_22813 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _65_22813 env' app))
in (match (_50_2082) with
| (k, decls) -> begin
(let _65_22821 = (let _65_22820 = (let _65_22819 = (let _65_22818 = (let _65_22817 = (let _65_22816 = (let _65_22815 = (let _65_22814 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_65_22814, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22815))
in ((app)::[], vars, _65_22816))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22817))
in (_65_22818, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22819))
in (_65_22820)::[])
in (Support.List.append decls _65_22821))
end))
in (let g = (Support.List.append (Support.List.append (Support.List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx))
in (g, env))))
end))))))))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _)) -> begin
(let tt = (whnf env t)
in (let _50_2095 = (encode_free_var env lid t tt quals)
in (match (_50_2095) with
| (decls, env) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_smt_lemma t) && ((Support.Prims.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption)) || env.tcenv.Microsoft_FStar_Tc_Env.is_iface))) with
| true -> begin
(let _65_22823 = (let _65_22822 = (encode_smt_lemma env lid t)
in (Support.List.append decls _65_22822))
in (_65_22823, env))
end
| false -> begin
(decls, env)
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((l, f, _, _)) -> begin
(let _50_2106 = (encode_formula f env)
in (match (_50_2106) with
| (f, decls) -> begin
(let g = (let _65_22828 = (let _65_22827 = (let _65_22826 = (let _65_22825 = (let _65_22824 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "Assumption: %s" _65_22824))
in Some (_65_22825))
in (f, _65_22826))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22827))
in (_65_22828)::[])
in ((Support.List.append decls g), env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _, datas, quals, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.precedes_lid) -> begin
(let _50_2122 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2122) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, _, _, _, _, _, _)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.char_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.Microsoft_FStar_Absyn_Syntax.str
in (let tsym = (Microsoft_FStar_ToSMT_Term.mkFreeV (tname, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((tname, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let _65_22830 = (let _65_22829 = (primitive_type_axioms t tname tsym)
in (decl)::_65_22829)
in (_65_22830, (push_free_tvar env t tname (Some (tsym))))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _, datas, quals, _)) -> begin
(let is_logical = (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _50_20 ) -> (match (_50_20) with
| (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _ -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun ( c ) -> (match (is_logical) with
| true -> begin
(let _50_2166 = c
in (match (_50_2166) with
| (name, args, _, _) -> begin
(let _65_22836 = (let _65_22835 = (let _65_22834 = (Support.Prims.pipe_right args (Support.List.map Support.Prims.snd))
in (name, _65_22834, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_65_22835))
in (_65_22836)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun ( tapp ) ( vars ) -> (match ((((Support.List.length datas) = 0) || (Support.Prims.pipe_right datas (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (let _65_22842 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (Support.Prims.pipe_right _65_22842 Support.Option.isNone))))))) with
| true -> begin
[]
end
| false -> begin
(let _50_2173 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_50_2173) with
| (xxsym, xx) -> begin
(let _50_2216 = (Support.Prims.pipe_right datas (Support.List.fold_left (fun ( _50_2176 ) ( l ) -> (match (_50_2176) with
| (out, decls) -> begin
(let data_t = (Microsoft_FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _50_2186 = (match ((Microsoft_FStar_Absyn_Util.function_formals data_t)) with
| Some ((formals, res)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_50_2186) with
| (args, res) -> begin
(let indices = (match ((let _65_22845 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _65_22845.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_, indices)) -> begin
indices
end
| _ -> begin
[]
end)
in (let env = (Support.Prims.pipe_right args (Support.List.fold_left (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _65_22850 = (let _65_22849 = (let _65_22848 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_65_22848, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22849))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _65_22850))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _65_22853 = (let _65_22852 = (let _65_22851 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_65_22851, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22852))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _65_22853))
end)) env))
in (let _50_2204 = (encode_args indices env)
in (match (_50_2204) with
| (indices, decls') -> begin
(let _50_2205 = (match (((Support.List.length indices) <> (Support.List.length vars))) with
| true -> begin
(failwith ("Impossible"))
end
| false -> begin
()
end)
in (let eqs = (let _65_22860 = (Support.List.map2 (fun ( v ) ( a ) -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _65_22857 = (let _65_22856 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_65_22856, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_22857))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(let _65_22859 = (let _65_22858 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_65_22858, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_22859))
end)) vars indices)
in (Support.Prims.pipe_right _65_22860 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _65_22865 = (let _65_22864 = (let _65_22863 = (let _65_22862 = (let _65_22861 = (mk_data_tester env l xx)
in (_65_22861, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _65_22862))
in (out, _65_22863))
in (Microsoft_FStar_ToSMT_Term.mkOr _65_22864))
in (_65_22865, (Support.List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_50_2216) with
| (data_ax, decls) -> begin
(let _50_2219 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2219) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _65_22866 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _65_22866 xx tapp))
in (let _65_22873 = (let _65_22872 = (let _65_22871 = (let _65_22870 = (let _65_22869 = (let _65_22868 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _65_22867 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _65_22868, _65_22867)))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22869))
in (_65_22870, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22871))
in (_65_22872)::[])
in (Support.List.append decls _65_22873)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _50_2231 = (match ((let _65_22874 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _65_22874.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, res)) -> begin
(true, bs, res)
end
| _ -> begin
(false, [], k)
end)
in (match (_50_2231) with
| (is_kind_arrow, formals, res) -> begin
(let _50_2238 = (encode_binders None formals env)
in (match (_50_2238) with
| (vars, guards, env', binder_decls, _) -> begin
(let projection_axioms = (fun ( tapp ) ( vars ) -> (match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.find_opt (fun ( _50_21 ) -> (match (_50_21) with
| Microsoft_FStar_Absyn_Syntax.Projector (_) -> begin
true
end
| _ -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inl (a)))) -> begin
(let rec projectee = (fun ( i ) ( _50_22 ) -> (match (_50_22) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
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
in (let _50_2277 = (match ((Support.Microsoft.FStar.Util.first_N projectee_pos vars)) with
| (_, xx::suffix) -> begin
(xx, suffix)
end
| _ -> begin
(failwith ("impossible"))
end)
in (match (_50_2277) with
| (xx, suffix) -> begin
(let dproj_app = (let _65_22888 = (let _65_22887 = (let _65_22886 = (mk_typ_projector_name d a)
in (let _65_22885 = (let _65_22884 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_65_22884)::[])
in (_65_22886, _65_22885)))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22887))
in (mk_ApplyT _65_22888 suffix))
in (let _65_22893 = (let _65_22892 = (let _65_22891 = (let _65_22890 = (let _65_22889 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _65_22889))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22890))
in (_65_22891, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22892))
in (_65_22893)::[]))
end))))
end
| _ -> begin
[]
end))
in (let pretype_axioms = (fun ( tapp ) ( vars ) -> (let _50_2286 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_50_2286) with
| (xxsym, xx) -> begin
(let _50_2289 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2289) with
| (ffsym, ff) -> begin
(let xx_has_type = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _65_22906 = (let _65_22905 = (let _65_22904 = (let _65_22903 = (let _65_22902 = (let _65_22901 = (let _65_22900 = (let _65_22899 = (let _65_22898 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _65_22898))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_22899))
in (xx_has_type, _65_22900))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22901))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _65_22902))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22903))
in (_65_22904, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22905))
in (_65_22906)::[]))
end))
end)))
in (let _50_2294 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2294) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _65_22908 = (let _65_22907 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _65_22907))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_22908))
in (let _50_2319 = (let tname_decl = (let _65_22912 = (let _65_22911 = (Support.Prims.pipe_right vars (Support.List.map (fun ( _50_2300 ) -> (match (_50_2300) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))))
in (let _65_22910 = (varops.next_id ())
in (tname, _65_22911, Microsoft_FStar_ToSMT_Term.Type_sort, _65_22910)))
in (constructor_or_logic_type_decl _65_22912))
in (let _50_2316 = (match (vars) with
| [] -> begin
(let _65_22916 = (let _65_22915 = (let _65_22914 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (Support.Prims.pipe_left (fun ( _65_22913 ) -> Some (_65_22913)) _65_22914))
in (push_free_tvar env t tname _65_22915))
in ([], _65_22916))
end
| _ -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _65_22917 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _65_22917))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match (((not (is_logical)) && (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _50_23 ) -> (match (_50_23) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _ -> begin
false
end)))))) with
| true -> begin
((ttok_app)::[])::((tapp)::[])::[]
end
| false -> begin
((ttok_app)::[])::[]
end)
in (let name_tok_corr = (let _65_22922 = (let _65_22921 = (let _65_22920 = (let _65_22919 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _65_22919))
in (Microsoft_FStar_ToSMT_Term.mkForall' _65_22920))
in (_65_22921, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22922))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_50_2316) with
| (tok_decls, env) -> begin
((Support.List.append tname_decl tok_decls), env)
end)))
in (match (_50_2319) with
| (decls, env) -> begin
(let kindingAx = (let _50_2322 = (encode_knd res env' tapp)
in (match (_50_2322) with
| (k, decls) -> begin
(let karr = (match (is_kind_arrow) with
| true -> begin
(let _65_22926 = (let _65_22925 = (let _65_22924 = (let _65_22923 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _65_22923))
in (_65_22924, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22925))
in (_65_22926)::[])
end
| false -> begin
[]
end)
in (let _65_22932 = (let _65_22931 = (let _65_22930 = (let _65_22929 = (let _65_22928 = (let _65_22927 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _65_22927))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22928))
in (_65_22929, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22930))
in (_65_22931)::[])
in (Support.List.append (Support.List.append decls karr) _65_22932)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _65_22933 = (projection_axioms tapp vars)
in (Support.List.append kindingAx _65_22933))
end
| false -> begin
(let _65_22940 = (let _65_22938 = (let _65_22936 = (let _65_22934 = (primitive_type_axioms t tname tapp)
in (Support.List.append kindingAx _65_22934))
in (let _65_22935 = (inversion_axioms tapp vars)
in (Support.List.append _65_22936 _65_22935)))
in (let _65_22937 = (projection_axioms tapp vars)
in (Support.List.append _65_22938 _65_22937)))
in (let _65_22939 = (pretype_axioms tapp vars)
in (Support.List.append _65_22940 _65_22939)))
end)
in (let g = (Support.List.append (Support.List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, _, _, _, _, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, t, _, quals, _, drange)) -> begin
(let _50_2353 = (new_term_constant_and_tok_from_lid env d)
in (match (_50_2353) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _50_2362 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(f, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_50_2362) with
| (formals, t_res) -> begin
(let _50_2365 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2365) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _50_2372 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_50_2372) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (Support.Prims.pipe_right names (Support.List.map (fun ( _50_24 ) -> (match (_50_24) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _65_22942 = (mk_typ_projector_name d a)
in (_65_22942, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _65_22943 = (mk_term_projector_name d x)
in (_65_22943, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _65_22945 = (let _65_22944 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _65_22944))
in (Support.Prims.pipe_right _65_22945 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _50_2386 = (encode_typ_pred' None t env ddtok_tm)
in (match (_50_2386) with
| (tok_typing, decls3) -> begin
(let _50_2393 = (encode_binders (Some (s_fuel_tm)) formals env)
in (match (_50_2393) with
| (vars', guards', env'', decls_formals, _) -> begin
(let _50_2398 = (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred' (Some (fuel_tm)) t_res env'' dapp)))
in (match (_50_2398) with
| (ty_pred', decls_pred) -> begin
(let guard' = (Microsoft_FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _ -> begin
(let _65_22947 = (let _65_22946 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _65_22946))
in (_65_22947)::[])
end)
in (let encode_elim = (fun ( _50_2405 ) -> (match (()) with
| () -> begin
(let _50_2408 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_50_2408) with
| (head, args) -> begin
(match ((let _65_22950 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _65_22950.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _50_2414 = (encode_args args env')
in (match (_50_2414) with
| (encoded_args, arg_decls) -> begin
(let _50_2438 = (Support.List.fold_left (fun ( _50_2418 ) ( arg ) -> (match (_50_2418) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _50_2426 = (let _65_22953 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _65_22953))
in (match (_50_2426) with
| (_, tv, env) -> begin
(let _65_22955 = (let _65_22954 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_65_22954)::eqns)
in (env, (tv)::arg_vars, _65_22955))
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _50_2433 = (let _65_22956 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _65_22956))
in (match (_50_2433) with
| (_, xv, env) -> begin
(let _65_22958 = (let _65_22957 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_65_22957)::eqns)
in (env, (xv)::arg_vars, _65_22958))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_50_2438) with
| (_, arg_vars, eqns) -> begin
(let arg_vars = (Support.List.rev arg_vars)
in (let ty = (Microsoft_FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (Support.List.map Microsoft_FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _65_22965 = (let _65_22964 = (let _65_22963 = (let _65_22962 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _65_22961 = (let _65_22960 = (let _65_22959 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards))
in (ty_pred, _65_22959))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22960))
in ((ty_pred)::[], _65_22962, _65_22961)))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22963))
in (_65_22964, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22965))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _65_22966 = (varops.fresh "x")
in (_65_22966, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _65_22975 = (let _65_22974 = (let _65_22973 = (let _65_22972 = (let _65_22967 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_65_22967)::[])
in (let _65_22971 = (let _65_22970 = (let _65_22969 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _65_22968 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_65_22969, _65_22968)))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22970))
in (_65_22972, (x)::[], _65_22971)))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22973))
in (_65_22974, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22975))))
end
| false -> begin
(let prec = (Support.Prims.pipe_right vars (Support.List.collect (fun ( v ) -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _65_22978 = (let _65_22977 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _65_22977 dapp))
in (_65_22978)::[])
end
| _ -> begin
(failwith ("unexpected sort"))
end))))
in (let _65_22985 = (let _65_22984 = (let _65_22983 = (let _65_22982 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _65_22981 = (let _65_22980 = (let _65_22979 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _65_22979))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_22980))
in ((ty_pred)::[], _65_22982, _65_22981)))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22983))
in (_65_22984, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_22985)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _ -> begin
(let _50_2458 = (let _65_22988 = (let _65_22987 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _65_22986 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" _65_22987 _65_22986)))
in (Microsoft_FStar_Tc_Errors.warn drange _65_22988))
in ([], []))
end)
end))
end))
in (let _50_2462 = (encode_elim ())
in (match (_50_2462) with
| (decls2, elim) -> begin
(let g = (let _65_23013 = (let _65_23012 = (let _65_22997 = (let _65_22996 = (let _65_22995 = (let _65_22994 = (let _65_22993 = (let _65_22992 = (let _65_22991 = (let _65_22990 = (let _65_22989 = (Microsoft_FStar_Absyn_Print.sli d)
in (Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" _65_22989))
in Some (_65_22990))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _65_22991))
in Microsoft_FStar_ToSMT_Term.DeclFun (_65_22992))
in (_65_22993)::[])
in (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) _65_22994))
in (Support.List.append _65_22995 proxy_fresh))
in (Support.List.append _65_22996 decls_formals))
in (Support.List.append _65_22997 decls_pred))
in (let _65_23011 = (let _65_23010 = (let _65_23009 = (let _65_23001 = (let _65_23000 = (let _65_22999 = (let _65_22998 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _65_22998))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_22999))
in (_65_23000, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23001))
in (let _65_23008 = (let _65_23007 = (let _65_23006 = (let _65_23005 = (let _65_23004 = (let _65_23003 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _65_23002 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _65_23003, _65_23002)))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23004))
in (_65_23005, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23006))
in (_65_23007)::[])
in (_65_23009)::_65_23008))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_65_23010)
in (Support.List.append _65_23012 _65_23011)))
in (Support.List.append _65_23013 elim))
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
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _, _, _)) -> begin
(let _50_2475 = (encode_signature env ses)
in (match (_50_2475) with
| (g, env) -> begin
(let _50_2487 = (Support.Prims.pipe_right g (Support.List.partition (fun ( _50_25 ) -> (match (_50_25) with
| Microsoft_FStar_ToSMT_Term.Assume ((_, Some ("inversion axiom"))) -> begin
false
end
| _ -> begin
true
end))))
in (match (_50_2487) with
| (g', inversions) -> begin
((Support.List.append g' inversions), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((is_rec, bindings), _, _, quals)) -> begin
(let eta_expand = (fun ( binders ) ( formals ) ( body ) ( t ) -> (let nbinders = (Support.List.length binders)
in (let _50_2506 = (Support.Microsoft.FStar.Util.first_N nbinders formals)
in (match (_50_2506) with
| (formals, extra_formals) -> begin
(let subst = (Support.List.map2 (fun ( formal ) ( binder ) -> (match (((Support.Prims.fst formal), (Support.Prims.fst binder))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _65_23026 = (let _65_23025 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _65_23025))
in Support.Microsoft.FStar.Util.Inl (_65_23026))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _65_23028 = (let _65_23027 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _65_23027))
in Support.Microsoft.FStar.Util.Inr (_65_23028))
end
| _ -> begin
(failwith ("Impossible"))
end)) formals binders)
in (let extra_formals = (let _65_23029 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (Support.Prims.pipe_right _65_23029 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _65_23035 = (let _65_23031 = (let _65_23030 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (Support.Prims.pipe_left Support.Prims.snd _65_23030))
in (body, _65_23031))
in (let _65_23034 = (let _65_23033 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (Support.Prims.pipe_left (fun ( _65_23032 ) -> Some (_65_23032)) _65_23033))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _65_23035 _65_23034 body.Microsoft_FStar_Absyn_Syntax.pos)))
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
(let _50_2558 = (Support.Microsoft.FStar.Util.first_N nformals binders)
in (match (_50_2558) with
| (bs0, rest) -> begin
(let tres = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tres)
end
| _ -> begin
(failwith ("impossible"))
end)
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end
| false -> begin
(match ((nformals > nbinders)) with
| true -> begin
(let _50_2567 = (eta_expand binders formals body tres)
in (match (_50_2567) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end
| false -> begin
(binders, body, formals, tres)
end)
end))))
end
| _ -> begin
(let _65_23044 = (let _65_23043 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _65_23042 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _65_23043 _65_23042)))
in (failwith (_65_23044)))
end)
end
| _ -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (let _50_2579 = (eta_expand [] formals e tres)
in (match (_50_2579) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _ -> begin
([], e, [], t_norm)
end)
end))
in (Support.Prims.try_with (fun ( _50_2583 ) -> (match (()) with
| () -> begin
(match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _50_26 ) -> (match (_50_26) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _ -> begin
false
end))))) with
| true -> begin
([], env)
end
| false -> begin
(match ((Support.Prims.pipe_right bindings (Support.Microsoft.FStar.Util.for_some (fun ( lb ) -> (Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp))))) with
| true -> begin
(let _65_23050 = (Support.Prims.pipe_right bindings (Support.List.collect (fun ( lb ) -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _65_23049 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _65_23049 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(raise (Let_rec_unencodeable))
end))))
in (_65_23050, env))
end
| false -> begin
(let _50_2614 = (Support.Prims.pipe_right bindings (Support.List.fold_left (fun ( _50_2601 ) ( lb ) -> (match (_50_2601) with
| (toks, typs, decls, env) -> begin
(let _50_2603 = (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(raise (Let_rec_unencodeable))
end
| false -> begin
()
end)
in (let t_norm = (let _65_23053 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.Prims.pipe_right _65_23053 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _50_2609 = (let _65_23054 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _65_23054 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_50_2609) with
| (tok, decl, env) -> begin
(let _65_23057 = (let _65_23056 = (let _65_23055 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_65_23055, tok))
in (_65_23056)::toks)
in (_65_23057, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_50_2614) with
| (toks, typs, decls, env) -> begin
(let toks = (Support.List.rev toks)
in (let decls = (Support.Prims.pipe_right (Support.List.rev decls) Support.List.flatten)
in (let typs = (Support.List.rev typs)
in (match (((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _50_27 ) -> (match (_50_27) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _ -> begin
false
end)))) || (Support.Prims.pipe_right typs (Support.Microsoft.FStar.Util.for_some (fun ( t ) -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (let _65_23060 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (Support.Prims.pipe_left Support.Prims.op_Negation _65_23060)))))))) with
| true -> begin
(decls, env)
end
| false -> begin
(match ((not (is_rec))) with
| true -> begin
(match ((bindings, typs, toks)) with
| ({Microsoft_FStar_Absyn_Syntax.lbname = _; Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _50_2645 = (destruct_bound_function flid t_norm e)
in (match (_50_2645) with
| (binders, body, formals, tres) -> begin
(let _50_2652 = (encode_binders None binders env)
in (match (_50_2652) with
| (vars, guards, env', binder_decls, _) -> begin
(let app = (match (vars) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _ -> begin
(let _65_23062 = (let _65_23061 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _65_23061))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_23062))
end)
in (let _50_2659 = (encode_exp body env')
in (match (_50_2659) with
| (body, decls2) -> begin
(let eqn = (let _65_23071 = (let _65_23070 = (let _65_23067 = (let _65_23066 = (let _65_23065 = (let _65_23064 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _65_23063 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_65_23064, _65_23063)))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_23065))
in ((app)::[], vars, _65_23066))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23067))
in (let _65_23069 = (let _65_23068 = (Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_65_23068))
in (_65_23070, _65_23069)))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23071))
in ((Support.List.append (Support.List.append (Support.List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _ -> begin
(failwith ("Impossible"))
end)
end
| false -> begin
(let fuel = (let _65_23072 = (varops.fresh "fuel")
in (_65_23072, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _50_2679 = (Support.Prims.pipe_right toks (Support.List.fold_left (fun ( _50_2668 ) ( _50_2673 ) -> (match ((_50_2668, _50_2673)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _65_23077 = (let _65_23076 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (Support.Prims.pipe_left (fun ( _65_23075 ) -> Some (_65_23075)) _65_23076))
in (push_free_var env flid gtok _65_23077))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_50_2679) with
| (gtoks, env) -> begin
(let gtoks = (Support.List.rev gtoks)
in (let encode_one_binding = (fun ( env0 ) ( _50_2688 ) ( t_norm ) ( _50_2697 ) -> (match ((_50_2688, _50_2697)) with
| ((flid, f, ftok, g, gtok), {Microsoft_FStar_Absyn_Syntax.lbname = _; Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _50_2702 = (destruct_bound_function flid t_norm e)
in (match (_50_2702) with
| (binders, body, formals, tres) -> begin
(let _50_2709 = (encode_binders None binders env)
in (match (_50_2709) with
| (vars, guards, env', binder_decls, _) -> begin
(let decl_g = (let _65_23088 = (let _65_23087 = (let _65_23086 = (Support.List.map Support.Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_65_23086)
in (g, _65_23087, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_65_23088))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _65_23091 = (let _65_23090 = (let _65_23089 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_65_23089)::vars_tm)
in (g, _65_23090))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_23091))
in (let gmax = (let _65_23094 = (let _65_23093 = (let _65_23092 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_65_23092)::vars_tm)
in (g, _65_23093))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_23094))
in (let _50_2719 = (encode_exp body env')
in (match (_50_2719) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _65_23103 = (let _65_23102 = (let _65_23099 = (let _65_23098 = (let _65_23097 = (let _65_23096 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _65_23095 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_65_23096, _65_23095)))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_23097))
in ((gsapp)::[], (fuel)::vars, _65_23098))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23099))
in (let _65_23101 = (let _65_23100 = (Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_65_23100))
in (_65_23102, _65_23101)))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23103))
in (let eqn_f = (let _65_23107 = (let _65_23106 = (let _65_23105 = (let _65_23104 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _65_23104))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23105))
in (_65_23106, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23107))
in (let eqn_g' = (let _65_23116 = (let _65_23115 = (let _65_23114 = (let _65_23113 = (let _65_23112 = (let _65_23111 = (let _65_23110 = (let _65_23109 = (let _65_23108 = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (_65_23108)::vars_tm)
in (g, _65_23109))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_23110))
in (gsapp, _65_23111))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_23112))
in ((gsapp)::[], (fuel)::vars, _65_23113))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23114))
in (_65_23115, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23116))
in (let _50_2742 = (let _50_2729 = (encode_binders None formals env0)
in (match (_50_2729) with
| (vars, v_guards, env, binder_decls, _) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _65_23117 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _65_23117 ((fuel)::vars)))
in (let _65_23121 = (let _65_23120 = (let _65_23119 = (let _65_23118 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _65_23118))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23119))
in (_65_23120, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23121)))
in (let _50_2739 = (let _50_2736 = (encode_typ_pred' None tres env gapp)
in (match (_50_2736) with
| (g_typing, d3) -> begin
(let _65_23129 = (let _65_23128 = (let _65_23127 = (let _65_23126 = (let _65_23125 = (let _65_23124 = (let _65_23123 = (let _65_23122 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_65_23122, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _65_23123))
in ((gapp)::[], (fuel)::vars, _65_23124))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23125))
in (_65_23126, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23127))
in (_65_23128)::[])
in (d3, _65_23129))
end))
in (match (_50_2739) with
| (aux_decls, typing_corr) -> begin
((Support.List.append binder_decls aux_decls), (Support.List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_50_2742) with
| (aux_decls, g_typing) -> begin
((Support.List.append (Support.List.append (Support.List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (Support.List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _50_2758 = (let _65_23132 = (Support.List.zip3 gtoks typs bindings)
in (Support.List.fold_left (fun ( _50_2746 ) ( _50_2750 ) -> (match ((_50_2746, _50_2750)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _50_2754 = (encode_one_binding env0 gtok ty bs)
in (match (_50_2754) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _65_23132))
in (match (_50_2758) with
| (decls, eqns, env0) -> begin
(let _50_2767 = (let _65_23134 = (Support.Prims.pipe_right decls Support.List.flatten)
in (Support.Prims.pipe_right _65_23134 (Support.List.partition (fun ( _50_28 ) -> (match (_50_28) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_) -> begin
true
end
| _ -> begin
false
end)))))
in (match (_50_2767) with
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
end)) (fun ( _50_2582 ) -> (match (_50_2582) with
| Let_rec_unencodeable -> begin
(let msg = (let _65_23137 = (Support.Prims.pipe_right bindings (Support.List.map (fun ( lb ) -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (Support.Prims.pipe_right _65_23137 (Support.String.concat " and ")))
in (let decl = Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun ( env ) ( x ) ( t ) ( t_norm ) -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _50_2794 = (encode_free_var env x t t_norm [])
in (match (_50_2794) with
| (decls, env) -> begin
(let _50_2799 = (lookup_lid env x)
in (match (_50_2799) with
| (n, x', _) -> begin
((n, x'), decls, env)
end))
end))
end
| Some ((n, x, _)) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun ( env ) ( lid ) ( t ) -> (let _50_2811 = (encode_function_type_as_formula None t env)
in (match (_50_2811) with
| (form, decls) -> begin
(Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume ((form, Some ((Support.String.strcat "Lemma: " lid.Microsoft_FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun ( env ) ( lid ) ( tt ) ( t_norm ) ( quals ) -> (match (((let _65_23150 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (Support.Prims.pipe_left Support.Prims.op_Negation _65_23150)) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm))) with
| true -> begin
(let _50_2820 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_2820) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _)) -> begin
(Support.Prims.pipe_right binders (Support.List.map (fun ( _50_29 ) -> (match (_50_29) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _ -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
end
| _ -> begin
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
in (let _50_2853 = (match ((Microsoft_FStar_Absyn_Util.function_formals t_norm)) with
| Some ((args, comp)) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _65_23152 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _65_23152))
end
| false -> begin
(args, (None, (Microsoft_FStar_Absyn_Util.comp_result comp)))
end)
end
| None -> begin
([], (None, t_norm))
end)
in (match (_50_2853) with
| (formals, (pre_opt, res_t)) -> begin
(let _50_2857 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_2857) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _ -> begin
(Microsoft_FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun ( vapp ) ( vars ) -> (Support.Prims.pipe_right quals (Support.List.collect (fun ( _50_30 ) -> (match (_50_30) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _50_2874 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_50_2874) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _65_23165 = (let _65_23164 = (let _65_23163 = (let _65_23162 = (let _65_23161 = (let _65_23160 = (let _65_23159 = (let _65_23158 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _65_23158))
in (vapp, _65_23159))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_23160))
in ((vapp)::[], vars, _65_23161))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23162))
in (_65_23163, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23164))
in (_65_23165)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _50_2887 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_50_2887) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _65_23174 = (let _65_23173 = (let _65_23172 = (let _65_23171 = (let _65_23170 = (let _65_23169 = (let _65_23168 = (let _65_23167 = (let _65_23166 = (mk_term_projector_name d f)
in (_65_23166, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_23167))
in (vapp, _65_23168))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_23169))
in ((vapp)::[], vars, _65_23170))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23171))
in (_65_23172, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23173))
in (_65_23174)::[]))
end))
end
| _ -> begin
[]
end)))))
in (let _50_2897 = (encode_binders None formals env)
in (match (_50_2897) with
| (vars, guards, env', decls1, _) -> begin
(let _50_2906 = (match (pre_opt) with
| None -> begin
(let _65_23175 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_65_23175, decls1))
end
| Some (p) -> begin
(let _50_2903 = (encode_formula p env')
in (match (_50_2903) with
| (g, ds) -> begin
(let _65_23176 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_65_23176, (Support.List.append decls1 ds)))
end))
end)
in (match (_50_2906) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _65_23178 = (let _65_23177 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _65_23177))
in (Microsoft_FStar_ToSMT_Term.mkApp _65_23178))
in (let _50_2937 = (let vname_decl = (let _65_23181 = (let _65_23180 = (Support.Prims.pipe_right formals (Support.List.map (fun ( _50_31 ) -> (match (_50_31) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _ -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _65_23180, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_65_23181))
in (let _50_2924 = (let env = (let _50_2919 = env
in {bindings = _50_2919.bindings; depth = _50_2919.depth; tcenv = _50_2919.tcenv; warn = _50_2919.warn; cache = _50_2919.cache; nolabels = _50_2919.nolabels; use_zfuel_name = _50_2919.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((not ((head_normal env tt)))) with
| true -> begin
(encode_typ_pred' None tt env vtok_tm)
end
| false -> begin
(encode_typ_pred' None t_norm env vtok_tm)
end))
in (match (_50_2924) with
| (tok_typing, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _50_2934 = (match (formals) with
| [] -> begin
(let _65_23185 = (let _65_23184 = (let _65_23183 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Support.Prims.pipe_left (fun ( _65_23182 ) -> Some (_65_23182)) _65_23183))
in (push_free_var env lid vname _65_23184))
in ((Support.List.append decls2 ((tok_typing)::[])), _65_23185))
end
| _ -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _65_23186 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _65_23186))
in (let name_tok_corr = (let _65_23190 = (let _65_23189 = (let _65_23188 = (let _65_23187 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _65_23187))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23188))
in (_65_23189, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23190))
in ((Support.List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_50_2934) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_50_2937) with
| (decls2, env) -> begin
(let _50_2940 = (encode_typ_pred' None res_t env' vapp)
in (match (_50_2940) with
| (ty_pred, decls3) -> begin
(let typingAx = (let _65_23194 = (let _65_23193 = (let _65_23192 = (let _65_23191 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _65_23191))
in (Microsoft_FStar_ToSMT_Term.mkForall _65_23192))
in (_65_23193, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23194))
in (let g = (let _65_23196 = (let _65_23195 = (mk_disc_proj_axioms vapp vars)
in (typingAx)::_65_23195)
in (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) _65_23196))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end)
end))
and encode_signature = (fun ( env ) ( ses ) -> (Support.Prims.pipe_right ses (Support.List.fold_left (fun ( _50_2947 ) ( se ) -> (match (_50_2947) with
| (g, env) -> begin
(let _50_2951 = (encode_sigelt env se)
in (match (_50_2951) with
| (g', env) -> begin
((Support.List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun ( env ) ( bindings ) -> (let encode_binding = (fun ( b ) ( _50_2958 ) -> (match (_50_2958) with
| (decls, env) -> begin
(match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t0)) -> begin
(let _50_2966 = (new_term_constant env x)
in (match (_50_2966) with
| (xxsym, xx, env') -> begin
(let t1 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _50_2970 = (encode_typ_pred' None t1 env xx)
in (match (_50_2970) with
| (t, decls') -> begin
(let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _65_23212 = (let _65_23211 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _65_23210 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _65_23209 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" _65_23211 _65_23210 _65_23209))))
in Some (_65_23212))
end
| false -> begin
None
end)
in (let g = (Support.List.append (Support.List.append ((Microsoft_FStar_ToSMT_Term.DeclFun ((xxsym, [], Microsoft_FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((Microsoft_FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((Support.List.append decls g), env')))
end)))
end))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let _50_2980 = (new_typ_constant env a)
in (match (_50_2980) with
| (aasym, aa, env') -> begin
(let _50_2983 = (encode_knd k env aa)
in (match (_50_2983) with
| (k, decls') -> begin
(let g = (let _65_23218 = (let _65_23217 = (let _65_23216 = (let _65_23215 = (let _65_23214 = (let _65_23213 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_65_23213))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _65_23214))
in Microsoft_FStar_ToSMT_Term.DeclFun (_65_23215))
in (_65_23216)::[])
in (Support.List.append _65_23217 decls'))
in (Support.List.append _65_23218 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((Support.List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((x, t)) -> begin
(let t_norm = (whnf env t)
in (let _50_2992 = (encode_free_var env x t t_norm [])
in (match (_50_2992) with
| (g, env') -> begin
((Support.List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _50_2997 = (encode_sigelt env se)
in (match (_50_2997) with
| (g, env') -> begin
((Support.List.append decls g), env')
end))
end)
end))
in (Support.List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun ( labs ) -> (let prefix = (Support.Prims.pipe_right labs (Support.List.map (fun ( _50_3004 ) -> (match (_50_3004) with
| (l, _, _) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Support.Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (Support.Prims.pipe_right labs (Support.List.collect (fun ( _50_3011 ) -> (match (_50_3011) with
| (l, _, _) -> begin
(let _65_23226 = (Support.Prims.pipe_left (fun ( _65_23222 ) -> Microsoft_FStar_ToSMT_Term.Echo (_65_23222)) (Support.Prims.fst l))
in (let _65_23225 = (let _65_23224 = (let _65_23223 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_65_23223))
in (_65_23224)::[])
in (_65_23226)::_65_23225))
end))))
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun ( tcenv ) -> (let _65_23231 = (let _65_23230 = (let _65_23229 = (Support.Microsoft.FStar.Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _65_23229; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_65_23230)::[])
in (Support.ST.op_Colon_Equals last_env _65_23231)))

let get_env = (fun ( tcenv ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(failwith ("No env; call init first!"))
end
| e::_ -> begin
(let _50_3020 = e
in {bindings = _50_3020.bindings; depth = _50_3020.depth; tcenv = tcenv; warn = _50_3020.warn; cache = _50_3020.cache; nolabels = _50_3020.nolabels; use_zfuel_name = _50_3020.use_zfuel_name; encode_non_total_function_typ = _50_3020.encode_non_total_function_typ})
end))

let set_env = (fun ( env ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(failwith ("Empty env stack"))
end
| _::tl -> begin
(Support.ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun ( _50_3028 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(failwith ("Empty env stack"))
end
| hd::tl -> begin
(let _50_3033 = (Microsoft_FStar_ToSMT_Term.push ())
in (let refs = (Support.Microsoft.FStar.Util.smap_copy hd.cache)
in (let top = (let _50_3036 = hd
in {bindings = _50_3036.bindings; depth = _50_3036.depth; tcenv = _50_3036.tcenv; warn = _50_3036.warn; cache = refs; nolabels = _50_3036.nolabels; use_zfuel_name = _50_3036.use_zfuel_name; encode_non_total_function_typ = _50_3036.encode_non_total_function_typ})
in (Support.ST.op_Colon_Equals last_env ((top)::(hd)::tl)))))
end)
end))

let pop_env = (fun ( _50_3039 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(failwith ("Popping an empty stack"))
end
| _::tl -> begin
(let _50_3045 = (Microsoft_FStar_ToSMT_Term.pop ())
in (Support.ST.op_Colon_Equals last_env tl))
end)
end))

let mark_env = (fun ( _50_3047 ) -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun ( _50_3048 ) -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun ( _50_3049 ) -> (match (()) with
| () -> begin
(let _50_3050 = (Microsoft_FStar_ToSMT_Term.commit_mark ())
in (match ((Support.ST.read last_env)) with
| hd::_::tl -> begin
(Support.ST.op_Colon_Equals last_env ((hd)::tl))
end
| _ -> begin
(failwith ("Impossible"))
end))
end))

let init = (fun ( tcenv ) -> (let _50_3061 = (init_env tcenv)
in (let _50_3063 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun ( msg ) -> (let _50_3066 = (push_env ())
in (let _50_3068 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun ( msg ) -> (let _50_3071 = (let _65_23252 = (pop_env ())
in (Support.Prims.pipe_left Support.Prims.ignore _65_23252))
in (let _50_3073 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun ( msg ) -> (let _50_3076 = (mark_env ())
in (let _50_3078 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun ( msg ) -> (let _50_3081 = (reset_mark_env ())
in (let _50_3083 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun ( msg ) -> (let _50_3086 = (commit_mark_env ())
in (let _50_3088 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun ( tcenv ) ( se ) -> (let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _65_23266 = (let _65_23265 = (let _65_23264 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.String.strcat "encoding sigelt " _65_23264))
in Microsoft_FStar_ToSMT_Term.Caption (_65_23265))
in (_65_23266)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _50_3097 = (encode_sigelt env se)
in (match (_50_3097) with
| (decls, env) -> begin
(let _50_3098 = (set_env env)
in (let _65_23267 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _65_23267)))
end)))))

let encode_modul = (fun ( tcenv ) ( modul ) -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _50_3103 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _65_23272 = (Support.Prims.pipe_right (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name _65_23272))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _50_3110 = (encode_signature (let _50_3106 = env
in {bindings = _50_3106.bindings; depth = _50_3106.depth; tcenv = _50_3106.tcenv; warn = false; cache = _50_3106.cache; nolabels = _50_3106.nolabels; use_zfuel_name = _50_3106.use_zfuel_name; encode_non_total_function_typ = _50_3106.encode_non_total_function_typ}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_50_3110) with
| (decls, env) -> begin
(let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let msg = (Support.String.strcat "Externals for " name)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _50_3116 = (set_env (let _50_3114 = env
in {bindings = _50_3114.bindings; depth = _50_3114.depth; tcenv = _50_3114.tcenv; warn = true; cache = _50_3114.cache; nolabels = _50_3114.nolabels; use_zfuel_name = _50_3114.use_zfuel_name; encode_non_total_function_typ = _50_3114.encode_non_total_function_typ}))
in (let _50_3118 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun ( tcenv ) ( q ) -> (let _50_3123 = (let _65_23281 = (let _65_23280 = (let _65_23279 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _65_23279))
in (Support.Microsoft.FStar.Util.format1 "Starting query at %s" _65_23280))
in (push _65_23281))
in (let pop = (fun ( _50_3126 ) -> (match (()) with
| () -> begin
(let _65_23286 = (let _65_23285 = (let _65_23284 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _65_23284))
in (Support.Microsoft.FStar.Util.format1 "Ending query at %s" _65_23285))
in (pop _65_23286))
end))
in (let _50_3156 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun ( bs ) ( b ) -> (b)::bs) [])
in (let _50_3139 = (let _65_23290 = (Support.List.filter (fun ( _50_32 ) -> (match (_50_32) with
| Microsoft_FStar_Tc_Env.Binding_sig (_) -> begin
false
end
| _ -> begin
true
end)) bindings)
in (encode_env_bindings env _65_23290))
in (match (_50_3139) with
| (env_decls, env) -> begin
(let _50_3140 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _65_23291 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" _65_23291))
end
| false -> begin
()
end)
in (let _50_3145 = (encode_formula_with_labels q env)
in (match (_50_3145) with
| (phi, labels, qdecls) -> begin
(let _50_3148 = (encode_labels labels)
in (match (_50_3148) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Support.List.append (Support.List.append env_decls label_prefix) qdecls)
in (let qry = (let _65_23293 = (let _65_23292 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_65_23292, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23293))
in (let suffix = (Support.List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_50_3156) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume (({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.False, _)); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}, _)) -> begin
()
end
| _ when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
()
end
| Microsoft_FStar_ToSMT_Term.Assume ((q, _)) -> begin
(let fresh = ((Support.String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _50_3183 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun ( p ) ( _50_3189 ) -> (match (_50_3189) with
| (n, i) -> begin
(let _65_23315 = (let _65_23314 = (let _65_23299 = (let _65_23298 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" _65_23298))
in Microsoft_FStar_ToSMT_Term.Caption (_65_23299))
in (let _65_23313 = (let _65_23312 = (let _65_23304 = (let _65_23303 = (let _65_23302 = (let _65_23301 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _65_23300 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_65_23301, _65_23300)))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_23302))
in (_65_23303, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23304))
in (let _65_23311 = (let _65_23310 = (let _65_23309 = (let _65_23308 = (let _65_23307 = (let _65_23306 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _65_23305 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_65_23306, _65_23305)))
in (Microsoft_FStar_ToSMT_Term.mkEq _65_23307))
in (_65_23308, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_23309))
in (_65_23310)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_65_23312)::_65_23311))
in (_65_23314)::_65_23313))
in (Support.List.append _65_23315 suffix))
end))
in (let check = (fun ( p ) -> (let initial_config = (let _65_23319 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _65_23318 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_65_23319, _65_23318)))
in (let alt_configs = (let _65_23338 = (let _65_23337 = (match (((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel))) with
| true -> begin
(let _65_23322 = (let _65_23321 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _65_23320 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_65_23321, _65_23320)))
in (_65_23322)::[])
end
| false -> begin
[]
end)
in (let _65_23336 = (let _65_23335 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2) > (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _65_23325 = (let _65_23324 = ((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2)
in (let _65_23323 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_65_23324, _65_23323)))
in (_65_23325)::[])
end
| false -> begin
[]
end)
in (let _65_23334 = (let _65_23333 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) > (Support.ST.read Microsoft_FStar_Options.initial_fuel)) && ((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel)))) with
| true -> begin
(let _65_23328 = (let _65_23327 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _65_23326 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_65_23327, _65_23326)))
in (_65_23328)::[])
end
| false -> begin
[]
end)
in (let _65_23332 = (let _65_23331 = (match (((Support.ST.read Microsoft_FStar_Options.min_fuel) < (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _65_23330 = (let _65_23329 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (_65_23329, 1))
in (_65_23330)::[])
end
| false -> begin
[]
end)
in (_65_23331)::[])
in (_65_23333)::_65_23332))
in (_65_23335)::_65_23334))
in (_65_23337)::_65_23336))
in (Support.List.flatten _65_23338))
in (let report = (fun ( _50_3197 ) -> (match (_50_3197) with
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
| _ -> begin
errs
end)
in (Microsoft_FStar_Tc_Errors.add_errors tcenv errs))
end)
end))
in (let rec try_alt_configs = (fun ( p ) ( errs ) ( _50_33 ) -> (match (_50_33) with
| [] -> begin
(report (false, errs))
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _65_23350 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _65_23350 (cb p [])))
end
| _ -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(let _65_23352 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _65_23352 (fun ( _50_3218 ) -> (match (_50_3218) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb p tl (ok, errs'))
end
| _ -> begin
(cb p tl (ok, errs))
end)
end))))
end))
and cb = (fun ( p ) ( alt ) ( _50_3226 ) -> (match (_50_3226) with
| (ok, errs) -> begin
(match (ok) with
| true -> begin
()
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _65_23356 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _65_23356 (cb p alt_configs))))))))
in (let process_query = (fun ( q ) -> (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let _50_3231 = (let _65_23362 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _65_23362 q))
in (match (_50_3231) with
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
in (let _50_3232 = (match ((Support.ST.read Microsoft_FStar_Options.admit_smt_queries)) with
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
in (let _50_3237 = (push "query")
in (let _50_3244 = (encode_formula_with_labels q env)
in (match (_50_3244) with
| (f, _, _) -> begin
(let _50_3245 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _)) -> begin
true
end
| _ -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = commit_mark; Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun ( _50_3254 ) -> ()); Microsoft_FStar_Tc_Env.push = (fun ( _50_3256 ) -> ()); Microsoft_FStar_Tc_Env.pop = (fun ( _50_3258 ) -> ()); Microsoft_FStar_Tc_Env.mark = (fun ( _50_3260 ) -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun ( _50_3262 ) -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun ( _50_3264 ) -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun ( _50_3266 ) ( _50_3268 ) -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun ( _50_3270 ) ( _50_3272 ) -> ()); Microsoft_FStar_Tc_Env.solve = (fun ( _50_3274 ) ( _50_3276 ) -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun ( _50_3278 ) ( _50_3280 ) -> false); Microsoft_FStar_Tc_Env.finish = (fun ( _50_3282 ) -> ()); Microsoft_FStar_Tc_Env.refresh = (fun ( _50_3283 ) -> ())}





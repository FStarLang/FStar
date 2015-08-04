
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

let mk_typ_projector_name = (fun ( lid ) ( a ) -> (let _68_21255 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.Prims.pipe_left escape _68_21255)))

let mk_term_projector_name = (fun ( lid ) ( a ) -> (let a = (let _68_21260 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _68_21260; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _68_21261 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.Prims.pipe_left escape _68_21261))))

let primitive_projector_by_pos = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _50_61 ) -> (match (()) with
| () -> begin
(let _68_21271 = (let _68_21270 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" _68_21270 lid.Microsoft_FStar_Absyn_Syntax.str))
in (failwith (_68_21271)))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _68_21272 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_21272.Microsoft_FStar_Absyn_Syntax.n)) with
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

let mk_term_projector_name_by_pos = (fun ( lid ) ( i ) -> (let _68_21278 = (let _68_21277 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _68_21277))
in (Support.Prims.pipe_left escape _68_21278)))

let mk_typ_projector = (fun ( lid ) ( a ) -> (let _68_21284 = (let _68_21283 = (mk_typ_projector_name lid a)
in (_68_21283, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _68_21284)))

let mk_term_projector = (fun ( lid ) ( a ) -> (let _68_21290 = (let _68_21289 = (mk_term_projector_name lid a)
in (_68_21289, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _68_21290)))

let mk_term_projector_by_pos = (fun ( lid ) ( i ) -> (let _68_21296 = (let _68_21295 = (mk_term_projector_name_by_pos lid i)
in (_68_21295, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _68_21296)))

let mk_data_tester = (fun ( env ) ( l ) ( x ) -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let is_Mkvarops_t = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkvarops_t")))

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun ( _50_100 ) -> (match (()) with
| () -> begin
(let _68_21400 = (Support.Microsoft.FStar.Util.smap_create 100)
in (let _68_21399 = (Support.Microsoft.FStar.Util.smap_create 100)
in (_68_21400, _68_21399)))
end))
in (let scopes = (let _68_21402 = (let _68_21401 = (new_scope ())
in (_68_21401)::[])
in (Support.Microsoft.FStar.Util.mk_ref _68_21402))
in (let mk_unique = (fun ( y ) -> (let y = (escape y)
in (let y = (match ((let _68_21406 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _68_21406 (fun ( _50_108 ) -> (match (_50_108) with
| (names, _) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_) -> begin
(let _50_113 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _68_21408 = (let _68_21407 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _68_21407))
in (Support.String.strcat (Support.String.strcat y "__") _68_21408)))
end)
in (let top_scope = (let _68_21410 = (let _68_21409 = (Support.ST.read scopes)
in (Support.List.hd _68_21409))
in (Support.Prims.pipe_left Support.Prims.fst _68_21410))
in (let _50_117 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun ( pp ) ( rn ) -> (let _68_21416 = (let _68_21415 = (Support.Prims.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.String.strcat _68_21415 "__"))
in (Support.String.strcat _68_21416 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun ( lid ) -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun ( _50_125 ) -> (match (()) with
| () -> begin
(let _50_126 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
end))
in (let fresh = (fun ( pfx ) -> (let _68_21424 = (let _68_21423 = (next_id ())
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int _68_21423))
in (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx _68_21424)))
in (let string_const = (fun ( s ) -> (match ((let _68_21428 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _68_21428 (fun ( _50_135 ) -> (match (_50_135) with
| (_, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _68_21429 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxString _68_21429))
in (let top_scope = (let _68_21431 = (let _68_21430 = (Support.ST.read scopes)
in (Support.List.hd _68_21430))
in (Support.Prims.pipe_left Support.Prims.snd _68_21431))
in (let _50_142 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun ( _50_145 ) -> (match (()) with
| () -> begin
(let _68_21436 = (let _68_21435 = (new_scope ())
in (let _68_21434 = (Support.ST.read scopes)
in (_68_21435)::_68_21434))
in (Support.ST.op_Colon_Equals scopes _68_21436))
end))
in (let pop = (fun ( _50_147 ) -> (match (()) with
| () -> begin
(let _68_21440 = (let _68_21439 = (Support.ST.read scopes)
in (Support.List.tl _68_21439))
in (Support.ST.op_Colon_Equals scopes _68_21440))
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

let unmangle = (fun ( x ) -> (let _68_21456 = (let _68_21455 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _68_21454 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_68_21455, _68_21454)))
in (Microsoft_FStar_Absyn_Util.mkbvd _68_21456)))

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

let is_Mkenv_t = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkenv_t")))

let print_env = (fun ( e ) -> (let _68_21514 = (Support.Prims.pipe_right e.bindings (Support.List.map (fun ( _50_2 ) -> (match (_50_2) with
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
in (Support.Prims.pipe_right _68_21514 (Support.String.concat ", "))))

let lookup_binding = (fun ( env ) ( f ) -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun ( env ) ( t ) -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_21524 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_68_21524))
end
| false -> begin
None
end))

let fresh_fvar = (fun ( x ) ( s ) -> (let xsym = (varops.fresh x)
in (let _68_21529 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _68_21529))))

let gen_term_var = (fun ( env ) ( x ) -> (let ysym = (let _68_21534 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@x" _68_21534))
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
(let _68_21549 = (let _68_21548 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" _68_21548))
in (failwith (_68_21549)))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun ( env ) ( x ) -> (let ysym = (let _68_21554 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@a" _68_21554))
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
(let _68_21569 = (let _68_21568 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" _68_21568))
in (failwith (_68_21569)))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _68_21580 = (let _50_290 = env
in (let _68_21579 = (let _68_21578 = (let _68_21577 = (let _68_21576 = (let _68_21575 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.Prims.pipe_left (fun ( _68_21574 ) -> Some (_68_21574)) _68_21575))
in (x, fname, _68_21576, None))
in Binding_fvar (_68_21577))
in (_68_21578)::env.bindings)
in {bindings = _68_21579; depth = _50_290.depth; tcenv = _50_290.tcenv; warn = _50_290.warn; cache = _50_290.cache; nolabels = _50_290.nolabels; use_zfuel_name = _50_290.use_zfuel_name; encode_non_total_function_typ = _50_290.encode_non_total_function_typ}))
in (fname, ftok, _68_21580)))))

let try_lookup_lid = (fun ( env ) ( a ) -> (lookup_binding env (fun ( _50_5 ) -> (match (_50_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _ -> begin
None
end))))

let lookup_lid = (fun ( env ) ( a ) -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _68_21591 = (let _68_21590 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _68_21590))
in (failwith (_68_21591)))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _50_312 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _50_312.depth; tcenv = _50_312.tcenv; warn = _50_312.warn; cache = _50_312.cache; nolabels = _50_312.nolabels; use_zfuel_name = _50_312.use_zfuel_name; encode_non_total_function_typ = _50_312.encode_non_total_function_typ}))

let push_zfuel_name = (fun ( env ) ( x ) ( f ) -> (let _50_321 = (lookup_lid env x)
in (match (_50_321) with
| (t1, t2, _) -> begin
(let t3 = (let _68_21608 = (let _68_21607 = (let _68_21606 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_68_21606)::[])
in (f, _68_21607))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21608))
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
(match ((let _68_21612 = (let _68_21611 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (Support.Prims.pipe_right _68_21611 Support.Prims.fst))
in (Support.Microsoft.FStar.Util.starts_with _68_21612 "fuel"))) with
| true -> begin
(let _68_21613 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _68_21613 fuel))
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
(let _68_21615 = (let _68_21614 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _68_21614))
in (failwith (_68_21615)))
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
in (let _68_21630 = (let _50_387 = env
in (let _68_21629 = (let _68_21628 = (let _68_21627 = (let _68_21626 = (let _68_21625 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.Prims.pipe_left (fun ( _68_21624 ) -> Some (_68_21624)) _68_21625))
in (x, fname, _68_21626))
in Binding_ftvar (_68_21627))
in (_68_21628)::env.bindings)
in {bindings = _68_21629; depth = _50_387.depth; tcenv = _50_387.tcenv; warn = _50_387.warn; cache = _50_387.cache; nolabels = _50_387.nolabels; use_zfuel_name = _50_387.use_zfuel_name; encode_non_total_function_typ = _50_387.encode_non_total_function_typ}))
in (fname, ftok, _68_21630)))))

let lookup_tlid = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _50_6 ) -> (match (_50_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _ -> begin
None
end)))) with
| None -> begin
(let _68_21637 = (let _68_21636 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _68_21636))
in (failwith (_68_21637)))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _50_406 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _50_406.depth; tcenv = _50_406.tcenv; warn = _50_406.warn; cache = _50_406.cache; nolabels = _50_406.nolabels; use_zfuel_name = _50_406.use_zfuel_name; encode_non_total_function_typ = _50_406.encode_non_total_function_typ}))

let lookup_free_tvar = (fun ( env ) ( a ) -> (match ((let _68_21648 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _68_21648 Support.Prims.snd))) with
| None -> begin
(let _68_21650 = (let _68_21649 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _68_21649))
in (failwith (_68_21650)))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun ( env ) ( a ) -> (let _68_21653 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _68_21653 Support.Prims.fst)))

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
(let _68_21669 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _68_21669 Support.Option.isNone))
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

let trivial_post = (fun ( t ) -> (let _68_21691 = (let _68_21690 = (let _68_21688 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_68_21688)::[])
in (let _68_21689 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_68_21690, _68_21689)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _68_21691 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun ( e ) ( vars ) -> (Support.Prims.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _68_21698 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _68_21698))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _68_21699 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _68_21699))
end
| _ -> begin
(let _68_21700 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _68_21700))
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
(let _68_21713 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _68_21713))
end
| _ -> begin
(let _68_21714 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _68_21714))
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

let is_Mkpattern = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkpattern")))

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
(let _68_21770 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _68_21770))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _68_21771 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _68_21771))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _68_21772 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _68_21772))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _68_21776 = (let _68_21775 = (let _68_21774 = (let _68_21773 = (Microsoft_FStar_ToSMT_Term.mkInteger' i)
in (Microsoft_FStar_ToSMT_Term.boxInt _68_21773))
in (_68_21774)::[])
in ("Int32.Int32", _68_21775))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21776))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _)) -> begin
(let _68_21777 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_bytes bytes)
in (varops.string_const _68_21777))
end
| c -> begin
(let _68_21779 = (let _68_21778 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" _68_21778))
in (failwith (_68_21779)))
end))

let as_function_typ = (fun ( env ) ( t0 ) -> (let rec aux = (fun ( norm ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
(let _68_21788 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _68_21788))
end
| _ -> begin
(match (norm) with
| true -> begin
(let _68_21789 = (whnf env t)
in (aux false _68_21789))
end
| false -> begin
(let _68_21792 = (let _68_21791 = (Support.Microsoft.FStar.Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_21790 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Support.Microsoft.FStar.Util.format2 "(%s) Expected a function typ; got %s" _68_21791 _68_21790)))
in (failwith (_68_21792)))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun ( k ) ( env ) -> (match ((let _68_21824 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _68_21824.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k0)) -> begin
(let _50_630 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _68_21826 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _68_21825 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _68_21826 _68_21825)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _)) -> begin
(let _68_21828 = (let _68_21827 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _68_21827))
in (_68_21828, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, kbody)) -> begin
(let tsym = (let _68_21829 = (varops.fresh "t")
in (_68_21829, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let t = (Microsoft_FStar_ToSMT_Term.mkFreeV tsym)
in (let _50_649 = (encode_binders None bs env)
in (match (_50_649) with
| (vars, guards, env', decls, _) -> begin
(let app = (mk_ApplyT t vars)
in (let _50_653 = (encode_knd kbody env' app)
in (match (_50_653) with
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
| _ -> begin
(let _68_21838 = (let _68_21837 = (let _68_21836 = (Microsoft_FStar_ToSMT_Term.mk_PreKind app)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _68_21836))
in (_68_21837, body))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21838))
end)
in (let _68_21840 = (let _68_21839 = (Microsoft_FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _68_21839))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_21840)))))
end
| _ -> begin
(failwith ("Impossible: vars and guards are in 1-1 correspondence"))
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _68_21842 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (Support.Prims.pipe_right _68_21842 (Support.List.filter (fun ( _50_680 ) -> (match (_50_680) with
| (x, _) -> begin
(x <> (Support.Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((k', sorts, _)) -> begin
(let _68_21845 = (let _68_21844 = (let _68_21843 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _68_21843))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21844))
in (_68_21845, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _68_21846 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_68_21846))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _68_21848 = (let _68_21847 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _68_21847))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21848))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _68_21857 = (let _68_21856 = (let _68_21855 = (let _68_21854 = (let _68_21853 = (let _68_21852 = (let _68_21851 = (let _68_21850 = (let _68_21849 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _68_21849))
in (_68_21850, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21851))
in (t_has_k, _68_21852))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_21853))
in ((t_has_k)::[], (tsym)::cvars, _68_21854))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_21855))
in (_68_21856, Some ((Support.String.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21857))
in (let k_decls = (Support.List.append (Support.List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _50_698 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _ -> begin
(let _68_21859 = (let _68_21858 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" _68_21858))
in (failwith (_68_21859)))
end))
and encode_knd = (fun ( k ) ( env ) ( t ) -> (let _50_707 = (encode_knd_term k env)
in (match (_50_707) with
| (k, decls) -> begin
(let _68_21863 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_68_21863, decls))
end)))
and encode_binders = (fun ( fuel_opt ) ( bs ) ( env ) -> (let _50_711 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_21867 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" _68_21867))
end
| false -> begin
()
end)
in (let _50_761 = (Support.Prims.pipe_right bs (Support.List.fold_left (fun ( _50_718 ) ( b ) -> (match (_50_718) with
| (vars, guards, env, decls, names) -> begin
(let _50_755 = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = a; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _}) -> begin
(let a = (unmangle a)
in (let _50_730 = (gen_typ_var env a)
in (match (_50_730) with
| (aasym, aa, env') -> begin
(let _50_731 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _68_21871 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _68_21870 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _68_21871 aasym _68_21870)))
end
| false -> begin
()
end)
in (let _50_735 = (encode_knd k env aa)
in (match (_50_735) with
| (guard_a_k, decls') -> begin
((aasym, Microsoft_FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', Support.Microsoft.FStar.Util.Inl (a))
end)))
end)))
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _}) -> begin
(let x = (unmangle x)
in (let _50_746 = (gen_term_var env x)
in (match (_50_746) with
| (xxsym, xx, env') -> begin
(let _50_749 = (let _68_21872 = (norm_t env t)
in (encode_typ_pred' fuel_opt _68_21872 env xx))
in (match (_50_749) with
| (guard_x_t, decls') -> begin
((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', Support.Microsoft.FStar.Util.Inr (x))
end))
end)))
end)
in (match (_50_755) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (Support.List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_50_761) with
| (vars, guards, env, decls, names) -> begin
((Support.List.rev vars), (Support.List.rev guards), env, decls, (Support.List.rev names))
end))))
and encode_typ_pred' = (fun ( fuel_opt ) ( t ) ( env ) ( e ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _50_769 = (encode_typ_term t env)
in (match (_50_769) with
| (t, decls) -> begin
(let _68_21877 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_68_21877, decls))
end))))
and encode_typ_term = (fun ( t ) ( env ) -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _68_21880 = (lookup_typ_var env a)
in (_68_21880, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _68_21881 = (lookup_free_tvar env fv)
in (_68_21881, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
(match (((env.encode_non_total_function_typ && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _50_787 = (encode_binders None binders env)
in (match (_50_787) with
| (vars, guards, env', decls, _) -> begin
(let fsym = (let _68_21882 = (varops.fresh "f")
in (_68_21882, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _50_793 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_50_793) with
| (pre_opt, res_t) -> begin
(let _50_796 = (encode_typ_pred' None res_t env' app)
in (match (_50_796) with
| (res_pred, decls') -> begin
(let _50_805 = (match (pre_opt) with
| None -> begin
(let _68_21883 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_68_21883, decls))
end
| Some (pre) -> begin
(let _50_802 = (encode_formula pre env')
in (match (_50_802) with
| (guard, decls0) -> begin
(let _68_21884 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_68_21884, (Support.List.append decls decls0)))
end))
end)
in (match (_50_805) with
| (guards, guard_decls) -> begin
(let t_interp = (let _68_21886 = (let _68_21885 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _68_21885))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_21886))
in (let cvars = (let _68_21888 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (Support.Prims.pipe_right _68_21888 (Support.List.filter (fun ( _50_810 ) -> (match (_50_810) with
| (x, _) -> begin
(x <> (Support.Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _)) -> begin
(let _68_21891 = (let _68_21890 = (let _68_21889 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _68_21889))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21890))
in (_68_21891, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _68_21892 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_68_21892))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _68_21894 = (let _68_21893 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _68_21893))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21894))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _68_21896 = (let _68_21895 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_68_21895, Some ((Support.String.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21896))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let pre_typing = (let _68_21903 = (let _68_21902 = (let _68_21901 = (let _68_21900 = (let _68_21899 = (let _68_21898 = (let _68_21897 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _68_21897))
in (f_has_t, _68_21898))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_21899))
in ((f_has_t)::[], (fsym)::cvars, _68_21900))
in (mkForall_fuel _68_21901))
in (_68_21902, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21903))
in (let t_interp = (let _68_21907 = (let _68_21906 = (let _68_21905 = (let _68_21904 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t, t_interp))
in ((f_has_t)::[], (fsym)::cvars, _68_21904))
in (mkForall_fuel _68_21905))
in (_68_21906, Some ((Support.String.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21907))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _50_831 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
in (let t_kinding = (let _68_21909 = (let _68_21908 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_68_21908, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21909))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _68_21916 = (let _68_21915 = (let _68_21914 = (let _68_21913 = (let _68_21912 = (let _68_21911 = (let _68_21910 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _68_21910))
in (f_has_t, _68_21911))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_21912))
in ((f_has_t)::[], (fsym)::[], _68_21913))
in (mkForall_fuel _68_21914))
in (_68_21915, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21916))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
(let _50_861 = (match ((Microsoft_FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, f)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(x, f)
end
| _ -> begin
(failwith ("impossible"))
end)
in (match (_50_861) with
| (x, f) -> begin
(let _50_864 = (encode_typ_term x.Microsoft_FStar_Absyn_Syntax.sort env)
in (match (_50_864) with
| (base_t, decls) -> begin
(let _50_868 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_868) with
| (x, xtm, env') -> begin
(let _50_871 = (encode_formula f env')
in (match (_50_871) with
| (refinement, decls') -> begin
(let encoding = (let _68_21918 = (let _68_21917 = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t)
in (_68_21917, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21918))
in (let cvars = (let _68_21920 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (Support.Prims.pipe_right _68_21920 (Support.List.filter (fun ( _50_876 ) -> (match (_50_876) with
| (y, _) -> begin
(y <> x)
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _68_21923 = (let _68_21922 = (let _68_21921 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _68_21921))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21922))
in (_68_21923, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _68_21925 = (let _68_21924 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _68_21924))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21925))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _68_21927 = (let _68_21926 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (xfv)::cvars, _68_21926))
in (mkForall_fuel _68_21927))
in (let t_decls = (let _68_21934 = (let _68_21933 = (let _68_21932 = (let _68_21931 = (let _68_21930 = (let _68_21929 = (let _68_21928 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_68_21928))
in (assumption, _68_21929))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21930))
in (_68_21931)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_68_21932)
in (tdecl)::_68_21933)
in (Support.List.append (Support.List.append decls decls') _68_21934))
in (let _50_897 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _68_21935 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _68_21935))
in (let _50_906 = (encode_knd k env ttm)
in (match (_50_906) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let is_full_app = (fun ( _50_913 ) -> (match (()) with
| () -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind head)
in (let _50_918 = (Microsoft_FStar_Absyn_Util.kind_formals kk)
in (match (_50_918) with
| (formals, _) -> begin
((Support.List.length formals) = (Support.List.length args))
end)))
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_typ head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _50_925 = (encode_args args env)
in (match (_50_925) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _50_931 = (encode_args args env)
in (match (_50_931) with
| (args, decls) -> begin
(match ((is_full_app ())) with
| true -> begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _68_21940 = (let _68_21939 = (Support.List.map (fun ( _50_10 ) -> (match (_50_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (head, _68_21939))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21940))
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
(let ttm = (let _68_21941 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _68_21941))
in (let _50_947 = (encode_knd k env ttm)
in (match (_50_947) with
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
(let _50_962 = (encode_binders None bs env)
in (match (_50_962) with
| (vars, guards, env, decls, _) -> begin
(let _50_965 = (encode_typ_term body env)
in (match (_50_965) with
| (body, decls') -> begin
(let key_body = (let _68_21945 = (let _68_21944 = (let _68_21943 = (let _68_21942 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_68_21942, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_21943))
in ([], vars, _68_21944))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_21945))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _68_21948 = (let _68_21947 = (let _68_21946 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _68_21946))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21947))
in (_68_21948, []))
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
in (let t = (let _68_21950 = (let _68_21949 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _68_21949))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21950))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _68_21957 = (let _68_21956 = (let _68_21955 = (let _68_21954 = (let _68_21953 = (let _68_21952 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _68_21951 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_68_21952, _68_21951)))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_21953))
in ((app)::[], (Support.List.append vars cvars), _68_21954))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_21955))
in (_68_21956, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21957))
in (let kinding = (let _50_988 = (let _68_21958 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _68_21958 env t))
in (match (_50_988) with
| (ktm, decls'') -> begin
(let _68_21962 = (let _68_21961 = (let _68_21960 = (let _68_21959 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_68_21959, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21960))
in (_68_21961)::[])
in (Support.List.append decls'' _68_21962))
end))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _50_991 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
(let _68_21963 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _68_21963 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _68_21968 = (let _68_21967 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_21966 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _68_21965 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _68_21964 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _68_21967 _68_21966 _68_21965 _68_21964)))))
in (failwith (_68_21968)))
end)))
and encode_exp = (fun ( e ) ( env ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(let _68_21971 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _68_21971 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _)) -> begin
(let _68_21972 = (lookup_free_var env v)
in (_68_21972, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _68_21973 = (encode_const c)
in (_68_21973, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _)) -> begin
(let _50_1028 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)) -> begin
(let e = (let _68_21974 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _68_21974))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun ( _50_1047 ) -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _68_21977 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_68_21977, (decl)::[]))))
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _50_1051 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _68_21978 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_21978))) with
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
(let _50_1063 = (Support.Microsoft.FStar.Util.first_N nformals bs)
in (match (_50_1063) with
| (bs0, rest) -> begin
(let res_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s (Microsoft_FStar_Absyn_Util.comp_result c))
end
| _ -> begin
(failwith ("Impossible"))
end)
in (let e = (let _68_21980 = (let _68_21979 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _68_21979))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _68_21980 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end
| false -> begin
(let _50_1076 = (encode_binders None bs env)
in (match (_50_1076) with
| (vars, guards, envbody, decls, _) -> begin
(let _50_1079 = (encode_exp body envbody)
in (match (_50_1079) with
| (body, decls') -> begin
(let key_body = (let _68_21984 = (let _68_21983 = (let _68_21982 = (let _68_21981 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_68_21981, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_21982))
in ([], vars, _68_21983))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_21984))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _68_21987 = (let _68_21986 = (let _68_21985 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _68_21985))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21986))
in (_68_21987, []))
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
in (let f = (let _68_21989 = (let _68_21988 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _68_21988))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_21989))
in (let app = (mk_ApplyE f vars)
in (let _50_1101 = (encode_typ_pred' None tfun env f)
in (match (_50_1101) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _68_21991 = (let _68_21990 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_68_21990, Some ((Support.String.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21991))
in (let interp_f = (let _68_21998 = (let _68_21997 = (let _68_21996 = (let _68_21995 = (let _68_21994 = (let _68_21993 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _68_21992 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_68_21993, _68_21992)))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_21994))
in ((app)::[], (Support.List.append vars cvars), _68_21995))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_21996))
in (_68_21997, Some ((Support.String.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21998))
in (let f_decls = (Support.List.append (Support.List.append (Support.List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _50_1105 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
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
(let _50_1144 = (encode_exp v1 env)
in (match (_50_1144) with
| (v1, decls1) -> begin
(let _50_1147 = (encode_exp v2 env)
in (match (_50_1147) with
| (v2, decls2) -> begin
(let _68_21999 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_68_21999, (Support.List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _68_22000 = (whnf_e env e)
in (encode_exp _68_22000 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args_e)) -> begin
(let _50_1170 = (encode_args args_e env)
in (match (_50_1170) with
| (args, decls) -> begin
(let encode_partial_app = (fun ( ht_opt ) -> (let _50_1175 = (encode_exp head env)
in (match (_50_1175) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (Support.List.append decls decls'))
end
| Some ((formals, c)) -> begin
(let _50_1184 = (Support.Microsoft.FStar.Util.first_N (Support.List.length args_e) formals)
in (match (_50_1184) with
| (formals, rest) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _68_22003 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _68_22003 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _50_1189 = (encode_typ_pred' None ty env app_tm)
in (match (_50_1189) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _68_22005 = (let _68_22004 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_68_22004, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22005))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun ( fv ) -> (let _50_1196 = (lookup_free_var_sym env fv)
in (match (_50_1196) with
| (fname, fuel_args) -> begin
(let tm = (let _68_22011 = (let _68_22010 = (let _68_22009 = (Support.List.map (fun ( _50_11 ) -> (match (_50_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (Support.List.append fuel_args _68_22009))
in (fname, _68_22010))
in (Microsoft_FStar_ToSMT_Term.mkApp' _68_22011))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _50_1203 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _68_22013 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _68_22012 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _68_22013 _68_22012)))
end
| false -> begin
()
end)
in (let head_type = (let _68_22016 = (let _68_22015 = (let _68_22014 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _68_22014))
in (whnf env _68_22015))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.unrefine _68_22016))
in (let _50_1206 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _68_22019 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _68_22018 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _68_22017 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _68_22019 _68_22018 _68_22017))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _68_22023 = (let _68_22022 = (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_22021 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _68_22020 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" _68_22022 _68_22021 _68_22020))))
in (failwith (_68_22023)))
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
(let _50_1252 = (encode_exp e1 env)
in (match (_50_1252) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _50_1256 = (encode_exp e2 env')
in (match (_50_1256) with
| (ee2, decls2) -> begin
(ee2, (Support.List.append decls1 decls2))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_) -> begin
(let _50_1260 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = Microsoft_FStar_ToSMT_Term.DeclFun ((e, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _68_22024 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_68_22024, (decl_e)::[])))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _50_1270 = (encode_exp e env)
in (match (_50_1270) with
| (scr, decls) -> begin
(let _50_1310 = (Support.List.fold_right (fun ( _50_1274 ) ( _50_1277 ) -> (match ((_50_1274, _50_1277)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (Support.List.fold_right (fun ( _50_1281 ) ( _50_1284 ) -> (match ((_50_1281, _50_1284)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (Support.Prims.pipe_right projections (Support.List.fold_left (fun ( env ) ( _50_1290 ) -> (match (_50_1290) with
| (x, t) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v t)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _50_1304 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _50_1301 = (encode_exp w env)
in (match (_50_1301) with
| (w, decls2) -> begin
(let _68_22035 = (let _68_22034 = (let _68_22033 = (let _68_22032 = (let _68_22031 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _68_22031))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_22032))
in (guard, _68_22033))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_22034))
in (_68_22035, decls2))
end))
end)
in (match (_50_1304) with
| (guard, decls2) -> begin
(let _50_1307 = (encode_exp br env)
in (match (_50_1307) with
| (br, decls3) -> begin
(let _68_22036 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_68_22036, (Support.List.append (Support.List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (Microsoft_FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_50_1310) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (_) -> begin
(let _68_22039 = (let _68_22038 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _68_22037 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" _68_22038 _68_22037)))
in (failwith (_68_22039)))
end))))
and encode_pat = (fun ( env ) ( pat ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _ -> begin
(let _68_22042 = (encode_one_pat env pat)
in (_68_22042)::[])
end))
and encode_one_pat = (fun ( env ) ( pat ) -> (let _50_1322 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_22045 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" _68_22045))
end
| false -> begin
()
end)
in (let _50_1326 = (Microsoft_FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_50_1326) with
| (vars, pat_exp_or_typ) -> begin
(let _50_1347 = (Support.Prims.pipe_right vars (Support.List.fold_left (fun ( _50_1329 ) ( v ) -> (match (_50_1329) with
| (env, vars) -> begin
(match (v) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _50_1337 = (gen_typ_var env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_1337) with
| (aa, _, env) -> begin
(env, ((v, (aa, Microsoft_FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _50_1344 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_50_1344) with
| (xx, _, env) -> begin
(env, ((v, (xx, Microsoft_FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_50_1347) with
| (env, vars) -> begin
(let rec mk_guard = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith ("Impossible"))
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
Microsoft_FStar_ToSMT_Term.mkTrue
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _68_22053 = (let _68_22052 = (encode_const c)
in (scrutinee, _68_22052))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_22053))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (Support.Prims.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _68_22056 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _68_22056))))))
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
(let _68_22064 = (Support.Prims.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _68_22063 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _68_22063))))))
in (Support.Prims.pipe_right _68_22064 Support.List.flatten))
end))
in (let pat_term = (fun ( _50_1421 ) -> (match (()) with
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
and encode_args = (fun ( l ) ( env ) -> (let _50_1451 = (Support.Prims.pipe_right l (Support.List.fold_left (fun ( _50_1431 ) ( x ) -> (match (_50_1431) with
| (tms, decls) -> begin
(match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let _50_1440 = (encode_typ_term t env)
in (match (_50_1440) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inl (t))::tms, (Support.List.append decls decls'))
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(let _50_1448 = (encode_exp e env)
in (match (_50_1448) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inr (t))::tms, (Support.List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_50_1451) with
| (l, decls) -> begin
((Support.List.rev l), decls)
end)))
and encode_formula = (fun ( phi ) ( env ) -> (let _50_1457 = (encode_formula_with_labels phi env)
in (match (_50_1457) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _ -> begin
(failwith ("Unexpected labels in formula"))
end)
end)))
and encode_function_type_as_formula = (fun ( induction_on ) ( t ) ( env ) -> (let v_or_t_pat = (fun ( p ) -> (match ((let _68_22078 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _68_22078.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, (Support.Microsoft.FStar.Util.Inl (_), _)::(Support.Microsoft.FStar.Util.Inr (e), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, (Support.Microsoft.FStar.Util.Inl (t), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _ -> begin
(failwith ("Unexpected pattern term"))
end))
in (let rec lemma_pats = (fun ( p ) -> (match ((let _68_22081 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _68_22081.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, _::(Support.Microsoft.FStar.Util.Inr (hd), _)::(Support.Microsoft.FStar.Util.Inr (tl), _)::[])) -> begin
(let _68_22083 = (v_or_t_pat hd)
in (let _68_22082 = (lemma_pats tl)
in (_68_22083)::_68_22082))
end
| _ -> begin
[]
end))
in (let _50_1553 = (match ((let _68_22084 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _68_22084.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _)::(Support.Microsoft.FStar.Util.Inl (post), _)::(Support.Microsoft.FStar.Util.Inr (pats), _)::[] -> begin
(let _68_22085 = (lemma_pats pats)
in (binders, pre, post, _68_22085))
end
| _ -> begin
(failwith ("impos"))
end)
end
| _ -> begin
(failwith ("Impos"))
end)
in (match (_50_1553) with
| (binders, pre, post, patterns) -> begin
(let _50_1560 = (encode_binders None binders env)
in (match (_50_1560) with
| (vars, guards, env, decls, _) -> begin
(let _50_1576 = (let _68_22087 = (Support.Prims.pipe_right patterns (Support.List.map (fun ( _50_12 ) -> (match (_50_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _50_1572 = env
in {bindings = _50_1572.bindings; depth = _50_1572.depth; tcenv = _50_1572.tcenv; warn = _50_1572.warn; cache = _50_1572.cache; nolabels = _50_1572.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1572.encode_non_total_function_typ}))
end))))
in (Support.Prims.pipe_right _68_22087 Support.List.unzip))
in (match (_50_1576) with
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
(let _68_22089 = (let _68_22088 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _68_22088 e))
in (_68_22089)::pats)
end
| _ -> begin
(let rec aux = (fun ( tl ) ( vars ) -> (match (vars) with
| [] -> begin
(let _68_22094 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_68_22094)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _68_22096 = (let _68_22095 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _68_22095 tl))
in (aux _68_22096 vars))
end
| _ -> begin
pats
end))
in (let _68_22097 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _68_22097 vars)))
end)
end)
in (let env = (let _50_1597 = env
in {bindings = _50_1597.bindings; depth = _50_1597.depth; tcenv = _50_1597.tcenv; warn = _50_1597.warn; cache = _50_1597.cache; nolabels = true; use_zfuel_name = _50_1597.use_zfuel_name; encode_non_total_function_typ = _50_1597.encode_non_total_function_typ})
in (let _50_1602 = (let _68_22098 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _68_22098 env))
in (match (_50_1602) with
| (pre, decls'') -> begin
(let _50_1605 = (let _68_22099 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _68_22099 env))
in (match (_50_1605) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in (let _68_22104 = (let _68_22103 = (let _68_22102 = (let _68_22101 = (let _68_22100 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_68_22100, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22101))
in (pats, vars, _68_22102))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22103))
in (_68_22104, decls)))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun ( phi ) ( env ) -> (let enc = (fun ( f ) -> (fun ( l ) -> (let _50_1626 = (Support.Microsoft.FStar.Util.fold_map (fun ( decls ) ( x ) -> (match ((Support.Prims.fst x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _50_1618 = (encode_typ_term t env)
in (match (_50_1618) with
| (t, decls') -> begin
((Support.List.append decls decls'), t)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _50_1623 = (encode_exp e env)
in (match (_50_1623) with
| (e, decls') -> begin
((Support.List.append decls decls'), e)
end))
end)) [] l)
in (match (_50_1626) with
| (decls, args) -> begin
(let _68_22122 = (f args)
in (_68_22122, [], decls))
end))))
in (let enc_prop_c = (fun ( f ) -> (fun ( l ) -> (let _50_1646 = (Support.List.fold_right (fun ( t ) ( _50_1634 ) -> (match (_50_1634) with
| (phis, labs, decls) -> begin
(match ((Support.Prims.fst t)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _50_1640 = (encode_formula_with_labels t env)
in (match (_50_1640) with
| (phi, labs', decls') -> begin
((phi)::phis, (Support.List.append labs' labs), (Support.List.append decls' decls))
end))
end
| _ -> begin
(failwith ("Expected a formula"))
end)
end)) l ([], [], []))
in (match (_50_1646) with
| (phis, labs, decls) -> begin
(let _68_22138 = (f phis)
in (_68_22138, labs, decls))
end))))
in (let const_op = (fun ( f ) ( _50_1649 ) -> (f, [], []))
in (let un_op = (fun ( f ) ( l ) -> (let _68_22152 = (Support.List.hd l)
in (Support.Prims.pipe_left f _68_22152)))
in (let bin_op = (fun ( f ) ( _50_13 ) -> (match (_50_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _ -> begin
(failwith ("Impossible"))
end))
in (let eq_op = (fun ( _50_14 ) -> (match (_50_14) with
| _::_::e1::e2::[] -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun ( _50_15 ) -> (match (_50_15) with
| (Support.Microsoft.FStar.Util.Inl (lhs), _)::(Support.Microsoft.FStar.Util.Inl (rhs), _)::[] -> begin
(let _50_1687 = (encode_formula_with_labels rhs env)
in (match (_50_1687) with
| (l1, labs1, decls1) -> begin
(match (l1.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _)) -> begin
(l1, labs1, decls1)
end
| _ -> begin
(let _50_1698 = (encode_formula_with_labels lhs env)
in (match (_50_1698) with
| (l2, labs2, decls2) -> begin
(let _68_22166 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_68_22166, (Support.List.append labs1 labs2), (Support.List.append decls1 decls2)))
end))
end)
end))
end
| _ -> begin
(failwith ("impossible"))
end))
in (let mk_ite = (fun ( _50_16 ) -> (match (_50_16) with
| (Support.Microsoft.FStar.Util.Inl (guard), _)::(Support.Microsoft.FStar.Util.Inl (_then), _)::(Support.Microsoft.FStar.Util.Inl (_else), _)::[] -> begin
(let _50_1722 = (encode_formula_with_labels guard env)
in (match (_50_1722) with
| (g, labs1, decls1) -> begin
(let _50_1726 = (encode_formula_with_labels _then env)
in (match (_50_1726) with
| (t, labs2, decls2) -> begin
(let _50_1730 = (encode_formula_with_labels _else env)
in (match (_50_1730) with
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
in (let unboxInt_l = (fun ( f ) ( l ) -> (let _68_22178 = (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _68_22178)))
in (let connectives = (let _68_22239 = (let _68_22187 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _68_22187))
in (let _68_22238 = (let _68_22237 = (let _68_22193 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _68_22193))
in (let _68_22236 = (let _68_22235 = (let _68_22234 = (let _68_22202 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _68_22202))
in (let _68_22233 = (let _68_22232 = (let _68_22231 = (let _68_22211 = (Support.Prims.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _68_22211))
in (let _68_22230 = (let _68_22229 = (let _68_22217 = (Support.Prims.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _68_22217))
in (_68_22229)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_68_22231)::_68_22230))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_68_22232)
in (_68_22234)::_68_22233))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_68_22235)
in (_68_22237)::_68_22236))
in (_68_22239)::_68_22238))
in (let fallback = (fun ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((phi', msg, r, b))) -> begin
(let _50_1751 = (encode_formula_with_labels phi' env)
in (match (_50_1751) with
| (phi, labs, decls) -> begin
(match (env.nolabels) with
| true -> begin
(phi, [], decls)
end
| false -> begin
(let lvar = (let _68_22242 = (varops.fresh "label")
in (_68_22242, Microsoft_FStar_ToSMT_Term.Bool_sort))
in (let lterm = (Microsoft_FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (Microsoft_FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ih); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inr (l), _)::(Support.Microsoft.FStar.Util.Inl (phi), _)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals ih.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.using_IH) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let _50_1783 = (encode_exp l env)
in (match (_50_1783) with
| (e, decls) -> begin
(let _50_1786 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_50_1786) with
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
(let _50_1791 = (encode_typ_term phi env)
in (match (_50_1791) with
| (tt, decls) -> begin
(let _68_22243 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_68_22243, [], decls))
end))
end))
in (let encode_q_body = (fun ( env ) ( bs ) ( ps ) ( body ) -> (let _50_1803 = (encode_binders None bs env)
in (match (_50_1803) with
| (vars, guards, env, decls, _) -> begin
(let _50_1819 = (let _68_22253 = (Support.Prims.pipe_right ps (Support.List.map (fun ( _50_17 ) -> (match (_50_17) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_typ_term t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _50_1815 = env
in {bindings = _50_1815.bindings; depth = _50_1815.depth; tcenv = _50_1815.tcenv; warn = _50_1815.warn; cache = _50_1815.cache; nolabels = _50_1815.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1815.encode_non_total_function_typ}))
end))))
in (Support.Prims.pipe_right _68_22253 Support.List.unzip))
in (match (_50_1819) with
| (pats, decls') -> begin
(let _50_1823 = (encode_formula_with_labels body env)
in (match (_50_1823) with
| (body, labs, decls'') -> begin
(let _68_22254 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _68_22254, body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'')))
end))
end))
end)))
in (let _50_1824 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_22255 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" _68_22255))
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
(match ((Support.Prims.pipe_right connectives (Support.List.tryFind (fun ( _50_1836 ) -> (match (_50_1836) with
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
(let _50_1849 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_22271 = (Support.Prims.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" _68_22271))
end
| false -> begin
()
end)
in (let _50_1857 = (encode_q_body env vars pats body)
in (match (_50_1857) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _68_22274 = (let _68_22273 = (let _68_22272 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _68_22272))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22273))
in (_68_22274, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _50_1870 = (encode_q_body env vars pats body)
in (match (_50_1870) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _68_22277 = (let _68_22276 = (let _68_22275 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _68_22275))
in (Microsoft_FStar_ToSMT_Term.mkExists _68_22276))
in (_68_22277, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : Microsoft_FStar_Absyn_Syntax.lident  ->  string  ->  Microsoft_FStar_ToSMT_Term.decl list; is : Microsoft_FStar_Absyn_Syntax.lident  ->  bool}

let is_Mkprims_t = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkprims_t")))

let prims = (let _50_1876 = (fresh_fvar "a" Microsoft_FStar_ToSMT_Term.Type_sort)
in (match (_50_1876) with
| (asym, a) -> begin
(let _50_1879 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_50_1879) with
| (xsym, x) -> begin
(let _50_1882 = (fresh_fvar "y" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_50_1882) with
| (ysym, y) -> begin
(let deffun = (fun ( vars ) ( body ) ( x ) -> (Microsoft_FStar_ToSMT_Term.DefineFun ((x, vars, Microsoft_FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun ( vars ) ( body ) -> (fun ( x ) -> (let t1 = (let _68_22320 = (let _68_22319 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _68_22319))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22320))
in (let vname_decl = (let _68_22322 = (let _68_22321 = (Support.Prims.pipe_right vars (Support.List.map Support.Prims.snd))
in (x, _68_22321, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_68_22322))
in (let _68_22328 = (let _68_22327 = (let _68_22326 = (let _68_22325 = (let _68_22324 = (let _68_22323 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _68_22323))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22324))
in (_68_22325, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22326))
in (_68_22327)::[])
in (vname_decl)::_68_22328)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _68_22488 = (let _68_22337 = (let _68_22336 = (let _68_22335 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22335))
in (quant axy _68_22336))
in (Microsoft_FStar_Absyn_Const.op_Eq, _68_22337))
in (let _68_22487 = (let _68_22486 = (let _68_22344 = (let _68_22343 = (let _68_22342 = (let _68_22341 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _68_22341))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22342))
in (quant axy _68_22343))
in (Microsoft_FStar_Absyn_Const.op_notEq, _68_22344))
in (let _68_22485 = (let _68_22484 = (let _68_22353 = (let _68_22352 = (let _68_22351 = (let _68_22350 = (let _68_22349 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22348 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22349, _68_22348)))
in (Microsoft_FStar_ToSMT_Term.mkLT _68_22350))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22351))
in (quant xy _68_22352))
in (Microsoft_FStar_Absyn_Const.op_LT, _68_22353))
in (let _68_22483 = (let _68_22482 = (let _68_22362 = (let _68_22361 = (let _68_22360 = (let _68_22359 = (let _68_22358 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22357 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22358, _68_22357)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _68_22359))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22360))
in (quant xy _68_22361))
in (Microsoft_FStar_Absyn_Const.op_LTE, _68_22362))
in (let _68_22481 = (let _68_22480 = (let _68_22371 = (let _68_22370 = (let _68_22369 = (let _68_22368 = (let _68_22367 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22366 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22367, _68_22366)))
in (Microsoft_FStar_ToSMT_Term.mkGT _68_22368))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22369))
in (quant xy _68_22370))
in (Microsoft_FStar_Absyn_Const.op_GT, _68_22371))
in (let _68_22479 = (let _68_22478 = (let _68_22380 = (let _68_22379 = (let _68_22378 = (let _68_22377 = (let _68_22376 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22375 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22376, _68_22375)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _68_22377))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22378))
in (quant xy _68_22379))
in (Microsoft_FStar_Absyn_Const.op_GTE, _68_22380))
in (let _68_22477 = (let _68_22476 = (let _68_22389 = (let _68_22388 = (let _68_22387 = (let _68_22386 = (let _68_22385 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22384 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22385, _68_22384)))
in (Microsoft_FStar_ToSMT_Term.mkSub _68_22386))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _68_22387))
in (quant xy _68_22388))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _68_22389))
in (let _68_22475 = (let _68_22474 = (let _68_22396 = (let _68_22395 = (let _68_22394 = (let _68_22393 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _68_22393))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _68_22394))
in (quant qx _68_22395))
in (Microsoft_FStar_Absyn_Const.op_Minus, _68_22396))
in (let _68_22473 = (let _68_22472 = (let _68_22405 = (let _68_22404 = (let _68_22403 = (let _68_22402 = (let _68_22401 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22400 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22401, _68_22400)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _68_22402))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _68_22403))
in (quant xy _68_22404))
in (Microsoft_FStar_Absyn_Const.op_Addition, _68_22405))
in (let _68_22471 = (let _68_22470 = (let _68_22414 = (let _68_22413 = (let _68_22412 = (let _68_22411 = (let _68_22410 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22409 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22410, _68_22409)))
in (Microsoft_FStar_ToSMT_Term.mkMul _68_22411))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _68_22412))
in (quant xy _68_22413))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _68_22414))
in (let _68_22469 = (let _68_22468 = (let _68_22423 = (let _68_22422 = (let _68_22421 = (let _68_22420 = (let _68_22419 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22418 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22419, _68_22418)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _68_22420))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _68_22421))
in (quant xy _68_22422))
in (Microsoft_FStar_Absyn_Const.op_Division, _68_22423))
in (let _68_22467 = (let _68_22466 = (let _68_22432 = (let _68_22431 = (let _68_22430 = (let _68_22429 = (let _68_22428 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22427 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_68_22428, _68_22427)))
in (Microsoft_FStar_ToSMT_Term.mkMod _68_22429))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _68_22430))
in (quant xy _68_22431))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _68_22432))
in (let _68_22465 = (let _68_22464 = (let _68_22441 = (let _68_22440 = (let _68_22439 = (let _68_22438 = (let _68_22437 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _68_22436 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_68_22437, _68_22436)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_22438))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22439))
in (quant xy _68_22440))
in (Microsoft_FStar_Absyn_Const.op_And, _68_22441))
in (let _68_22463 = (let _68_22462 = (let _68_22450 = (let _68_22449 = (let _68_22448 = (let _68_22447 = (let _68_22446 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _68_22445 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_68_22446, _68_22445)))
in (Microsoft_FStar_ToSMT_Term.mkOr _68_22447))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22448))
in (quant xy _68_22449))
in (Microsoft_FStar_Absyn_Const.op_Or, _68_22450))
in (let _68_22461 = (let _68_22460 = (let _68_22457 = (let _68_22456 = (let _68_22455 = (let _68_22454 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _68_22454))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_22455))
in (quant qx _68_22456))
in (Microsoft_FStar_Absyn_Const.op_Negation, _68_22457))
in (_68_22460)::[])
in (_68_22462)::_68_22461))
in (_68_22464)::_68_22463))
in (_68_22466)::_68_22465))
in (_68_22468)::_68_22467))
in (_68_22470)::_68_22469))
in (_68_22472)::_68_22471))
in (_68_22474)::_68_22473))
in (_68_22476)::_68_22475))
in (_68_22478)::_68_22477))
in (_68_22480)::_68_22479))
in (_68_22482)::_68_22481))
in (_68_22484)::_68_22483))
in (_68_22486)::_68_22485))
in (_68_22488)::_68_22487))
in (let mk = (fun ( l ) ( v ) -> (let _68_22519 = (Support.Prims.pipe_right prims (Support.List.filter (fun ( _50_1902 ) -> (match (_50_1902) with
| (l', _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (Support.Prims.pipe_right _68_22519 (Support.List.collect (fun ( _50_1906 ) -> (match (_50_1906) with
| (_, b) -> begin
(b v)
end))))))
in (let is = (fun ( l ) -> (Support.Prims.pipe_right prims (Support.Microsoft.FStar.Util.for_some (fun ( _50_1912 ) -> (match (_50_1912) with
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
in (let mk_unit = (fun ( _50_1918 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let _68_22550 = (let _68_22541 = (let _68_22540 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_68_22540, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22541))
in (let _68_22549 = (let _68_22548 = (let _68_22547 = (let _68_22546 = (let _68_22545 = (let _68_22544 = (let _68_22543 = (let _68_22542 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _68_22542))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22543))
in ((typing_pred)::[], (xx)::[], _68_22544))
in (mkForall_fuel _68_22545))
in (_68_22546, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22547))
in (_68_22548)::[])
in (_68_22550)::_68_22549))))
in (let mk_bool = (fun ( _50_1923 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _68_22570 = (let _68_22560 = (let _68_22559 = (let _68_22558 = (let _68_22557 = (let _68_22556 = (let _68_22555 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _68_22555))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22556))
in ((typing_pred)::[], (xx)::[], _68_22557))
in (mkForall_fuel _68_22558))
in (_68_22559, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22560))
in (let _68_22569 = (let _68_22568 = (let _68_22567 = (let _68_22566 = (let _68_22565 = (let _68_22564 = (let _68_22561 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_68_22561)::[])
in (let _68_22563 = (let _68_22562 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _68_22562 tt))
in (_68_22564, (bb)::[], _68_22563)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22565))
in (_68_22566, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22567))
in (_68_22568)::[])
in (_68_22570)::_68_22569))))))
in (let mk_int = (fun ( _50_1930 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _68_22582 = (let _68_22581 = (let _68_22580 = (let _68_22579 = (let _68_22578 = (let _68_22577 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _68_22576 = (let _68_22575 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_68_22575)::[])
in (_68_22577)::_68_22576))
in (tt)::_68_22578)
in (tt)::_68_22579)
in ("Prims.Precedes", _68_22580))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22581))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _68_22582))
in (let precedes_y_x = (let _68_22583 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _68_22583))
in (let _68_22624 = (let _68_22589 = (let _68_22588 = (let _68_22587 = (let _68_22586 = (let _68_22585 = (let _68_22584 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _68_22584))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22585))
in ((typing_pred)::[], (xx)::[], _68_22586))
in (mkForall_fuel _68_22587))
in (_68_22588, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22589))
in (let _68_22623 = (let _68_22622 = (let _68_22596 = (let _68_22595 = (let _68_22594 = (let _68_22593 = (let _68_22590 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_68_22590)::[])
in (let _68_22592 = (let _68_22591 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _68_22591 tt))
in (_68_22593, (bb)::[], _68_22592)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22594))
in (_68_22595, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22596))
in (let _68_22621 = (let _68_22620 = (let _68_22619 = (let _68_22618 = (let _68_22617 = (let _68_22616 = (let _68_22615 = (let _68_22614 = (let _68_22613 = (let _68_22612 = (let _68_22611 = (let _68_22610 = (let _68_22599 = (let _68_22598 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _68_22597 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_68_22598, _68_22597)))
in (Microsoft_FStar_ToSMT_Term.mkGT _68_22599))
in (let _68_22609 = (let _68_22608 = (let _68_22602 = (let _68_22601 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _68_22600 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_68_22601, _68_22600)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _68_22602))
in (let _68_22607 = (let _68_22606 = (let _68_22605 = (let _68_22604 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _68_22603 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_68_22604, _68_22603)))
in (Microsoft_FStar_ToSMT_Term.mkLT _68_22605))
in (_68_22606)::[])
in (_68_22608)::_68_22607))
in (_68_22610)::_68_22609))
in (typing_pred_y)::_68_22611)
in (typing_pred)::_68_22612)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _68_22613))
in (_68_22614, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22615))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _68_22616))
in (mkForall_fuel _68_22617))
in (_68_22618, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22619))
in (_68_22620)::[])
in (_68_22622)::_68_22621))
in (_68_22624)::_68_22623)))))))))))
in (let mk_int_alias = (fun ( _50_1942 ) ( tt ) -> (let _68_22633 = (let _68_22632 = (let _68_22631 = (let _68_22630 = (let _68_22629 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _68_22629))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_22630))
in (_68_22631, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22632))
in (_68_22633)::[]))
in (let mk_str = (fun ( _50_1946 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _68_22653 = (let _68_22643 = (let _68_22642 = (let _68_22641 = (let _68_22640 = (let _68_22639 = (let _68_22638 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _68_22638))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22639))
in ((typing_pred)::[], (xx)::[], _68_22640))
in (mkForall_fuel _68_22641))
in (_68_22642, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22643))
in (let _68_22652 = (let _68_22651 = (let _68_22650 = (let _68_22649 = (let _68_22648 = (let _68_22647 = (let _68_22644 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_68_22644)::[])
in (let _68_22646 = (let _68_22645 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _68_22645 tt))
in (_68_22647, (bb)::[], _68_22646)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22648))
in (_68_22649, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22650))
in (_68_22651)::[])
in (_68_22653)::_68_22652))))))
in (let mk_ref = (fun ( reft_name ) ( _50_1954 ) -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _68_22660 = (let _68_22659 = (let _68_22658 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_68_22658)::[])
in (reft_name, _68_22659))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22660))
in (let refb = (let _68_22663 = (let _68_22662 = (let _68_22661 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_68_22661)::[])
in (reft_name, _68_22662))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22663))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _68_22682 = (let _68_22669 = (let _68_22668 = (let _68_22667 = (let _68_22666 = (let _68_22665 = (let _68_22664 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _68_22664))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22665))
in ((typing_pred)::[], (xx)::(aa)::[], _68_22666))
in (mkForall_fuel _68_22667))
in (_68_22668, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22669))
in (let _68_22681 = (let _68_22680 = (let _68_22679 = (let _68_22678 = (let _68_22677 = (let _68_22676 = (let _68_22675 = (let _68_22674 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _68_22673 = (let _68_22672 = (let _68_22671 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _68_22670 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_68_22671, _68_22670)))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_22672))
in (_68_22674, _68_22673)))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22675))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _68_22676))
in (mkForall_fuel' 2 _68_22677))
in (_68_22678, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22679))
in (_68_22680)::[])
in (_68_22682)::_68_22681))))))))))
in (let mk_false_interp = (fun ( _50_1964 ) ( false_tm ) -> (let valid = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _68_22689 = (let _68_22688 = (let _68_22687 = (Microsoft_FStar_ToSMT_Term.mkIff (Microsoft_FStar_ToSMT_Term.mkFalse, valid))
in (_68_22687, Some ("False interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22688))
in (_68_22689)::[])))
in (let mk_and_interp = (fun ( conj ) ( _50_1970 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _68_22696 = (let _68_22695 = (let _68_22694 = (Microsoft_FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_68_22694)::[])
in ("Valid", _68_22695))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22696))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _68_22703 = (let _68_22702 = (let _68_22701 = (let _68_22700 = (let _68_22699 = (let _68_22698 = (let _68_22697 = (Microsoft_FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_68_22697, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22698))
in ((valid)::[], (aa)::(bb)::[], _68_22699))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22700))
in (_68_22701, Some ("/\\ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22702))
in (_68_22703)::[])))))))))
in (let mk_or_interp = (fun ( disj ) ( _50_1981 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _68_22710 = (let _68_22709 = (let _68_22708 = (Microsoft_FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_68_22708)::[])
in ("Valid", _68_22709))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22710))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _68_22717 = (let _68_22716 = (let _68_22715 = (let _68_22714 = (let _68_22713 = (let _68_22712 = (let _68_22711 = (Microsoft_FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_68_22711, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22712))
in ((valid)::[], (aa)::(bb)::[], _68_22713))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22714))
in (_68_22715, Some ("\\/ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22716))
in (_68_22717)::[])))))))))
in (let mk_eq2_interp = (fun ( eq2 ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _68_22724 = (let _68_22723 = (let _68_22722 = (Microsoft_FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_68_22722)::[])
in ("Valid", _68_22723))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22724))
in (let _68_22731 = (let _68_22730 = (let _68_22729 = (let _68_22728 = (let _68_22727 = (let _68_22726 = (let _68_22725 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (_68_22725, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22726))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _68_22727))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22728))
in (_68_22729, Some ("Eq2 interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22730))
in (_68_22731)::[])))))))))))
in (let mk_imp_interp = (fun ( imp ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _68_22738 = (let _68_22737 = (let _68_22736 = (Microsoft_FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_68_22736)::[])
in ("Valid", _68_22737))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22738))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _68_22745 = (let _68_22744 = (let _68_22743 = (let _68_22742 = (let _68_22741 = (let _68_22740 = (let _68_22739 = (Microsoft_FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_68_22739, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22740))
in ((valid)::[], (aa)::(bb)::[], _68_22741))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22742))
in (_68_22743, Some ("==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22744))
in (_68_22745)::[])))))))))
in (let mk_iff_interp = (fun ( iff ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _68_22752 = (let _68_22751 = (let _68_22750 = (Microsoft_FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_68_22750)::[])
in ("Valid", _68_22751))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22752))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _68_22759 = (let _68_22758 = (let _68_22757 = (let _68_22756 = (let _68_22755 = (let _68_22754 = (let _68_22753 = (Microsoft_FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_68_22753, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22754))
in ((valid)::[], (aa)::(bb)::[], _68_22755))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22756))
in (_68_22757, Some ("<==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22758))
in (_68_22759)::[])))))))))
in (let mk_forall_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _68_22766 = (let _68_22765 = (let _68_22764 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_68_22764)::[])
in ("Valid", _68_22765))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22766))
in (let valid_b_x = (let _68_22769 = (let _68_22768 = (let _68_22767 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_68_22767)::[])
in ("Valid", _68_22768))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22769))
in (let _68_22782 = (let _68_22781 = (let _68_22780 = (let _68_22779 = (let _68_22778 = (let _68_22777 = (let _68_22776 = (let _68_22775 = (let _68_22774 = (let _68_22770 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_68_22770)::[])
in (let _68_22773 = (let _68_22772 = (let _68_22771 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_68_22771, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22772))
in (_68_22774, (xx)::[], _68_22773)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22775))
in (_68_22776, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22777))
in ((valid)::[], (aa)::(bb)::[], _68_22778))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22779))
in (_68_22780, Some ("forall interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22781))
in (_68_22782)::[]))))))))))
in (let mk_exists_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _68_22789 = (let _68_22788 = (let _68_22787 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_68_22787)::[])
in ("Valid", _68_22788))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22789))
in (let valid_b_x = (let _68_22792 = (let _68_22791 = (let _68_22790 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_68_22790)::[])
in ("Valid", _68_22791))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22792))
in (let _68_22805 = (let _68_22804 = (let _68_22803 = (let _68_22802 = (let _68_22801 = (let _68_22800 = (let _68_22799 = (let _68_22798 = (let _68_22797 = (let _68_22793 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_68_22793)::[])
in (let _68_22796 = (let _68_22795 = (let _68_22794 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_68_22794, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22795))
in (_68_22797, (xx)::[], _68_22796)))
in (Microsoft_FStar_ToSMT_Term.mkExists _68_22798))
in (_68_22799, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22800))
in ((valid)::[], (aa)::(bb)::[], _68_22801))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22802))
in (_68_22803, Some ("exists interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22804))
in (_68_22805)::[]))))))))))
in (let mk_foralltyp_interp = (fun ( for_all ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _68_22812 = (let _68_22811 = (let _68_22810 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_68_22810)::[])
in ("Valid", _68_22811))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22812))
in (let valid_a_b = (let _68_22815 = (let _68_22814 = (let _68_22813 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_68_22813)::[])
in ("Valid", _68_22814))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22815))
in (let _68_22828 = (let _68_22827 = (let _68_22826 = (let _68_22825 = (let _68_22824 = (let _68_22823 = (let _68_22822 = (let _68_22821 = (let _68_22820 = (let _68_22816 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_68_22816)::[])
in (let _68_22819 = (let _68_22818 = (let _68_22817 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_68_22817, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22818))
in (_68_22820, (bb)::[], _68_22819)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22821))
in (_68_22822, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22823))
in ((valid)::[], (kk)::(aa)::[], _68_22824))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22825))
in (_68_22826, Some ("ForallTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22827))
in (_68_22828)::[]))))))))))
in (let mk_existstyp_interp = (fun ( for_some ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _68_22835 = (let _68_22834 = (let _68_22833 = (Microsoft_FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_68_22833)::[])
in ("Valid", _68_22834))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22835))
in (let valid_a_b = (let _68_22838 = (let _68_22837 = (let _68_22836 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_68_22836)::[])
in ("Valid", _68_22837))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_22838))
in (let _68_22851 = (let _68_22850 = (let _68_22849 = (let _68_22848 = (let _68_22847 = (let _68_22846 = (let _68_22845 = (let _68_22844 = (let _68_22843 = (let _68_22839 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_68_22839)::[])
in (let _68_22842 = (let _68_22841 = (let _68_22840 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_68_22840, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_22841))
in (_68_22843, (bb)::[], _68_22842)))
in (Microsoft_FStar_ToSMT_Term.mkExists _68_22844))
in (_68_22845, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _68_22846))
in ((valid)::[], (kk)::(aa)::[], _68_22847))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_22848))
in (_68_22849, Some ("ExistsTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_22850))
in (_68_22851)::[]))))))))))
in (let prims = ((Microsoft_FStar_Absyn_Const.unit_lid, mk_unit))::((Microsoft_FStar_Absyn_Const.bool_lid, mk_bool))::((Microsoft_FStar_Absyn_Const.int_lid, mk_int))::((Microsoft_FStar_Absyn_Const.string_lid, mk_str))::((Microsoft_FStar_Absyn_Const.ref_lid, mk_ref))::((Microsoft_FStar_Absyn_Const.char_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.uint8_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.false_lid, mk_false_interp))::((Microsoft_FStar_Absyn_Const.and_lid, mk_and_interp))::((Microsoft_FStar_Absyn_Const.or_lid, mk_or_interp))::((Microsoft_FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp_interp))::((Microsoft_FStar_Absyn_Const.iff_lid, mk_iff_interp))::((Microsoft_FStar_Absyn_Const.forall_lid, mk_forall_interp))::((Microsoft_FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun ( t ) ( s ) ( tt ) -> (match ((Support.Microsoft.FStar.Util.find_opt (fun ( _50_2074 ) -> (match (_50_2074) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some ((_, f)) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun ( env ) ( se ) -> (let _50_2083 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_22992 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") _68_22992))
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
in (let _50_2091 = (encode_sigelt' env se)
in (match (_50_2091) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _68_22995 = (let _68_22994 = (let _68_22993 = (Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_68_22993))
in (_68_22994)::[])
in (_68_22995, e))
end
| _ -> begin
(let _68_23002 = (let _68_23001 = (let _68_22997 = (let _68_22996 = (Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_68_22996))
in (_68_22997)::g)
in (let _68_23000 = (let _68_22999 = (let _68_22998 = (Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_68_22998))
in (_68_22999)::[])
in (Support.List.append _68_23001 _68_23000)))
in (_68_23002, e))
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
(let _50_2142 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2142) with
| (tname, ttok, env) -> begin
(let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _68_23007 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _68_23007))
in (let decls = (let _68_23015 = (let _68_23014 = (let _68_23013 = (let _68_23012 = (let _68_23011 = (let _68_23010 = (let _68_23009 = (let _68_23008 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _68_23008))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23009))
in ((valid_b2t_x)::[], (xx)::[], _68_23010))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23011))
in (_68_23012, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23013))
in (_68_23014)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_68_23015)
in (decls, env)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _, t, tags, _)) -> begin
(let _50_2160 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2160) with
| (tname, ttok, env) -> begin
(let _50_2169 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((tps', body)) -> begin
((Support.List.append tps tps'), body)
end
| _ -> begin
(tps, t)
end)
in (match (_50_2169) with
| (tps, t) -> begin
(let _50_2176 = (encode_binders None tps env)
in (match (_50_2176) with
| (vars, guards, env', binder_decls, _) -> begin
(let tok_app = (let _68_23016 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _68_23016 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _68_23018 = (let _68_23017 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _68_23017))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23018))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _ -> begin
(let _68_23020 = (let _68_23019 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _68_23019))
in (_68_23020)::[])
end)
in (let decls = (let _68_23031 = (let _68_23024 = (let _68_23023 = (let _68_23022 = (let _68_23021 = (Support.List.map Support.Prims.snd vars)
in (tname, _68_23021, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_68_23022))
in (_68_23023)::(tok_decl)::[])
in (Support.List.append _68_23024 fresh_tok))
in (let _68_23030 = (let _68_23029 = (let _68_23028 = (let _68_23027 = (let _68_23026 = (let _68_23025 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _68_23025))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23026))
in (_68_23027, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23028))
in (_68_23029)::[])
in (Support.List.append _68_23031 _68_23030)))
in (let t = (whnf env t)
in (let _50_2194 = (match ((Support.Prims.pipe_right tags (Support.Microsoft.FStar.Util.for_some (fun ( _50_18 ) -> (match (_50_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _ -> begin
false
end))))) with
| true -> begin
(let _68_23034 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _68_23033 = (encode_formula t env')
in (_68_23034, _68_23033)))
end
| false -> begin
(let _68_23035 = (encode_typ_term t env')
in (app, _68_23035))
end)
in (match (_50_2194) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _68_23042 = (let _68_23041 = (let _68_23040 = (let _68_23039 = (let _68_23038 = (let _68_23037 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _68_23036 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_68_23037, _68_23036)))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23038))
in ((def)::[], vars, _68_23039))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23040))
in (_68_23041, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23042))
in (let kindingAx = (let _50_2198 = (let _68_23043 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _68_23043 env' app))
in (match (_50_2198) with
| (k, decls) -> begin
(let _68_23051 = (let _68_23050 = (let _68_23049 = (let _68_23048 = (let _68_23047 = (let _68_23046 = (let _68_23045 = (let _68_23044 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_68_23044, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23045))
in ((app)::[], vars, _68_23046))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23047))
in (_68_23048, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23049))
in (_68_23050)::[])
in (Support.List.append decls _68_23051))
end))
in (let g = (let _68_23052 = (primitive_type_axioms lid tname app)
in (Support.List.append (Support.List.append (Support.List.append (Support.List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _68_23052))
in (g, env))))
end))))))))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _)) -> begin
(let tt = (whnf env t)
in (let _50_2211 = (encode_free_var env lid t tt quals)
in (match (_50_2211) with
| (decls, env) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_smt_lemma t) && ((Support.Prims.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption)) || env.tcenv.Microsoft_FStar_Tc_Env.is_iface))) with
| true -> begin
(let _68_23054 = (let _68_23053 = (encode_smt_lemma env lid t)
in (Support.List.append decls _68_23053))
in (_68_23054, env))
end
| false -> begin
(decls, env)
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((l, f, _, _)) -> begin
(let _50_2222 = (encode_formula f env)
in (match (_50_2222) with
| (f, decls) -> begin
(let g = (let _68_23059 = (let _68_23058 = (let _68_23057 = (let _68_23056 = (let _68_23055 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "Assumption: %s" _68_23055))
in Some (_68_23056))
in (f, _68_23057))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23058))
in (_68_23059)::[])
in ((Support.List.append decls g), env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _, datas, quals, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.precedes_lid) -> begin
(let _50_2238 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2238) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, _, _, _, _, _, _)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.char_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.Microsoft_FStar_Absyn_Syntax.str
in (let tsym = (Microsoft_FStar_ToSMT_Term.mkFreeV (tname, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((tname, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let _68_23061 = (let _68_23060 = (primitive_type_axioms t tname tsym)
in (decl)::_68_23060)
in (_68_23061, (push_free_tvar env t tname (Some (tsym))))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _, datas, quals, _)) -> begin
(let is_logical = (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _50_19 ) -> (match (_50_19) with
| (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _ -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun ( c ) -> (match (is_logical) with
| true -> begin
(let _50_2282 = c
in (match (_50_2282) with
| (name, args, _, _) -> begin
(let _68_23067 = (let _68_23066 = (let _68_23065 = (Support.Prims.pipe_right args (Support.List.map Support.Prims.snd))
in (name, _68_23065, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_68_23066))
in (_68_23067)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun ( tapp ) ( vars ) -> (match ((((Support.List.length datas) = 0) || (Support.Prims.pipe_right datas (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (let _68_23073 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (Support.Prims.pipe_right _68_23073 Support.Option.isNone))))))) with
| true -> begin
[]
end
| false -> begin
(let _50_2289 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_50_2289) with
| (xxsym, xx) -> begin
(let _50_2332 = (Support.Prims.pipe_right datas (Support.List.fold_left (fun ( _50_2292 ) ( l ) -> (match (_50_2292) with
| (out, decls) -> begin
(let data_t = (Microsoft_FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _50_2302 = (match ((Microsoft_FStar_Absyn_Util.function_formals data_t)) with
| Some ((formals, res)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_50_2302) with
| (args, res) -> begin
(let indices = (match ((let _68_23076 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _68_23076.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_, indices)) -> begin
indices
end
| _ -> begin
[]
end)
in (let env = (Support.Prims.pipe_right args (Support.List.fold_left (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_23081 = (let _68_23080 = (let _68_23079 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_68_23079, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23080))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _68_23081))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_23084 = (let _68_23083 = (let _68_23082 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_68_23082, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23083))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _68_23084))
end)) env))
in (let _50_2320 = (encode_args indices env)
in (match (_50_2320) with
| (indices, decls') -> begin
(let _50_2321 = (match (((Support.List.length indices) <> (Support.List.length vars))) with
| true -> begin
(failwith ("Impossible"))
end
| false -> begin
()
end)
in (let eqs = (let _68_23091 = (Support.List.map2 (fun ( v ) ( a ) -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_23088 = (let _68_23087 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_68_23087, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23088))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(let _68_23090 = (let _68_23089 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_68_23089, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23090))
end)) vars indices)
in (Support.Prims.pipe_right _68_23091 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _68_23096 = (let _68_23095 = (let _68_23094 = (let _68_23093 = (let _68_23092 = (mk_data_tester env l xx)
in (_68_23092, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_23093))
in (out, _68_23094))
in (Microsoft_FStar_ToSMT_Term.mkOr _68_23095))
in (_68_23096, (Support.List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_50_2332) with
| (data_ax, decls) -> begin
(let _50_2335 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2335) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _68_23097 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _68_23097 xx tapp))
in (let _68_23104 = (let _68_23103 = (let _68_23102 = (let _68_23101 = (let _68_23100 = (let _68_23099 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _68_23098 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _68_23099, _68_23098)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23100))
in (_68_23101, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23102))
in (_68_23103)::[])
in (Support.List.append decls _68_23104)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _50_2347 = (match ((let _68_23105 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _68_23105.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, res)) -> begin
(true, bs, res)
end
| _ -> begin
(false, [], k)
end)
in (match (_50_2347) with
| (is_kind_arrow, formals, res) -> begin
(let _50_2354 = (encode_binders None formals env)
in (match (_50_2354) with
| (vars, guards, env', binder_decls, _) -> begin
(let projection_axioms = (fun ( tapp ) ( vars ) -> (match ((Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.find_opt (fun ( _50_20 ) -> (match (_50_20) with
| Microsoft_FStar_Absyn_Syntax.Projector (_) -> begin
true
end
| _ -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inl (a)))) -> begin
(let rec projectee = (fun ( i ) ( _50_21 ) -> (match (_50_21) with
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
in (let _50_2393 = (match ((Support.Microsoft.FStar.Util.first_N projectee_pos vars)) with
| (_, xx::suffix) -> begin
(xx, suffix)
end
| _ -> begin
(failwith ("impossible"))
end)
in (match (_50_2393) with
| (xx, suffix) -> begin
(let dproj_app = (let _68_23119 = (let _68_23118 = (let _68_23117 = (mk_typ_projector_name d a)
in (let _68_23116 = (let _68_23115 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_68_23115)::[])
in (_68_23117, _68_23116)))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23118))
in (mk_ApplyT _68_23119 suffix))
in (let _68_23124 = (let _68_23123 = (let _68_23122 = (let _68_23121 = (let _68_23120 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _68_23120))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23121))
in (_68_23122, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23123))
in (_68_23124)::[]))
end))))
end
| _ -> begin
[]
end))
in (let pretype_axioms = (fun ( tapp ) ( vars ) -> (let _50_2402 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_50_2402) with
| (xxsym, xx) -> begin
(let _50_2405 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2405) with
| (ffsym, ff) -> begin
(let xx_has_type = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _68_23137 = (let _68_23136 = (let _68_23135 = (let _68_23134 = (let _68_23133 = (let _68_23132 = (let _68_23131 = (let _68_23130 = (let _68_23129 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _68_23129))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23130))
in (xx_has_type, _68_23131))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23132))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _68_23133))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23134))
in (_68_23135, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23136))
in (_68_23137)::[]))
end))
end)))
in (let _50_2410 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2410) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _68_23139 = (let _68_23138 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _68_23138))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23139))
in (let _50_2435 = (let tname_decl = (let _68_23143 = (let _68_23142 = (Support.Prims.pipe_right vars (Support.List.map (fun ( _50_2416 ) -> (match (_50_2416) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))))
in (let _68_23141 = (varops.next_id ())
in (tname, _68_23142, Microsoft_FStar_ToSMT_Term.Type_sort, _68_23141)))
in (constructor_or_logic_type_decl _68_23143))
in (let _50_2432 = (match (vars) with
| [] -> begin
(let _68_23147 = (let _68_23146 = (let _68_23145 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (Support.Prims.pipe_left (fun ( _68_23144 ) -> Some (_68_23144)) _68_23145))
in (push_free_tvar env t tname _68_23146))
in ([], _68_23147))
end
| _ -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _68_23148 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _68_23148))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match (((not (is_logical)) && (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _50_22 ) -> (match (_50_22) with
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
in (let name_tok_corr = (let _68_23153 = (let _68_23152 = (let _68_23151 = (let _68_23150 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _68_23150))
in (Microsoft_FStar_ToSMT_Term.mkForall' _68_23151))
in (_68_23152, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23153))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_50_2432) with
| (tok_decls, env) -> begin
((Support.List.append tname_decl tok_decls), env)
end)))
in (match (_50_2435) with
| (decls, env) -> begin
(let kindingAx = (let _50_2438 = (encode_knd res env' tapp)
in (match (_50_2438) with
| (k, decls) -> begin
(let karr = (match (is_kind_arrow) with
| true -> begin
(let _68_23157 = (let _68_23156 = (let _68_23155 = (let _68_23154 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _68_23154))
in (_68_23155, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23156))
in (_68_23157)::[])
end
| false -> begin
[]
end)
in (let _68_23163 = (let _68_23162 = (let _68_23161 = (let _68_23160 = (let _68_23159 = (let _68_23158 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _68_23158))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23159))
in (_68_23160, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23161))
in (_68_23162)::[])
in (Support.List.append (Support.List.append decls karr) _68_23163)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _68_23164 = (projection_axioms tapp vars)
in (Support.List.append kindingAx _68_23164))
end
| false -> begin
(let _68_23171 = (let _68_23169 = (let _68_23167 = (let _68_23165 = (primitive_type_axioms t tname tapp)
in (Support.List.append kindingAx _68_23165))
in (let _68_23166 = (inversion_axioms tapp vars)
in (Support.List.append _68_23167 _68_23166)))
in (let _68_23168 = (projection_axioms tapp vars)
in (Support.List.append _68_23169 _68_23168)))
in (let _68_23170 = (pretype_axioms tapp vars)
in (Support.List.append _68_23171 _68_23170)))
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
(let _50_2469 = (new_term_constant_and_tok_from_lid env d)
in (match (_50_2469) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _50_2478 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(f, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_50_2478) with
| (formals, t_res) -> begin
(let _50_2481 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2481) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _50_2488 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_50_2488) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (Support.Prims.pipe_right names (Support.List.map (fun ( _50_23 ) -> (match (_50_23) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _68_23173 = (mk_typ_projector_name d a)
in (_68_23173, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _68_23174 = (mk_term_projector_name d x)
in (_68_23174, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _68_23176 = (let _68_23175 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _68_23175))
in (Support.Prims.pipe_right _68_23176 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _50_2502 = (encode_typ_pred' None t env ddtok_tm)
in (match (_50_2502) with
| (tok_typing, decls3) -> begin
(let _50_2509 = (encode_binders (Some (s_fuel_tm)) formals env)
in (match (_50_2509) with
| (vars', guards', env'', decls_formals, _) -> begin
(let _50_2514 = (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred' (Some (fuel_tm)) t_res env'' dapp)))
in (match (_50_2514) with
| (ty_pred', decls_pred) -> begin
(let guard' = (Microsoft_FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _ -> begin
(let _68_23178 = (let _68_23177 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _68_23177))
in (_68_23178)::[])
end)
in (let encode_elim = (fun ( _50_2521 ) -> (match (()) with
| () -> begin
(let _50_2524 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_50_2524) with
| (head, args) -> begin
(match ((let _68_23181 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _68_23181.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _50_2530 = (encode_args args env')
in (match (_50_2530) with
| (encoded_args, arg_decls) -> begin
(let _50_2554 = (Support.List.fold_left (fun ( _50_2534 ) ( arg ) -> (match (_50_2534) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _50_2542 = (let _68_23184 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _68_23184))
in (match (_50_2542) with
| (_, tv, env) -> begin
(let _68_23186 = (let _68_23185 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_68_23185)::eqns)
in (env, (tv)::arg_vars, _68_23186))
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _50_2549 = (let _68_23187 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _68_23187))
in (match (_50_2549) with
| (_, xv, env) -> begin
(let _68_23189 = (let _68_23188 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_68_23188)::eqns)
in (env, (xv)::arg_vars, _68_23189))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_50_2554) with
| (_, arg_vars, eqns) -> begin
(let arg_vars = (Support.List.rev arg_vars)
in (let ty = (Microsoft_FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (Support.List.map Microsoft_FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _68_23196 = (let _68_23195 = (let _68_23194 = (let _68_23193 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _68_23192 = (let _68_23191 = (let _68_23190 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards))
in (ty_pred, _68_23190))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23191))
in ((ty_pred)::[], _68_23193, _68_23192)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23194))
in (_68_23195, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23196))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _68_23197 = (varops.fresh "x")
in (_68_23197, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _68_23206 = (let _68_23205 = (let _68_23204 = (let _68_23203 = (let _68_23198 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_68_23198)::[])
in (let _68_23202 = (let _68_23201 = (let _68_23200 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _68_23199 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_68_23200, _68_23199)))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23201))
in (_68_23203, (x)::[], _68_23202)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23204))
in (_68_23205, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23206))))
end
| false -> begin
(let prec = (Support.Prims.pipe_right vars (Support.List.collect (fun ( v ) -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _68_23209 = (let _68_23208 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _68_23208 dapp))
in (_68_23209)::[])
end
| _ -> begin
(failwith ("unexpected sort"))
end))))
in (let _68_23216 = (let _68_23215 = (let _68_23214 = (let _68_23213 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _68_23212 = (let _68_23211 = (let _68_23210 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _68_23210))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23211))
in ((ty_pred)::[], _68_23213, _68_23212)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23214))
in (_68_23215, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23216)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _ -> begin
(let _50_2574 = (let _68_23219 = (let _68_23218 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _68_23217 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" _68_23218 _68_23217)))
in (Microsoft_FStar_Tc_Errors.warn drange _68_23219))
in ([], []))
end)
end))
end))
in (let _50_2578 = (encode_elim ())
in (match (_50_2578) with
| (decls2, elim) -> begin
(let g = (let _68_23244 = (let _68_23243 = (let _68_23228 = (let _68_23227 = (let _68_23226 = (let _68_23225 = (let _68_23224 = (let _68_23223 = (let _68_23222 = (let _68_23221 = (let _68_23220 = (Microsoft_FStar_Absyn_Print.sli d)
in (Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" _68_23220))
in Some (_68_23221))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _68_23222))
in Microsoft_FStar_ToSMT_Term.DeclFun (_68_23223))
in (_68_23224)::[])
in (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) _68_23225))
in (Support.List.append _68_23226 proxy_fresh))
in (Support.List.append _68_23227 decls_formals))
in (Support.List.append _68_23228 decls_pred))
in (let _68_23242 = (let _68_23241 = (let _68_23240 = (let _68_23232 = (let _68_23231 = (let _68_23230 = (let _68_23229 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _68_23229))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23230))
in (_68_23231, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23232))
in (let _68_23239 = (let _68_23238 = (let _68_23237 = (let _68_23236 = (let _68_23235 = (let _68_23234 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _68_23233 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _68_23234, _68_23233)))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23235))
in (_68_23236, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23237))
in (_68_23238)::[])
in (_68_23240)::_68_23239))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_68_23241)
in (Support.List.append _68_23243 _68_23242)))
in (Support.List.append _68_23244 elim))
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
(let _50_2591 = (encode_signature env ses)
in (match (_50_2591) with
| (g, env) -> begin
(let _50_2603 = (Support.Prims.pipe_right g (Support.List.partition (fun ( _50_24 ) -> (match (_50_24) with
| Microsoft_FStar_ToSMT_Term.Assume ((_, Some ("inversion axiom"))) -> begin
false
end
| _ -> begin
true
end))))
in (match (_50_2603) with
| (g', inversions) -> begin
(let _50_2612 = (Support.Prims.pipe_right g' (Support.List.partition (fun ( _50_25 ) -> (match (_50_25) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_) -> begin
true
end
| _ -> begin
false
end))))
in (match (_50_2612) with
| (decls, rest) -> begin
((Support.List.append (Support.List.append decls rest) inversions), env)
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((is_rec, bindings), _, _, quals)) -> begin
(let eta_expand = (fun ( binders ) ( formals ) ( body ) ( t ) -> (let nbinders = (Support.List.length binders)
in (let _50_2631 = (Support.Microsoft.FStar.Util.first_N nbinders formals)
in (match (_50_2631) with
| (formals, extra_formals) -> begin
(let subst = (Support.List.map2 (fun ( formal ) ( binder ) -> (match (((Support.Prims.fst formal), (Support.Prims.fst binder))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _68_23258 = (let _68_23257 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _68_23257))
in Support.Microsoft.FStar.Util.Inl (_68_23258))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _68_23260 = (let _68_23259 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _68_23259))
in Support.Microsoft.FStar.Util.Inr (_68_23260))
end
| _ -> begin
(failwith ("Impossible"))
end)) formals binders)
in (let extra_formals = (let _68_23261 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (Support.Prims.pipe_right _68_23261 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _68_23267 = (let _68_23263 = (let _68_23262 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (Support.Prims.pipe_left Support.Prims.snd _68_23262))
in (body, _68_23263))
in (let _68_23266 = (let _68_23265 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (Support.Prims.pipe_left (fun ( _68_23264 ) -> Some (_68_23264)) _68_23265))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _68_23267 _68_23266 body.Microsoft_FStar_Absyn_Syntax.pos)))
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
(let _50_2683 = (Support.Microsoft.FStar.Util.first_N nformals binders)
in (match (_50_2683) with
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
(let _50_2692 = (eta_expand binders formals body tres)
in (match (_50_2692) with
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
(let _68_23276 = (let _68_23275 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _68_23274 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _68_23275 _68_23274)))
in (failwith (_68_23276)))
end)
end
| _ -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (let _50_2704 = (eta_expand [] formals e tres)
in (match (_50_2704) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _ -> begin
([], e, [], t_norm)
end)
end))
in (Support.Prims.try_with (fun ( _50_2708 ) -> (match (()) with
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
(let _68_23282 = (Support.Prims.pipe_right bindings (Support.List.collect (fun ( lb ) -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _68_23281 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _68_23281 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(raise (Let_rec_unencodeable))
end))))
in (_68_23282, env))
end
| false -> begin
(let _50_2739 = (Support.Prims.pipe_right bindings (Support.List.fold_left (fun ( _50_2726 ) ( lb ) -> (match (_50_2726) with
| (toks, typs, decls, env) -> begin
(let _50_2728 = (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(raise (Let_rec_unencodeable))
end
| false -> begin
()
end)
in (let t_norm = (let _68_23285 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.Prims.pipe_right _68_23285 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _50_2734 = (let _68_23286 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _68_23286 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_50_2734) with
| (tok, decl, env) -> begin
(let _68_23289 = (let _68_23288 = (let _68_23287 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_68_23287, tok))
in (_68_23288)::toks)
in (_68_23289, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_50_2739) with
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
end)))) || (Support.Prims.pipe_right typs (Support.Microsoft.FStar.Util.for_some (fun ( t ) -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (let _68_23292 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_23292)))))))) with
| true -> begin
(decls, env)
end
| false -> begin
(match ((not (is_rec))) with
| true -> begin
(match ((bindings, typs, toks)) with
| ({Microsoft_FStar_Absyn_Syntax.lbname = _; Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _50_2770 = (destruct_bound_function flid t_norm e)
in (match (_50_2770) with
| (binders, body, formals, tres) -> begin
(let _50_2777 = (encode_binders None binders env)
in (match (_50_2777) with
| (vars, guards, env', binder_decls, _) -> begin
(let app = (match (vars) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _ -> begin
(let _68_23294 = (let _68_23293 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _68_23293))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23294))
end)
in (let _50_2784 = (encode_exp body env')
in (match (_50_2784) with
| (body, decls2) -> begin
(let eqn = (let _68_23303 = (let _68_23302 = (let _68_23299 = (let _68_23298 = (let _68_23297 = (let _68_23296 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _68_23295 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_68_23296, _68_23295)))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23297))
in ((app)::[], vars, _68_23298))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23299))
in (let _68_23301 = (let _68_23300 = (Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_68_23300))
in (_68_23302, _68_23301)))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23303))
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
(let fuel = (let _68_23304 = (varops.fresh "fuel")
in (_68_23304, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _50_2804 = (Support.Prims.pipe_right toks (Support.List.fold_left (fun ( _50_2793 ) ( _50_2798 ) -> (match ((_50_2793, _50_2798)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _68_23309 = (let _68_23308 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (Support.Prims.pipe_left (fun ( _68_23307 ) -> Some (_68_23307)) _68_23308))
in (push_free_var env flid gtok _68_23309))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_50_2804) with
| (gtoks, env) -> begin
(let gtoks = (Support.List.rev gtoks)
in (let encode_one_binding = (fun ( env0 ) ( _50_2813 ) ( t_norm ) ( _50_2822 ) -> (match ((_50_2813, _50_2822)) with
| ((flid, f, ftok, g, gtok), {Microsoft_FStar_Absyn_Syntax.lbname = _; Microsoft_FStar_Absyn_Syntax.lbtyp = _; Microsoft_FStar_Absyn_Syntax.lbeff = _; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _50_2827 = (destruct_bound_function flid t_norm e)
in (match (_50_2827) with
| (binders, body, formals, tres) -> begin
(let _50_2834 = (encode_binders None binders env)
in (match (_50_2834) with
| (vars, guards, env', binder_decls, _) -> begin
(let decl_g = (let _68_23320 = (let _68_23319 = (let _68_23318 = (Support.List.map Support.Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_68_23318)
in (g, _68_23319, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_68_23320))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _68_23323 = (let _68_23322 = (let _68_23321 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_68_23321)::vars_tm)
in (g, _68_23322))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23323))
in (let gmax = (let _68_23326 = (let _68_23325 = (let _68_23324 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_68_23324)::vars_tm)
in (g, _68_23325))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23326))
in (let _50_2844 = (encode_exp body env')
in (match (_50_2844) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _68_23335 = (let _68_23334 = (let _68_23331 = (let _68_23330 = (let _68_23329 = (let _68_23328 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _68_23327 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_68_23328, _68_23327)))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23329))
in ((gsapp)::[], (fuel)::vars, _68_23330))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23331))
in (let _68_23333 = (let _68_23332 = (Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_68_23332))
in (_68_23334, _68_23333)))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23335))
in (let eqn_f = (let _68_23339 = (let _68_23338 = (let _68_23337 = (let _68_23336 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _68_23336))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23337))
in (_68_23338, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23339))
in (let eqn_g' = (let _68_23348 = (let _68_23347 = (let _68_23346 = (let _68_23345 = (let _68_23344 = (let _68_23343 = (let _68_23342 = (let _68_23341 = (let _68_23340 = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (_68_23340)::vars_tm)
in (g, _68_23341))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23342))
in (gsapp, _68_23343))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23344))
in ((gsapp)::[], (fuel)::vars, _68_23345))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23346))
in (_68_23347, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23348))
in (let _50_2867 = (let _50_2854 = (encode_binders None formals env0)
in (match (_50_2854) with
| (vars, v_guards, env, binder_decls, _) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _68_23349 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _68_23349 ((fuel)::vars)))
in (let _68_23353 = (let _68_23352 = (let _68_23351 = (let _68_23350 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _68_23350))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23351))
in (_68_23352, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23353)))
in (let _50_2864 = (let _50_2861 = (encode_typ_pred' None tres env gapp)
in (match (_50_2861) with
| (g_typing, d3) -> begin
(let _68_23361 = (let _68_23360 = (let _68_23359 = (let _68_23358 = (let _68_23357 = (let _68_23356 = (let _68_23355 = (let _68_23354 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_68_23354, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _68_23355))
in ((gapp)::[], (fuel)::vars, _68_23356))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23357))
in (_68_23358, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23359))
in (_68_23360)::[])
in (d3, _68_23361))
end))
in (match (_50_2864) with
| (aux_decls, typing_corr) -> begin
((Support.List.append binder_decls aux_decls), (Support.List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_50_2867) with
| (aux_decls, g_typing) -> begin
((Support.List.append (Support.List.append (Support.List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (Support.List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _50_2883 = (let _68_23364 = (Support.List.zip3 gtoks typs bindings)
in (Support.List.fold_left (fun ( _50_2871 ) ( _50_2875 ) -> (match ((_50_2871, _50_2875)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _50_2879 = (encode_one_binding env0 gtok ty bs)
in (match (_50_2879) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _68_23364))
in (match (_50_2883) with
| (decls, eqns, env0) -> begin
(let _50_2892 = (let _68_23366 = (Support.Prims.pipe_right decls Support.List.flatten)
in (Support.Prims.pipe_right _68_23366 (Support.List.partition (fun ( _50_28 ) -> (match (_50_28) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_) -> begin
true
end
| _ -> begin
false
end)))))
in (match (_50_2892) with
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
end)) (fun ( _50_2707 ) -> (match (_50_2707) with
| Let_rec_unencodeable -> begin
(let msg = (let _68_23369 = (Support.Prims.pipe_right bindings (Support.List.map (fun ( lb ) -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (Support.Prims.pipe_right _68_23369 (Support.String.concat " and ")))
in (let decl = Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun ( env ) ( x ) ( t ) ( t_norm ) -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _50_2919 = (encode_free_var env x t t_norm [])
in (match (_50_2919) with
| (decls, env) -> begin
(let _50_2924 = (lookup_lid env x)
in (match (_50_2924) with
| (n, x', _) -> begin
((n, x'), decls, env)
end))
end))
end
| Some ((n, x, _)) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun ( env ) ( lid ) ( t ) -> (let _50_2936 = (encode_function_type_as_formula None t env)
in (match (_50_2936) with
| (form, decls) -> begin
(Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume ((form, Some ((Support.String.strcat "Lemma: " lid.Microsoft_FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun ( env ) ( lid ) ( tt ) ( t_norm ) ( quals ) -> (match (((let _68_23382 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (Support.Prims.pipe_left Support.Prims.op_Negation _68_23382)) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm))) with
| true -> begin
(let _50_2945 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_2945) with
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
in (let _50_2978 = (match ((Microsoft_FStar_Absyn_Util.function_formals t_norm)) with
| Some ((args, comp)) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _68_23384 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _68_23384))
end
| false -> begin
(args, (None, (Microsoft_FStar_Absyn_Util.comp_result comp)))
end)
end
| None -> begin
([], (None, t_norm))
end)
in (match (_50_2978) with
| (formals, (pre_opt, res_t)) -> begin
(let _50_2982 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_2982) with
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
(let _50_2999 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_50_2999) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _68_23397 = (let _68_23396 = (let _68_23395 = (let _68_23394 = (let _68_23393 = (let _68_23392 = (let _68_23391 = (let _68_23390 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _68_23390))
in (vapp, _68_23391))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23392))
in ((vapp)::[], vars, _68_23393))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23394))
in (_68_23395, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23396))
in (_68_23397)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _50_3012 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_50_3012) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _68_23406 = (let _68_23405 = (let _68_23404 = (let _68_23403 = (let _68_23402 = (let _68_23401 = (let _68_23400 = (let _68_23399 = (let _68_23398 = (mk_term_projector_name d f)
in (_68_23398, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23399))
in (vapp, _68_23400))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23401))
in ((vapp)::[], vars, _68_23402))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23403))
in (_68_23404, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23405))
in (_68_23406)::[]))
end))
end
| _ -> begin
[]
end)))))
in (let _50_3022 = (encode_binders None formals env)
in (match (_50_3022) with
| (vars, guards, env', decls1, _) -> begin
(let _50_3031 = (match (pre_opt) with
| None -> begin
(let _68_23407 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_68_23407, decls1))
end
| Some (p) -> begin
(let _50_3028 = (encode_formula p env')
in (match (_50_3028) with
| (g, ds) -> begin
(let _68_23408 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_68_23408, (Support.List.append decls1 ds)))
end))
end)
in (match (_50_3031) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _68_23410 = (let _68_23409 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _68_23409))
in (Microsoft_FStar_ToSMT_Term.mkApp _68_23410))
in (let _50_3062 = (let vname_decl = (let _68_23413 = (let _68_23412 = (Support.Prims.pipe_right formals (Support.List.map (fun ( _50_31 ) -> (match (_50_31) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _ -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _68_23412, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_68_23413))
in (let _50_3049 = (let env = (let _50_3044 = env
in {bindings = _50_3044.bindings; depth = _50_3044.depth; tcenv = _50_3044.tcenv; warn = _50_3044.warn; cache = _50_3044.cache; nolabels = _50_3044.nolabels; use_zfuel_name = _50_3044.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((not ((head_normal env tt)))) with
| true -> begin
(encode_typ_pred' None tt env vtok_tm)
end
| false -> begin
(encode_typ_pred' None t_norm env vtok_tm)
end))
in (match (_50_3049) with
| (tok_typing, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _50_3059 = (match (formals) with
| [] -> begin
(let _68_23417 = (let _68_23416 = (let _68_23415 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Support.Prims.pipe_left (fun ( _68_23414 ) -> Some (_68_23414)) _68_23415))
in (push_free_var env lid vname _68_23416))
in ((Support.List.append decls2 ((tok_typing)::[])), _68_23417))
end
| _ -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _68_23418 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _68_23418))
in (let name_tok_corr = (let _68_23422 = (let _68_23421 = (let _68_23420 = (let _68_23419 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _68_23419))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23420))
in (_68_23421, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23422))
in ((Support.List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_50_3059) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_50_3062) with
| (decls2, env) -> begin
(let _50_3065 = (encode_typ_pred' None res_t env' vapp)
in (match (_50_3065) with
| (ty_pred, decls3) -> begin
(let typingAx = (let _68_23426 = (let _68_23425 = (let _68_23424 = (let _68_23423 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _68_23423))
in (Microsoft_FStar_ToSMT_Term.mkForall _68_23424))
in (_68_23425, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23426))
in (let g = (let _68_23428 = (let _68_23427 = (mk_disc_proj_axioms vapp vars)
in (typingAx)::_68_23427)
in (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) _68_23428))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end)
end))
and encode_signature = (fun ( env ) ( ses ) -> (Support.Prims.pipe_right ses (Support.List.fold_left (fun ( _50_3072 ) ( se ) -> (match (_50_3072) with
| (g, env) -> begin
(let _50_3076 = (encode_sigelt env se)
in (match (_50_3076) with
| (g', env) -> begin
((Support.List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun ( env ) ( bindings ) -> (let encode_binding = (fun ( b ) ( _50_3083 ) -> (match (_50_3083) with
| (decls, env) -> begin
(match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t0)) -> begin
(let _50_3091 = (new_term_constant env x)
in (match (_50_3091) with
| (xxsym, xx, env') -> begin
(let t1 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _50_3095 = (encode_typ_pred' None t1 env xx)
in (match (_50_3095) with
| (t, decls') -> begin
(let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _68_23444 = (let _68_23443 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _68_23442 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _68_23441 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" _68_23443 _68_23442 _68_23441))))
in Some (_68_23444))
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
(let _50_3105 = (new_typ_constant env a)
in (match (_50_3105) with
| (aasym, aa, env') -> begin
(let _50_3108 = (encode_knd k env aa)
in (match (_50_3108) with
| (k, decls') -> begin
(let g = (let _68_23450 = (let _68_23449 = (let _68_23448 = (let _68_23447 = (let _68_23446 = (let _68_23445 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_68_23445))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _68_23446))
in Microsoft_FStar_ToSMT_Term.DeclFun (_68_23447))
in (_68_23448)::[])
in (Support.List.append _68_23449 decls'))
in (Support.List.append _68_23450 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((Support.List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((x, t)) -> begin
(let t_norm = (whnf env t)
in (let _50_3117 = (encode_free_var env x t t_norm [])
in (match (_50_3117) with
| (g, env') -> begin
((Support.List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _50_3122 = (encode_sigelt env se)
in (match (_50_3122) with
| (g, env') -> begin
((Support.List.append decls g), env')
end))
end)
end))
in (Support.List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun ( labs ) -> (let prefix = (Support.Prims.pipe_right labs (Support.List.map (fun ( _50_3129 ) -> (match (_50_3129) with
| (l, _, _) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Support.Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (Support.Prims.pipe_right labs (Support.List.collect (fun ( _50_3136 ) -> (match (_50_3136) with
| (l, _, _) -> begin
(let _68_23458 = (Support.Prims.pipe_left (fun ( _68_23454 ) -> Microsoft_FStar_ToSMT_Term.Echo (_68_23454)) (Support.Prims.fst l))
in (let _68_23457 = (let _68_23456 = (let _68_23455 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_68_23455))
in (_68_23456)::[])
in (_68_23458)::_68_23457))
end))))
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun ( tcenv ) -> (let _68_23463 = (let _68_23462 = (let _68_23461 = (Support.Microsoft.FStar.Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _68_23461; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_68_23462)::[])
in (Support.ST.op_Colon_Equals last_env _68_23463)))

let get_env = (fun ( tcenv ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(failwith ("No env; call init first!"))
end
| e::_ -> begin
(let _50_3145 = e
in {bindings = _50_3145.bindings; depth = _50_3145.depth; tcenv = tcenv; warn = _50_3145.warn; cache = _50_3145.cache; nolabels = _50_3145.nolabels; use_zfuel_name = _50_3145.use_zfuel_name; encode_non_total_function_typ = _50_3145.encode_non_total_function_typ})
end))

let set_env = (fun ( env ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(failwith ("Empty env stack"))
end
| _::tl -> begin
(Support.ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun ( _50_3153 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(failwith ("Empty env stack"))
end
| hd::tl -> begin
(let _50_3158 = (Microsoft_FStar_ToSMT_Term.push ())
in (let refs = (Support.Microsoft.FStar.Util.smap_copy hd.cache)
in (let top = (let _50_3161 = hd
in {bindings = _50_3161.bindings; depth = _50_3161.depth; tcenv = _50_3161.tcenv; warn = _50_3161.warn; cache = refs; nolabels = _50_3161.nolabels; use_zfuel_name = _50_3161.use_zfuel_name; encode_non_total_function_typ = _50_3161.encode_non_total_function_typ})
in (Support.ST.op_Colon_Equals last_env ((top)::(hd)::tl)))))
end)
end))

let pop_env = (fun ( _50_3164 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(failwith ("Popping an empty stack"))
end
| _::tl -> begin
(let _50_3170 = (Microsoft_FStar_ToSMT_Term.pop ())
in (Support.ST.op_Colon_Equals last_env tl))
end)
end))

let mark_env = (fun ( _50_3172 ) -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun ( _50_3173 ) -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun ( _50_3174 ) -> (match (()) with
| () -> begin
(let _50_3175 = (Microsoft_FStar_ToSMT_Term.commit_mark ())
in (match ((Support.ST.read last_env)) with
| hd::_::tl -> begin
(Support.ST.op_Colon_Equals last_env ((hd)::tl))
end
| _ -> begin
(failwith ("Impossible"))
end))
end))

let init = (fun ( tcenv ) -> (let _50_3186 = (init_env tcenv)
in (let _50_3188 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun ( msg ) -> (let _50_3191 = (push_env ())
in (let _50_3193 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun ( msg ) -> (let _50_3196 = (let _68_23484 = (pop_env ())
in (Support.Prims.pipe_left Support.Prims.ignore _68_23484))
in (let _50_3198 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun ( msg ) -> (let _50_3201 = (mark_env ())
in (let _50_3203 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun ( msg ) -> (let _50_3206 = (reset_mark_env ())
in (let _50_3208 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun ( msg ) -> (let _50_3211 = (commit_mark_env ())
in (let _50_3213 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun ( tcenv ) ( se ) -> (let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _68_23498 = (let _68_23497 = (let _68_23496 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.String.strcat "encoding sigelt " _68_23496))
in Microsoft_FStar_ToSMT_Term.Caption (_68_23497))
in (_68_23498)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _50_3222 = (encode_sigelt env se)
in (match (_50_3222) with
| (decls, env) -> begin
(let _50_3223 = (set_env env)
in (let _68_23499 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _68_23499)))
end)))))

let encode_modul = (fun ( tcenv ) ( modul ) -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _50_3228 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_23504 = (Support.Prims.pipe_right (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name _68_23504))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _50_3235 = (encode_signature (let _50_3231 = env
in {bindings = _50_3231.bindings; depth = _50_3231.depth; tcenv = _50_3231.tcenv; warn = false; cache = _50_3231.cache; nolabels = _50_3231.nolabels; use_zfuel_name = _50_3231.use_zfuel_name; encode_non_total_function_typ = _50_3231.encode_non_total_function_typ}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_50_3235) with
| (decls, env) -> begin
(let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let msg = (Support.String.strcat "Externals for " name)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _50_3241 = (set_env (let _50_3239 = env
in {bindings = _50_3239.bindings; depth = _50_3239.depth; tcenv = _50_3239.tcenv; warn = true; cache = _50_3239.cache; nolabels = _50_3239.nolabels; use_zfuel_name = _50_3239.use_zfuel_name; encode_non_total_function_typ = _50_3239.encode_non_total_function_typ}))
in (let _50_3243 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun ( tcenv ) ( q ) -> (let _50_3248 = (let _68_23513 = (let _68_23512 = (let _68_23511 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _68_23511))
in (Support.Microsoft.FStar.Util.format1 "Starting query at %s" _68_23512))
in (push _68_23513))
in (let pop = (fun ( _50_3251 ) -> (match (()) with
| () -> begin
(let _68_23518 = (let _68_23517 = (let _68_23516 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _68_23516))
in (Support.Microsoft.FStar.Util.format1 "Ending query at %s" _68_23517))
in (pop _68_23518))
end))
in (let _50_3281 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun ( bs ) ( b ) -> (b)::bs) [])
in (let _50_3264 = (let _68_23522 = (Support.List.filter (fun ( _50_32 ) -> (match (_50_32) with
| Microsoft_FStar_Tc_Env.Binding_sig (_) -> begin
false
end
| _ -> begin
true
end)) bindings)
in (encode_env_bindings env _68_23522))
in (match (_50_3264) with
| (env_decls, env) -> begin
(let _50_3265 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _68_23523 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" _68_23523))
end
| false -> begin
()
end)
in (let _50_3270 = (encode_formula_with_labels q env)
in (match (_50_3270) with
| (phi, labels, qdecls) -> begin
(let _50_3273 = (encode_labels labels)
in (match (_50_3273) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Support.List.append (Support.List.append env_decls label_prefix) qdecls)
in (let qry = (let _68_23525 = (let _68_23524 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_68_23524, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23525))
in (let suffix = (Support.List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_50_3281) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume (({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.False, _)); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}, _)) -> begin
(let _50_3296 = (pop ())
in ())
end
| _ when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
(let _50_3300 = (pop ())
in ())
end
| Microsoft_FStar_ToSMT_Term.Assume ((q, _)) -> begin
(let fresh = ((Support.String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _50_3308 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun ( p ) ( _50_3314 ) -> (match (_50_3314) with
| (n, i) -> begin
(let _68_23547 = (let _68_23546 = (let _68_23531 = (let _68_23530 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" _68_23530))
in Microsoft_FStar_ToSMT_Term.Caption (_68_23531))
in (let _68_23545 = (let _68_23544 = (let _68_23536 = (let _68_23535 = (let _68_23534 = (let _68_23533 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _68_23532 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_68_23533, _68_23532)))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23534))
in (_68_23535, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23536))
in (let _68_23543 = (let _68_23542 = (let _68_23541 = (let _68_23540 = (let _68_23539 = (let _68_23538 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _68_23537 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_68_23538, _68_23537)))
in (Microsoft_FStar_ToSMT_Term.mkEq _68_23539))
in (_68_23540, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_23541))
in (_68_23542)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_68_23544)::_68_23543))
in (_68_23546)::_68_23545))
in (Support.List.append _68_23547 suffix))
end))
in (let check = (fun ( p ) -> (let initial_config = (let _68_23551 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _68_23550 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_68_23551, _68_23550)))
in (let alt_configs = (let _68_23570 = (let _68_23569 = (match (((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel))) with
| true -> begin
(let _68_23554 = (let _68_23553 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _68_23552 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_68_23553, _68_23552)))
in (_68_23554)::[])
end
| false -> begin
[]
end)
in (let _68_23568 = (let _68_23567 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2) > (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _68_23557 = (let _68_23556 = ((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2)
in (let _68_23555 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_68_23556, _68_23555)))
in (_68_23557)::[])
end
| false -> begin
[]
end)
in (let _68_23566 = (let _68_23565 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) > (Support.ST.read Microsoft_FStar_Options.initial_fuel)) && ((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel)))) with
| true -> begin
(let _68_23560 = (let _68_23559 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _68_23558 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_68_23559, _68_23558)))
in (_68_23560)::[])
end
| false -> begin
[]
end)
in (let _68_23564 = (let _68_23563 = (match (((Support.ST.read Microsoft_FStar_Options.min_fuel) < (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _68_23562 = (let _68_23561 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (_68_23561, 1))
in (_68_23562)::[])
end
| false -> begin
[]
end)
in (_68_23563)::[])
in (_68_23565)::_68_23564))
in (_68_23567)::_68_23566))
in (_68_23569)::_68_23568))
in (Support.List.flatten _68_23570))
in (let report = (fun ( _50_3322 ) -> (match (_50_3322) with
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
(let _68_23582 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _68_23582 (cb p [])))
end
| _ -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(let _68_23584 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _68_23584 (fun ( _50_3343 ) -> (match (_50_3343) with
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
and cb = (fun ( p ) ( alt ) ( _50_3351 ) -> (match (_50_3351) with
| (ok, errs) -> begin
(match (ok) with
| true -> begin
()
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _68_23588 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _68_23588 (cb p alt_configs))))))))
in (let process_query = (fun ( q ) -> (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let _50_3356 = (let _68_23594 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _68_23594 q))
in (match (_50_3356) with
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
in (let _50_3357 = (match ((Support.ST.read Microsoft_FStar_Options.admit_smt_queries)) with
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
in (let _50_3362 = (push "query")
in (let _50_3369 = (encode_formula_with_labels q env)
in (match (_50_3369) with
| (f, _, _) -> begin
(let _50_3370 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _)) -> begin
true
end
| _ -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = commit_mark; Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun ( _50_3379 ) -> ()); Microsoft_FStar_Tc_Env.push = (fun ( _50_3381 ) -> ()); Microsoft_FStar_Tc_Env.pop = (fun ( _50_3383 ) -> ()); Microsoft_FStar_Tc_Env.mark = (fun ( _50_3385 ) -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun ( _50_3387 ) -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun ( _50_3389 ) -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun ( _50_3391 ) ( _50_3393 ) -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun ( _50_3395 ) ( _50_3397 ) -> ()); Microsoft_FStar_Tc_Env.solve = (fun ( _50_3399 ) ( _50_3401 ) -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun ( _50_3403 ) ( _50_3405 ) -> false); Microsoft_FStar_Tc_Env.finish = (fun ( _50_3407 ) -> ()); Microsoft_FStar_Tc_Env.refresh = (fun ( _50_3408 ) -> ())}





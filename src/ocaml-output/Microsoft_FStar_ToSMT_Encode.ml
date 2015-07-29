
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

let mk_typ_projector_name = (fun ( lid ) ( a ) -> (let _52_17987 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.Prims.pipe_left escape _52_17987)))

let mk_term_projector_name = (fun ( lid ) ( a ) -> (let a = (let _52_17992 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _52_17992; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _52_17993 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.Prims.pipe_left escape _52_17993))))

let primitive_projector_by_pos = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _50_61 ) -> (match (()) with
| () -> begin
(let _52_18003 = (let _52_18002 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" _52_18002 lid.Microsoft_FStar_Absyn_Syntax.str))
in (failwith (_52_18003)))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _52_18004 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _52_18004.Microsoft_FStar_Absyn_Syntax.n)) with
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

let mk_term_projector_name_by_pos = (fun ( lid ) ( i ) -> (let _52_18010 = (let _52_18009 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _52_18009))
in (Support.Prims.pipe_left escape _52_18010)))

let mk_typ_projector = (fun ( lid ) ( a ) -> (let _52_18016 = (let _52_18015 = (mk_typ_projector_name lid a)
in (_52_18015, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _52_18016)))

let mk_term_projector = (fun ( lid ) ( a ) -> (let _52_18022 = (let _52_18021 = (mk_term_projector_name lid a)
in (_52_18021, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _52_18022)))

let mk_term_projector_by_pos = (fun ( lid ) ( i ) -> (let _52_18028 = (let _52_18027 = (mk_term_projector_name_by_pos lid i)
in (_52_18027, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _52_18028)))

let mk_data_tester = (fun ( env ) ( l ) ( x ) -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let is_Mkvarops_t = (fun ( _ ) -> (failwith ("Not yet implemented")))

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun ( _50_100 ) -> (match (()) with
| () -> begin
(let _52_18132 = (Support.Microsoft.FStar.Util.smap_create 100)
in (let _52_18131 = (Support.Microsoft.FStar.Util.smap_create 100)
in (_52_18132, _52_18131)))
end))
in (let scopes = (let _52_18134 = (let _52_18133 = (new_scope ())
in (_52_18133)::[])
in (Support.Microsoft.FStar.Util.mk_ref _52_18134))
in (let mk_unique = (fun ( y ) -> (let y = (escape y)
in (let y = (match ((let _52_18138 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _52_18138 (fun ( _50_108 ) -> (match (_50_108) with
| (names, _) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_) -> begin
(let _50_113 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _52_18140 = (let _52_18139 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _52_18139))
in (Support.String.strcat (Support.String.strcat y "__") _52_18140)))
end)
in (let top_scope = (let _52_18142 = (let _52_18141 = (Support.ST.read scopes)
in (Support.List.hd _52_18141))
in (Support.Prims.pipe_left Support.Prims.fst _52_18142))
in (let _50_117 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun ( pp ) ( rn ) -> (let _52_18148 = (let _52_18147 = (Support.Prims.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.String.strcat _52_18147 "__"))
in (Support.String.strcat _52_18148 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun ( lid ) -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun ( _50_125 ) -> (match (()) with
| () -> begin
(let _50_126 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
end))
in (let fresh = (fun ( pfx ) -> (let _52_18156 = (let _52_18155 = (next_id ())
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int _52_18155))
in (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx _52_18156)))
in (let string_const = (fun ( s ) -> (match ((let _52_18160 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _52_18160 (fun ( _50_135 ) -> (match (_50_135) with
| (_, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _52_18161 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxString _52_18161))
in (let top_scope = (let _52_18163 = (let _52_18162 = (Support.ST.read scopes)
in (Support.List.hd _52_18162))
in (Support.Prims.pipe_left Support.Prims.snd _52_18163))
in (let _50_142 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun ( _50_145 ) -> (match (()) with
| () -> begin
(let _52_18168 = (let _52_18167 = (new_scope ())
in (let _52_18166 = (Support.ST.read scopes)
in (_52_18167)::_52_18166))
in (Support.ST.op_Colon_Equals scopes _52_18168))
end))
in (let pop = (fun ( _50_147 ) -> (match (()) with
| () -> begin
(let _52_18172 = (let _52_18171 = (Support.ST.read scopes)
in (Support.List.tl _52_18171))
in (Support.ST.op_Colon_Equals scopes _52_18172))
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

let unmangle = (fun ( x ) -> (let _52_18188 = (let _52_18187 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _52_18186 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_52_18187, _52_18186)))
in (Microsoft_FStar_Absyn_Util.mkbvd _52_18188)))

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

let print_env = (fun ( e ) -> (let _52_18246 = (Support.Prims.pipe_right e.bindings (Support.List.map (fun ( _50_2 ) -> (match (_50_2) with
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
in (Support.Prims.pipe_right _52_18246 (Support.String.concat ", "))))

let lookup_binding = (fun ( env ) ( f ) -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun ( env ) ( t ) -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_18256 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_52_18256))
end
| false -> begin
None
end))

let fresh_fvar = (fun ( x ) ( s ) -> (let xsym = (varops.fresh x)
in (let _52_18261 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _52_18261))))

let gen_term_var = (fun ( env ) ( x ) -> (let ysym = (let _52_18266 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@x" _52_18266))
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
(let _52_18281 = (let _52_18280 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" _52_18280))
in (failwith (_52_18281)))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun ( env ) ( x ) -> (let ysym = (let _52_18286 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@a" _52_18286))
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
(let _52_18301 = (let _52_18300 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" _52_18300))
in (failwith (_52_18301)))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _52_18312 = (let _50_290 = env
in (let _52_18311 = (let _52_18310 = (let _52_18309 = (let _52_18308 = (let _52_18307 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.Prims.pipe_left (fun ( _52_18306 ) -> Some (_52_18306)) _52_18307))
in (x, fname, _52_18308, None))
in Binding_fvar (_52_18309))
in (_52_18310)::env.bindings)
in {bindings = _52_18311; depth = _50_290.depth; tcenv = _50_290.tcenv; warn = _50_290.warn; cache = _50_290.cache; nolabels = _50_290.nolabels; use_zfuel_name = _50_290.use_zfuel_name; encode_non_total_function_typ = _50_290.encode_non_total_function_typ}))
in (fname, ftok, _52_18312)))))

let try_lookup_lid = (fun ( env ) ( a ) -> (lookup_binding env (fun ( _50_5 ) -> (match (_50_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _ -> begin
None
end))))

let lookup_lid = (fun ( env ) ( a ) -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _52_18323 = (let _52_18322 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _52_18322))
in (failwith (_52_18323)))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _50_312 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _50_312.depth; tcenv = _50_312.tcenv; warn = _50_312.warn; cache = _50_312.cache; nolabels = _50_312.nolabels; use_zfuel_name = _50_312.use_zfuel_name; encode_non_total_function_typ = _50_312.encode_non_total_function_typ}))

let push_zfuel_name = (fun ( env ) ( x ) ( f ) -> (let _50_321 = (lookup_lid env x)
in (match (_50_321) with
| (t1, t2, _) -> begin
(let t3 = (let _52_18340 = (let _52_18339 = (let _52_18338 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_52_18338)::[])
in (f, _52_18339))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18340))
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
(match ((let _52_18344 = (let _52_18343 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (Support.Prims.pipe_right _52_18343 Support.Prims.fst))
in (Support.Microsoft.FStar.Util.starts_with _52_18344 "fuel"))) with
| true -> begin
(let _52_18345 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _52_18345 fuel))
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
(let _52_18347 = (let _52_18346 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _52_18346))
in (failwith (_52_18347)))
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
in (let _52_18362 = (let _50_387 = env
in (let _52_18361 = (let _52_18360 = (let _52_18359 = (let _52_18358 = (let _52_18357 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.Prims.pipe_left (fun ( _52_18356 ) -> Some (_52_18356)) _52_18357))
in (x, fname, _52_18358))
in Binding_ftvar (_52_18359))
in (_52_18360)::env.bindings)
in {bindings = _52_18361; depth = _50_387.depth; tcenv = _50_387.tcenv; warn = _50_387.warn; cache = _50_387.cache; nolabels = _50_387.nolabels; use_zfuel_name = _50_387.use_zfuel_name; encode_non_total_function_typ = _50_387.encode_non_total_function_typ}))
in (fname, ftok, _52_18362)))))

let lookup_tlid = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _50_6 ) -> (match (_50_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _ -> begin
None
end)))) with
| None -> begin
(let _52_18369 = (let _52_18368 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _52_18368))
in (failwith (_52_18369)))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _50_406 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _50_406.depth; tcenv = _50_406.tcenv; warn = _50_406.warn; cache = _50_406.cache; nolabels = _50_406.nolabels; use_zfuel_name = _50_406.use_zfuel_name; encode_non_total_function_typ = _50_406.encode_non_total_function_typ}))

let lookup_free_tvar = (fun ( env ) ( a ) -> (match ((let _52_18380 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _52_18380 Support.Prims.snd))) with
| None -> begin
(let _52_18382 = (let _52_18381 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _52_18381))
in (failwith (_52_18382)))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun ( env ) ( a ) -> (let _52_18385 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _52_18385 Support.Prims.fst)))

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
(let _52_18401 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Prims.pipe_right _52_18401 Support.Option.isNone))
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

let trivial_post = (fun ( t ) -> (let _52_18423 = (let _52_18422 = (let _52_18420 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_52_18420)::[])
in (let _52_18421 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_52_18422, _52_18421)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _52_18423 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun ( e ) ( vars ) -> (Support.Prims.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _52_18430 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _52_18430))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _52_18431 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _52_18431))
end
| _ -> begin
(let _52_18432 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _52_18432))
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
(let _52_18445 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _52_18445))
end
| _ -> begin
(let _52_18446 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _52_18446))
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
| (Microsoft_FStar_ToSMT_Term.App ((app, f::{Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.FreeV (y); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}::[])), x::xs) when (let _52_18465 = (Microsoft_FStar_ToSMT_Term.fv_eq x y)
in ((is_app app) && _52_18465)) -> begin
(aux f xs)
end
| (Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var (f), args)), _) -> begin
(match ((let _52_18468 = (Support.List.forall2 (fun ( a ) ( v ) -> (match (a.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (fv) -> begin
(Microsoft_FStar_ToSMT_Term.fv_eq fv v)
end
| _ -> begin
false
end)) args vars)
in (((Support.List.length args) = (Support.List.length vars)) && _52_18468))) with
| true -> begin
(tok_of_name env f)
end
| false -> begin
None
end)
end
| (_, []) -> begin
(let fvs = (Microsoft_FStar_ToSMT_Term.free_variables t)
in (match ((Support.Prims.pipe_right fvs (Support.List.for_all (fun ( fv ) -> (let _52_18470 = (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_ToSMT_Term.fv_eq fv) vars)
in (not (_52_18470))))))) with
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
(let _52_18505 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _52_18505))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _52_18506 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _52_18506))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _52_18507 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _52_18507))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _52_18511 = (let _52_18510 = (let _52_18509 = (let _52_18508 = (Microsoft_FStar_ToSMT_Term.mkInteger' i)
in (Microsoft_FStar_ToSMT_Term.boxInt _52_18508))
in (_52_18509)::[])
in ("Int32.Int32", _52_18510))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18511))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _)) -> begin
(let _52_18512 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_bytes bytes)
in (varops.string_const _52_18512))
end
| c -> begin
(let _52_18514 = (let _52_18513 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" _52_18513))
in (failwith (_52_18514)))
end))

let as_function_typ = (fun ( env ) ( t0 ) -> (let rec aux = (fun ( norm ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
(let _52_18523 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _52_18523))
end
| _ -> begin
(match (norm) with
| true -> begin
(let _52_18524 = (whnf env t)
in (aux false _52_18524))
end
| false -> begin
(let _52_18527 = (let _52_18526 = (Support.Microsoft.FStar.Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_18525 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Support.Microsoft.FStar.Util.format2 "(%s) Expected a function typ; got %s" _52_18526 _52_18525)))
in (failwith (_52_18527)))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun ( k ) ( env ) -> (match ((let _52_18559 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _52_18559.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k0)) -> begin
(let _50_630 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _52_18561 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _52_18560 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _52_18561 _52_18560)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _)) -> begin
(let _52_18563 = (let _52_18562 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _52_18562))
in (_52_18563, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, kbody)) -> begin
(let tsym = (let _52_18564 = (varops.fresh "t")
in (_52_18564, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let t = (Microsoft_FStar_ToSMT_Term.mkFreeV tsym)
in (let _50_649 = (encode_binders None bs env)
in (match (_50_649) with
| (vars, guards, env', decls, _) -> begin
(let app = (mk_ApplyT t vars)
in (let _50_653 = (encode_knd kbody env' app)
in (match (_50_653) with
| (kbody, decls') -> begin
(let k_interp = (let _52_18568 = (let _52_18567 = (let _52_18566 = (let _52_18565 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_52_18565, kbody))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_18566))
in ((app)::[], vars, _52_18567))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_18568))
in (let cvars = (let _52_18570 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (Support.Prims.pipe_right _52_18570 (Support.List.filter (fun ( _50_658 ) -> (match (_50_658) with
| (x, _) -> begin
(x <> (Support.Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((k', sorts, _)) -> begin
(let _52_18573 = (let _52_18572 = (let _52_18571 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _52_18571))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18572))
in (_52_18573, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _52_18574 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_52_18574))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _52_18576 = (let _52_18575 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _52_18575))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18576))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _52_18585 = (let _52_18584 = (let _52_18583 = (let _52_18582 = (let _52_18581 = (let _52_18580 = (let _52_18579 = (let _52_18578 = (let _52_18577 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _52_18577))
in (_52_18578, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _52_18579))
in (t_has_k, _52_18580))
in (Microsoft_FStar_ToSMT_Term.mkIff _52_18581))
in ((t_has_k)::[], (tsym)::cvars, _52_18582))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_18583))
in (_52_18584, Some ((Support.String.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18585))
in (let k_decls = (Support.List.append (Support.List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _50_676 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end))))
end)))
end))))
end
| _ -> begin
(let _52_18587 = (let _52_18586 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" _52_18586))
in (failwith (_52_18587)))
end))
and encode_knd = (fun ( k ) ( env ) ( t ) -> (let _50_685 = (encode_knd_term k env)
in (match (_50_685) with
| (k, decls) -> begin
(let _52_18591 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_52_18591, decls))
end)))
and encode_binders = (fun ( fuel_opt ) ( bs ) ( env ) -> (let _50_689 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_18595 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" _52_18595))
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
(let _52_18599 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _52_18598 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _52_18599 aasym _52_18598)))
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
(let _50_727 = (let _52_18600 = (norm_t env t)
in (encode_typ_pred' fuel_opt _52_18600 env xx))
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
(let _52_18605 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_52_18605, decls))
end))))
and encode_typ_term = (fun ( t ) ( env ) -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _52_18608 = (lookup_typ_var env a)
in (_52_18608, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _52_18609 = (lookup_free_tvar env fv)
in (_52_18609, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
(match ((let _52_18612 = (let _52_18610 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)
in (env.encode_non_total_function_typ && _52_18610))
in (let _52_18611 = (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res)
in (_52_18612 || _52_18611)))) with
| true -> begin
(let _50_765 = (encode_binders None binders env)
in (match (_50_765) with
| (vars, guards, env', decls, _) -> begin
(let fsym = (let _52_18613 = (varops.fresh "f")
in (_52_18613, Microsoft_FStar_ToSMT_Term.Term_sort))
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
(let _52_18614 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_52_18614, decls))
end
| Some (pre) -> begin
(let _50_780 = (encode_formula pre env')
in (match (_50_780) with
| (guard, decls0) -> begin
(let _52_18615 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_52_18615, (Support.List.append decls decls0)))
end))
end)
in (match (_50_783) with
| (guards, guard_decls) -> begin
(let t_interp = (let _52_18617 = (let _52_18616 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _52_18616))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_18617))
in (let cvars = (let _52_18619 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (Support.Prims.pipe_right _52_18619 (Support.List.filter (fun ( _50_788 ) -> (match (_50_788) with
| (x, _) -> begin
(x <> (Support.Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _)) -> begin
(let _52_18622 = (let _52_18621 = (let _52_18620 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _52_18620))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18621))
in (_52_18622, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _52_18623 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_52_18623))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _52_18625 = (let _52_18624 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _52_18624))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18625))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _52_18627 = (let _52_18626 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_52_18626, Some ((Support.String.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18627))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let pre_typing = (let _52_18634 = (let _52_18633 = (let _52_18632 = (let _52_18631 = (let _52_18630 = (let _52_18629 = (let _52_18628 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _52_18628))
in (f_has_t, _52_18629))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_18630))
in ((f_has_t)::[], (fsym)::cvars, _52_18631))
in (mkForall_fuel _52_18632))
in (_52_18633, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18634))
in (let t_interp = (let _52_18638 = (let _52_18637 = (let _52_18636 = (let _52_18635 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t, t_interp))
in ((f_has_t)::[], (fsym)::cvars, _52_18635))
in (mkForall_fuel _52_18636))
in (_52_18637, Some ((Support.String.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18638))
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
in (let t_kinding = (let _52_18640 = (let _52_18639 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_52_18639, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18640))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _52_18647 = (let _52_18646 = (let _52_18645 = (let _52_18644 = (let _52_18643 = (let _52_18642 = (let _52_18641 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _52_18641))
in (f_has_t, _52_18642))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_18643))
in ((f_has_t)::[], (fsym)::[], _52_18644))
in (mkForall_fuel _52_18645))
in (_52_18646, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18647))
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
(let encoding = (let _52_18649 = (let _52_18648 = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t)
in (_52_18648, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _52_18649))
in (let cvars = (let _52_18651 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (Support.Prims.pipe_right _52_18651 (Support.List.filter (fun ( _50_854 ) -> (match (_50_854) with
| (y, _) -> begin
(y <> x)
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _52_18654 = (let _52_18653 = (let _52_18652 = (Support.Prims.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _52_18652))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18653))
in (_52_18654, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _52_18656 = (let _52_18655 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _52_18655))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18656))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _52_18658 = (let _52_18657 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (xfv)::cvars, _52_18657))
in (mkForall_fuel _52_18658))
in (let t_decls = (let _52_18665 = (let _52_18664 = (let _52_18663 = (let _52_18662 = (let _52_18661 = (let _52_18660 = (let _52_18659 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_52_18659))
in (assumption, _52_18660))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18661))
in (_52_18662)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_52_18663)
in (tdecl)::_52_18664)
in (Support.List.append (Support.List.append decls decls') _52_18665))
in (let _50_875 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _52_18666 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _52_18666))
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
in (let t = (let _52_18671 = (let _52_18670 = (Support.List.map (fun ( _50_10 ) -> (match (_50_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (head, _52_18670))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18671))
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
(let ttm = (let _52_18672 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _52_18672))
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
(let key_body = (let _52_18676 = (let _52_18675 = (let _52_18674 = (let _52_18673 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_52_18673, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_18674))
in ([], vars, _52_18675))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_18676))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _52_18679 = (let _52_18678 = (let _52_18677 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _52_18677))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18678))
in (_52_18679, []))
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
in (let t = (let _52_18681 = (let _52_18680 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _52_18680))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18681))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _52_18688 = (let _52_18687 = (let _52_18686 = (let _52_18685 = (let _52_18684 = (let _52_18683 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _52_18682 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_52_18683, _52_18682)))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_18684))
in ((app)::[], (Support.List.append vars cvars), _52_18685))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_18686))
in (_52_18687, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18688))
in (let kinding = (let _50_966 = (let _52_18689 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _52_18689 env t))
in (match (_50_966) with
| (ktm, decls'') -> begin
(let _52_18693 = (let _52_18692 = (let _52_18691 = (let _52_18690 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_52_18690, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18691))
in (_52_18692)::[])
in (Support.List.append decls'' _52_18693))
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
(let _52_18694 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _52_18694 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _52_18699 = (let _52_18698 = (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_18697 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _52_18696 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _52_18695 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _52_18698 _52_18697 _52_18696 _52_18695)))))
in (failwith (_52_18699)))
end)))
and encode_exp = (fun ( e ) ( env ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(let _52_18702 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _52_18702 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _)) -> begin
(let _52_18703 = (lookup_free_var env v)
in (_52_18703, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _52_18704 = (encode_const c)
in (_52_18704, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _)) -> begin
(let _50_1006 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)) -> begin
(let e = (let _52_18705 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _52_18705))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun ( _50_1025 ) -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _52_18708 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_52_18708, (decl)::[]))))
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _50_1029 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _52_18709 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_18709))) with
| true -> begin
(fallback ())
end
| false -> begin
(let tfun = (as_function_typ env tfun)
in (match (tfun.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
(let nformals = (Support.List.length bs')
in (match ((let _52_18710 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in ((nformals < (Support.List.length bs)) && _52_18710))) with
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
in (let e = (let _52_18712 = (let _52_18711 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _52_18711))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _52_18712 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
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
(let key_body = (let _52_18716 = (let _52_18715 = (let _52_18714 = (let _52_18713 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_52_18713, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_18714))
in ([], vars, _52_18715))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_18716))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
(let _52_18719 = (let _52_18718 = (let _52_18717 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _52_18717))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18718))
in (_52_18719, []))
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
in (let f = (let _52_18721 = (let _52_18720 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _52_18720))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_18721))
in (let app = (mk_ApplyE f vars)
in (let _50_1079 = (encode_typ_pred' None tfun env f)
in (match (_50_1079) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _52_18723 = (let _52_18722 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_52_18722, Some ((Support.String.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18723))
in (let interp_f = (let _52_18730 = (let _52_18729 = (let _52_18728 = (let _52_18727 = (let _52_18726 = (let _52_18725 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _52_18724 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_52_18725, _52_18724)))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_18726))
in ((app)::[], (Support.List.append vars cvars), _52_18727))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_18728))
in (_52_18729, Some ((Support.String.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18730))
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
(let _52_18731 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_52_18731, (Support.List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _52_18732 = (whnf_e env e)
in (encode_exp _52_18732 env))
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
in (let ty = (let _52_18735 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.Prims.pipe_right _52_18735 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _50_1167 = (encode_typ_pred' None ty env app_tm)
in (match (_50_1167) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _52_18737 = (let _52_18736 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_52_18736, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_18737))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun ( fv ) -> (let _50_1174 = (lookup_free_var_sym env fv)
in (match (_50_1174) with
| (fname, fuel_args) -> begin
(let tm = (let _52_18743 = (let _52_18742 = (let _52_18741 = (Support.List.map (fun ( _50_11 ) -> (match (_50_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (Support.List.append fuel_args _52_18741))
in (fname, _52_18742))
in (Microsoft_FStar_ToSMT_Term.mkApp' _52_18743))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _50_1181 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _52_18745 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _52_18744 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _52_18745 _52_18744)))
end
| false -> begin
()
end)
in (let head_type = (let _52_18748 = (let _52_18747 = (let _52_18746 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _52_18746))
in (whnf env _52_18747))
in (Support.Prims.pipe_left Microsoft_FStar_Absyn_Util.unrefine _52_18748))
in (let _50_1184 = (match ((Support.Prims.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _52_18751 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _52_18750 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _52_18749 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _52_18751 _52_18750 _52_18749))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _52_18755 = (let _52_18754 = (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_18753 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _52_18752 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" _52_18754 _52_18753 _52_18752))))
in (failwith (_52_18755)))
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
in (let _52_18756 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_52_18756, (decl_e)::[])))))
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
(let _52_18767 = (let _52_18766 = (let _52_18765 = (let _52_18764 = (let _52_18763 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _52_18763))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_18764))
in (guard, _52_18765))
in (Microsoft_FStar_ToSMT_Term.mkAnd _52_18766))
in (_52_18767, decls2))
end))
end)
in (match (_50_1282) with
| (guard, decls2) -> begin
(let _50_1285 = (encode_exp br env)
in (match (_50_1285) with
| (br, decls3) -> begin
(let _52_18768 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_52_18768, (Support.List.append (Support.List.append decls decls2) decls3)))
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
(let _52_18771 = (let _52_18770 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _52_18769 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" _52_18770 _52_18769)))
in (failwith (_52_18771)))
end))))
and encode_pat = (fun ( env ) ( pat ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _ -> begin
(let _52_18774 = (encode_one_pat env pat)
in (_52_18774)::[])
end))
and encode_one_pat = (fun ( env ) ( pat ) -> (let _50_1300 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_18777 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" _52_18777))
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
(let _52_18785 = (let _52_18784 = (encode_const c)
in (scrutinee, _52_18784))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_18785))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (Support.Prims.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _52_18788 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _52_18788))))))
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
(let _52_18796 = (Support.Prims.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _52_18795 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _52_18795))))))
in (Support.Prims.pipe_right _52_18796 Support.List.flatten))
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
and encode_function_type_as_formula = (fun ( induction_on ) ( t ) ( env ) -> (let v_or_t_pat = (fun ( p ) -> (match ((let _52_18810 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _52_18810.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, (Support.Microsoft.FStar.Util.Inl (_), _)::(Support.Microsoft.FStar.Util.Inr (e), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, (Support.Microsoft.FStar.Util.Inl (t), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _ -> begin
(failwith ("Unexpected pattern term"))
end))
in (let rec lemma_pats = (fun ( p ) -> (match ((let _52_18813 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _52_18813.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, _::(Support.Microsoft.FStar.Util.Inr (hd), _)::(Support.Microsoft.FStar.Util.Inr (tl), _)::[])) -> begin
(let _52_18815 = (v_or_t_pat hd)
in (let _52_18814 = (lemma_pats tl)
in (_52_18815)::_52_18814))
end
| _ -> begin
[]
end))
in (let _50_1531 = (match ((let _52_18816 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _52_18816.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _)::(Support.Microsoft.FStar.Util.Inl (post), _)::(Support.Microsoft.FStar.Util.Inr (pats), _)::[] -> begin
(let _52_18817 = (lemma_pats pats)
in (binders, pre, post, _52_18817))
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
(let _50_1554 = (let _52_18819 = (Support.Prims.pipe_right patterns (Support.List.map (fun ( _50_12 ) -> (match (_50_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _50_1550 = env
in {bindings = _50_1550.bindings; depth = _50_1550.depth; tcenv = _50_1550.tcenv; warn = _50_1550.warn; cache = _50_1550.cache; nolabels = _50_1550.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1550.encode_non_total_function_typ}))
end))))
in (Support.Prims.pipe_right _52_18819 Support.List.unzip))
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
(let _52_18821 = (let _52_18820 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _52_18820 e))
in (_52_18821)::pats)
end
| _ -> begin
(let rec aux = (fun ( tl ) ( vars ) -> (match (vars) with
| [] -> begin
(let _52_18826 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_52_18826)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _52_18828 = (let _52_18827 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _52_18827 tl))
in (aux _52_18828 vars))
end
| _ -> begin
pats
end))
in (let _52_18829 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _52_18829 vars)))
end)
end)
in (let env = (let _50_1575 = env
in {bindings = _50_1575.bindings; depth = _50_1575.depth; tcenv = _50_1575.tcenv; warn = _50_1575.warn; cache = _50_1575.cache; nolabels = true; use_zfuel_name = _50_1575.use_zfuel_name; encode_non_total_function_typ = _50_1575.encode_non_total_function_typ})
in (let _50_1580 = (let _52_18830 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _52_18830 env))
in (match (_50_1580) with
| (pre, decls'') -> begin
(let _50_1583 = (let _52_18831 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _52_18831 env))
in (match (_50_1583) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in (let _52_18836 = (let _52_18835 = (let _52_18834 = (let _52_18833 = (let _52_18832 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_52_18832, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_18833))
in (pats, vars, _52_18834))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_18835))
in (_52_18836, decls)))
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
(let _52_18854 = (f args)
in (_52_18854, [], decls))
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
(let _52_18870 = (f phis)
in (_52_18870, labs, decls))
end))))
in (let const_op = (fun ( f ) ( _50_1627 ) -> (f, [], []))
in (let un_op = (fun ( f ) ( l ) -> (let _52_18884 = (Support.List.hd l)
in (Support.Prims.pipe_left f _52_18884)))
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
(let _52_18907 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_52_18907, (Support.List.append labs1 labs2), (Support.List.append decls1 decls2)))
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
in (let unboxInt_l = (fun ( f ) ( l ) -> (let _52_18919 = (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _52_18919)))
in (let connectives = (let _52_18980 = (let _52_18928 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _52_18928))
in (let _52_18979 = (let _52_18978 = (let _52_18934 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _52_18934))
in (let _52_18977 = (let _52_18976 = (let _52_18975 = (let _52_18943 = (Support.Prims.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _52_18943))
in (let _52_18974 = (let _52_18973 = (let _52_18972 = (let _52_18952 = (Support.Prims.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _52_18952))
in (let _52_18971 = (let _52_18970 = (let _52_18958 = (Support.Prims.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _52_18958))
in (_52_18970)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_52_18972)::_52_18971))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_52_18973)
in (_52_18975)::_52_18974))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_52_18976)
in (_52_18978)::_52_18977))
in (_52_18980)::_52_18979))
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
(let lvar = (let _52_18983 = (varops.fresh "label")
in (_52_18983, Microsoft_FStar_ToSMT_Term.Bool_sort))
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
(let _52_18984 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_52_18984, [], decls))
end))
end))
in (let encode_q_body = (fun ( env ) ( bs ) ( ps ) ( body ) -> (let _50_1790 = (encode_binders None bs env)
in (match (_50_1790) with
| (vars, guards, env, decls, _) -> begin
(let _50_1806 = (let _52_18994 = (Support.Prims.pipe_right ps (Support.List.map (fun ( _50_18 ) -> (match (_50_18) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_typ_term t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _50_1802 = env
in {bindings = _50_1802.bindings; depth = _50_1802.depth; tcenv = _50_1802.tcenv; warn = _50_1802.warn; cache = _50_1802.cache; nolabels = _50_1802.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1802.encode_non_total_function_typ}))
end))))
in (Support.Prims.pipe_right _52_18994 Support.List.unzip))
in (match (_50_1806) with
| (pats, decls') -> begin
(let _50_1810 = (encode_formula_with_labels body env)
in (match (_50_1810) with
| (body, labs, decls'') -> begin
(let _52_18995 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _52_18995, body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'')))
end))
end))
end)))
in (let _50_1811 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_18996 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" _52_18996))
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
(let _52_19012 = (Support.Prims.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" _52_19012))
end
| false -> begin
()
end)
in (let _50_1844 = (encode_q_body env vars pats body)
in (match (_50_1844) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _52_19015 = (let _52_19014 = (let _52_19013 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _52_19013))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19014))
in (_52_19015, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _50_1857 = (encode_q_body env vars pats body)
in (match (_50_1857) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _52_19018 = (let _52_19017 = (let _52_19016 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _52_19016))
in (Microsoft_FStar_ToSMT_Term.mkExists _52_19017))
in (_52_19018, labs, decls))
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
in (let quant = (fun ( vars ) ( body ) -> (fun ( x ) -> (let t1 = (let _52_19061 = (let _52_19060 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _52_19060))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19061))
in (let vname_decl = (let _52_19063 = (let _52_19062 = (Support.Prims.pipe_right vars (Support.List.map Support.Prims.snd))
in (x, _52_19062, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_52_19063))
in (let _52_19069 = (let _52_19068 = (let _52_19067 = (let _52_19066 = (let _52_19065 = (let _52_19064 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _52_19064))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19065))
in (_52_19066, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19067))
in (_52_19068)::[])
in (vname_decl)::_52_19069)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _52_19229 = (let _52_19078 = (let _52_19077 = (let _52_19076 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19076))
in (quant axy _52_19077))
in (Microsoft_FStar_Absyn_Const.op_Eq, _52_19078))
in (let _52_19228 = (let _52_19227 = (let _52_19085 = (let _52_19084 = (let _52_19083 = (let _52_19082 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _52_19082))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19083))
in (quant axy _52_19084))
in (Microsoft_FStar_Absyn_Const.op_notEq, _52_19085))
in (let _52_19226 = (let _52_19225 = (let _52_19094 = (let _52_19093 = (let _52_19092 = (let _52_19091 = (let _52_19090 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19089 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19090, _52_19089)))
in (Microsoft_FStar_ToSMT_Term.mkLT _52_19091))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19092))
in (quant xy _52_19093))
in (Microsoft_FStar_Absyn_Const.op_LT, _52_19094))
in (let _52_19224 = (let _52_19223 = (let _52_19103 = (let _52_19102 = (let _52_19101 = (let _52_19100 = (let _52_19099 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19098 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19099, _52_19098)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _52_19100))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19101))
in (quant xy _52_19102))
in (Microsoft_FStar_Absyn_Const.op_LTE, _52_19103))
in (let _52_19222 = (let _52_19221 = (let _52_19112 = (let _52_19111 = (let _52_19110 = (let _52_19109 = (let _52_19108 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19107 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19108, _52_19107)))
in (Microsoft_FStar_ToSMT_Term.mkGT _52_19109))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19110))
in (quant xy _52_19111))
in (Microsoft_FStar_Absyn_Const.op_GT, _52_19112))
in (let _52_19220 = (let _52_19219 = (let _52_19121 = (let _52_19120 = (let _52_19119 = (let _52_19118 = (let _52_19117 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19116 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19117, _52_19116)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _52_19118))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19119))
in (quant xy _52_19120))
in (Microsoft_FStar_Absyn_Const.op_GTE, _52_19121))
in (let _52_19218 = (let _52_19217 = (let _52_19130 = (let _52_19129 = (let _52_19128 = (let _52_19127 = (let _52_19126 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19125 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19126, _52_19125)))
in (Microsoft_FStar_ToSMT_Term.mkSub _52_19127))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _52_19128))
in (quant xy _52_19129))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _52_19130))
in (let _52_19216 = (let _52_19215 = (let _52_19137 = (let _52_19136 = (let _52_19135 = (let _52_19134 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _52_19134))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _52_19135))
in (quant qx _52_19136))
in (Microsoft_FStar_Absyn_Const.op_Minus, _52_19137))
in (let _52_19214 = (let _52_19213 = (let _52_19146 = (let _52_19145 = (let _52_19144 = (let _52_19143 = (let _52_19142 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19141 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19142, _52_19141)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _52_19143))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _52_19144))
in (quant xy _52_19145))
in (Microsoft_FStar_Absyn_Const.op_Addition, _52_19146))
in (let _52_19212 = (let _52_19211 = (let _52_19155 = (let _52_19154 = (let _52_19153 = (let _52_19152 = (let _52_19151 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19150 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19151, _52_19150)))
in (Microsoft_FStar_ToSMT_Term.mkMul _52_19152))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _52_19153))
in (quant xy _52_19154))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _52_19155))
in (let _52_19210 = (let _52_19209 = (let _52_19164 = (let _52_19163 = (let _52_19162 = (let _52_19161 = (let _52_19160 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19159 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19160, _52_19159)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _52_19161))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _52_19162))
in (quant xy _52_19163))
in (Microsoft_FStar_Absyn_Const.op_Division, _52_19164))
in (let _52_19208 = (let _52_19207 = (let _52_19173 = (let _52_19172 = (let _52_19171 = (let _52_19170 = (let _52_19169 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19168 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_52_19169, _52_19168)))
in (Microsoft_FStar_ToSMT_Term.mkMod _52_19170))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _52_19171))
in (quant xy _52_19172))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _52_19173))
in (let _52_19206 = (let _52_19205 = (let _52_19182 = (let _52_19181 = (let _52_19180 = (let _52_19179 = (let _52_19178 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _52_19177 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_52_19178, _52_19177)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _52_19179))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19180))
in (quant xy _52_19181))
in (Microsoft_FStar_Absyn_Const.op_And, _52_19182))
in (let _52_19204 = (let _52_19203 = (let _52_19191 = (let _52_19190 = (let _52_19189 = (let _52_19188 = (let _52_19187 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _52_19186 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_52_19187, _52_19186)))
in (Microsoft_FStar_ToSMT_Term.mkOr _52_19188))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19189))
in (quant xy _52_19190))
in (Microsoft_FStar_Absyn_Const.op_Or, _52_19191))
in (let _52_19202 = (let _52_19201 = (let _52_19198 = (let _52_19197 = (let _52_19196 = (let _52_19195 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _52_19195))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19196))
in (quant qx _52_19197))
in (Microsoft_FStar_Absyn_Const.op_Negation, _52_19198))
in (_52_19201)::[])
in (_52_19203)::_52_19202))
in (_52_19205)::_52_19204))
in (_52_19207)::_52_19206))
in (_52_19209)::_52_19208))
in (_52_19211)::_52_19210))
in (_52_19213)::_52_19212))
in (_52_19215)::_52_19214))
in (_52_19217)::_52_19216))
in (_52_19219)::_52_19218))
in (_52_19221)::_52_19220))
in (_52_19223)::_52_19222))
in (_52_19225)::_52_19224))
in (_52_19227)::_52_19226))
in (_52_19229)::_52_19228))
in (let mk = (fun ( l ) ( v ) -> (let _52_19260 = (Support.Prims.pipe_right prims (Support.List.filter (fun ( _50_1889 ) -> (match (_50_1889) with
| (l', _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (Support.Prims.pipe_right _52_19260 (Support.List.collect (fun ( _50_1893 ) -> (match (_50_1893) with
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
in (let _52_19291 = (let _52_19282 = (let _52_19281 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_52_19281, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19282))
in (let _52_19290 = (let _52_19289 = (let _52_19288 = (let _52_19287 = (let _52_19286 = (let _52_19285 = (let _52_19284 = (let _52_19283 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _52_19283))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19284))
in ((typing_pred)::[], (xx)::[], _52_19285))
in (mkForall_fuel _52_19286))
in (_52_19287, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19288))
in (_52_19289)::[])
in (_52_19291)::_52_19290))))
in (let mk_bool = (fun ( _50_1910 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _52_19311 = (let _52_19301 = (let _52_19300 = (let _52_19299 = (let _52_19298 = (let _52_19297 = (let _52_19296 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _52_19296))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19297))
in ((typing_pred)::[], (xx)::[], _52_19298))
in (mkForall_fuel _52_19299))
in (_52_19300, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19301))
in (let _52_19310 = (let _52_19309 = (let _52_19308 = (let _52_19307 = (let _52_19306 = (let _52_19305 = (let _52_19302 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_52_19302)::[])
in (let _52_19304 = (let _52_19303 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _52_19303 tt))
in (_52_19305, (bb)::[], _52_19304)))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19306))
in (_52_19307, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19308))
in (_52_19309)::[])
in (_52_19311)::_52_19310))))))
in (let mk_int = (fun ( _50_1917 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _52_19323 = (let _52_19322 = (let _52_19321 = (let _52_19320 = (let _52_19319 = (let _52_19318 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _52_19317 = (let _52_19316 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_52_19316)::[])
in (_52_19318)::_52_19317))
in (tt)::_52_19319)
in (tt)::_52_19320)
in ("Prims.Precedes", _52_19321))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19322))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _52_19323))
in (let precedes_y_x = (let _52_19324 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _52_19324))
in (let _52_19365 = (let _52_19330 = (let _52_19329 = (let _52_19328 = (let _52_19327 = (let _52_19326 = (let _52_19325 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _52_19325))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19326))
in ((typing_pred)::[], (xx)::[], _52_19327))
in (mkForall_fuel _52_19328))
in (_52_19329, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19330))
in (let _52_19364 = (let _52_19363 = (let _52_19337 = (let _52_19336 = (let _52_19335 = (let _52_19334 = (let _52_19331 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_52_19331)::[])
in (let _52_19333 = (let _52_19332 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _52_19332 tt))
in (_52_19334, (bb)::[], _52_19333)))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19335))
in (_52_19336, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19337))
in (let _52_19362 = (let _52_19361 = (let _52_19360 = (let _52_19359 = (let _52_19358 = (let _52_19357 = (let _52_19356 = (let _52_19355 = (let _52_19354 = (let _52_19353 = (let _52_19352 = (let _52_19351 = (let _52_19340 = (let _52_19339 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _52_19338 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_52_19339, _52_19338)))
in (Microsoft_FStar_ToSMT_Term.mkGT _52_19340))
in (let _52_19350 = (let _52_19349 = (let _52_19343 = (let _52_19342 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _52_19341 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_52_19342, _52_19341)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _52_19343))
in (let _52_19348 = (let _52_19347 = (let _52_19346 = (let _52_19345 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _52_19344 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_52_19345, _52_19344)))
in (Microsoft_FStar_ToSMT_Term.mkLT _52_19346))
in (_52_19347)::[])
in (_52_19349)::_52_19348))
in (_52_19351)::_52_19350))
in (typing_pred_y)::_52_19352)
in (typing_pred)::_52_19353)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _52_19354))
in (_52_19355, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19356))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _52_19357))
in (mkForall_fuel _52_19358))
in (_52_19359, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19360))
in (_52_19361)::[])
in (_52_19363)::_52_19362))
in (_52_19365)::_52_19364)))))))))))
in (let mk_int_alias = (fun ( _50_1929 ) ( tt ) -> (let _52_19374 = (let _52_19373 = (let _52_19372 = (let _52_19371 = (let _52_19370 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _52_19370))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19371))
in (_52_19372, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19373))
in (_52_19374)::[]))
in (let mk_str = (fun ( _50_1933 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _52_19394 = (let _52_19384 = (let _52_19383 = (let _52_19382 = (let _52_19381 = (let _52_19380 = (let _52_19379 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _52_19379))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19380))
in ((typing_pred)::[], (xx)::[], _52_19381))
in (mkForall_fuel _52_19382))
in (_52_19383, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19384))
in (let _52_19393 = (let _52_19392 = (let _52_19391 = (let _52_19390 = (let _52_19389 = (let _52_19388 = (let _52_19385 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_52_19385)::[])
in (let _52_19387 = (let _52_19386 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _52_19386 tt))
in (_52_19388, (bb)::[], _52_19387)))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19389))
in (_52_19390, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19391))
in (_52_19392)::[])
in (_52_19394)::_52_19393))))))
in (let mk_ref = (fun ( reft_name ) ( _50_1941 ) -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _52_19401 = (let _52_19400 = (let _52_19399 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_52_19399)::[])
in (reft_name, _52_19400))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19401))
in (let refb = (let _52_19404 = (let _52_19403 = (let _52_19402 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_52_19402)::[])
in (reft_name, _52_19403))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19404))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _52_19423 = (let _52_19410 = (let _52_19409 = (let _52_19408 = (let _52_19407 = (let _52_19406 = (let _52_19405 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _52_19405))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19406))
in ((typing_pred)::[], (xx)::(aa)::[], _52_19407))
in (mkForall_fuel _52_19408))
in (_52_19409, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19410))
in (let _52_19422 = (let _52_19421 = (let _52_19420 = (let _52_19419 = (let _52_19418 = (let _52_19417 = (let _52_19416 = (let _52_19415 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _52_19414 = (let _52_19413 = (let _52_19412 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _52_19411 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_52_19412, _52_19411)))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19413))
in (_52_19415, _52_19414)))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19416))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _52_19417))
in (mkForall_fuel' 2 _52_19418))
in (_52_19419, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19420))
in (_52_19421)::[])
in (_52_19423)::_52_19422))))))))))
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
(let _52_19516 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") _52_19516))
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
(let _52_19519 = (let _52_19518 = (let _52_19517 = (Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_52_19517))
in (_52_19518)::[])
in (_52_19519, e))
end
| _ -> begin
(let _52_19526 = (let _52_19525 = (let _52_19521 = (let _52_19520 = (Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_52_19520))
in (_52_19521)::g)
in (let _52_19524 = (let _52_19523 = (let _52_19522 = (Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_52_19522))
in (_52_19523)::[])
in (Support.List.append _52_19525 _52_19524)))
in (_52_19526, e))
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
in (let valid_b2t_x = (let _52_19531 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _52_19531))
in (let decls = (let _52_19539 = (let _52_19538 = (let _52_19537 = (let _52_19536 = (let _52_19535 = (let _52_19534 = (let _52_19533 = (let _52_19532 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _52_19532))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19533))
in ((valid_b2t_x)::[], (xx)::[], _52_19534))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19535))
in (_52_19536, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19537))
in (_52_19538)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_52_19539)
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
(let tok_app = (let _52_19540 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _52_19540 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _52_19542 = (let _52_19541 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _52_19541))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19542))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _ -> begin
(let _52_19544 = (let _52_19543 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _52_19543))
in (_52_19544)::[])
end)
in (let decls = (let _52_19555 = (let _52_19548 = (let _52_19547 = (let _52_19546 = (let _52_19545 = (Support.List.map Support.Prims.snd vars)
in (tname, _52_19545, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_52_19546))
in (_52_19547)::(tok_decl)::[])
in (Support.List.append _52_19548 fresh_tok))
in (let _52_19554 = (let _52_19553 = (let _52_19552 = (let _52_19551 = (let _52_19550 = (let _52_19549 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _52_19549))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19550))
in (_52_19551, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19552))
in (_52_19553)::[])
in (Support.List.append _52_19555 _52_19554)))
in (let t = (whnf env t)
in (let _50_2078 = (match ((Support.Prims.pipe_right tags (Support.Microsoft.FStar.Util.for_some (fun ( _50_19 ) -> (match (_50_19) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _ -> begin
false
end))))) with
| true -> begin
(let _52_19558 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _52_19557 = (encode_formula t env')
in (_52_19558, _52_19557)))
end
| false -> begin
(let _52_19559 = (encode_typ_term t env')
in (app, _52_19559))
end)
in (match (_50_2078) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _52_19566 = (let _52_19565 = (let _52_19564 = (let _52_19563 = (let _52_19562 = (let _52_19561 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _52_19560 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_52_19561, _52_19560)))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19562))
in ((def)::[], vars, _52_19563))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19564))
in (_52_19565, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19566))
in (let kindingAx = (let _50_2082 = (let _52_19567 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _52_19567 env' app))
in (match (_50_2082) with
| (k, decls) -> begin
(let _52_19575 = (let _52_19574 = (let _52_19573 = (let _52_19572 = (let _52_19571 = (let _52_19570 = (let _52_19569 = (let _52_19568 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_52_19568, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19569))
in ((app)::[], vars, _52_19570))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19571))
in (_52_19572, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19573))
in (_52_19574)::[])
in (Support.List.append decls _52_19575))
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
(match ((let _52_19578 = (Microsoft_FStar_Absyn_Util.is_smt_lemma t)
in (let _52_19577 = (let _52_19576 = (Support.Prims.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption))
in (_52_19576 || env.tcenv.Microsoft_FStar_Tc_Env.is_iface))
in (_52_19578 && _52_19577)))) with
| true -> begin
(let _52_19580 = (let _52_19579 = (encode_smt_lemma env lid t)
in (Support.List.append decls _52_19579))
in (_52_19580, env))
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
(let g = (let _52_19585 = (let _52_19584 = (let _52_19583 = (let _52_19582 = (let _52_19581 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "Assumption: %s" _52_19581))
in Some (_52_19582))
in (f, _52_19583))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19584))
in (_52_19585)::[])
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
in (let _52_19587 = (let _52_19586 = (primitive_type_axioms t tname tsym)
in (decl)::_52_19586)
in (_52_19587, (push_free_tvar env t tname (Some (tsym))))))))
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
(let _52_19593 = (let _52_19592 = (let _52_19591 = (Support.Prims.pipe_right args (Support.List.map Support.Prims.snd))
in (name, _52_19591, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_52_19592))
in (_52_19593)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun ( tapp ) ( vars ) -> (match ((let _52_19600 = (Support.Prims.pipe_right datas (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (let _52_19599 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (Support.Prims.pipe_right _52_19599 Support.Option.isNone)))))
in (((Support.List.length datas) = 0) || _52_19600))) with
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
(let indices = (match ((let _52_19603 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _52_19603.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_, indices)) -> begin
indices
end
| _ -> begin
[]
end)
in (let env = (Support.Prims.pipe_right args (Support.List.fold_left (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_19608 = (let _52_19607 = (let _52_19606 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_52_19606, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19607))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _52_19608))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_19611 = (let _52_19610 = (let _52_19609 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_52_19609, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19610))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _52_19611))
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
in (let eqs = (let _52_19618 = (Support.List.map2 (fun ( v ) ( a ) -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_19615 = (let _52_19614 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_52_19614, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19615))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(let _52_19617 = (let _52_19616 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_52_19616, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19617))
end)) vars indices)
in (Support.Prims.pipe_right _52_19618 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _52_19623 = (let _52_19622 = (let _52_19621 = (let _52_19620 = (let _52_19619 = (mk_data_tester env l xx)
in (_52_19619, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _52_19620))
in (out, _52_19621))
in (Microsoft_FStar_ToSMT_Term.mkOr _52_19622))
in (_52_19623, (Support.List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_50_2216) with
| (data_ax, decls) -> begin
(let _50_2219 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2219) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _52_19624 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _52_19624 xx tapp))
in (let _52_19631 = (let _52_19630 = (let _52_19629 = (let _52_19628 = (let _52_19627 = (let _52_19626 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _52_19625 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _52_19626, _52_19625)))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19627))
in (_52_19628, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19629))
in (_52_19630)::[])
in (Support.List.append decls _52_19631)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _50_2231 = (match ((let _52_19632 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _52_19632.Microsoft_FStar_Absyn_Syntax.n)) with
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
(let dproj_app = (let _52_19646 = (let _52_19645 = (let _52_19644 = (mk_typ_projector_name d a)
in (let _52_19643 = (let _52_19642 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_52_19642)::[])
in (_52_19644, _52_19643)))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19645))
in (mk_ApplyT _52_19646 suffix))
in (let _52_19651 = (let _52_19650 = (let _52_19649 = (let _52_19648 = (let _52_19647 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _52_19647))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19648))
in (_52_19649, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19650))
in (_52_19651)::[]))
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
in (let _52_19664 = (let _52_19663 = (let _52_19662 = (let _52_19661 = (let _52_19660 = (let _52_19659 = (let _52_19658 = (let _52_19657 = (let _52_19656 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _52_19656))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19657))
in (xx_has_type, _52_19658))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19659))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _52_19660))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19661))
in (_52_19662, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19663))
in (_52_19664)::[]))
end))
end)))
in (let _50_2294 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2294) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _52_19666 = (let _52_19665 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _52_19665))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19666))
in (let _50_2319 = (let tname_decl = (let _52_19670 = (let _52_19669 = (Support.Prims.pipe_right vars (Support.List.map (fun ( _50_2300 ) -> (match (_50_2300) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))))
in (let _52_19668 = (varops.next_id ())
in (tname, _52_19669, Microsoft_FStar_ToSMT_Term.Type_sort, _52_19668)))
in (constructor_or_logic_type_decl _52_19670))
in (let _50_2316 = (match (vars) with
| [] -> begin
(let _52_19674 = (let _52_19673 = (let _52_19672 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (Support.Prims.pipe_left (fun ( _52_19671 ) -> Some (_52_19671)) _52_19672))
in (push_free_tvar env t tname _52_19673))
in ([], _52_19674))
end
| _ -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _52_19675 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _52_19675))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match ((let _52_19677 = (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _50_23 ) -> (match (_50_23) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _ -> begin
false
end))))
in ((not (is_logical)) && _52_19677))) with
| true -> begin
((ttok_app)::[])::((tapp)::[])::[]
end
| false -> begin
((ttok_app)::[])::[]
end)
in (let name_tok_corr = (let _52_19681 = (let _52_19680 = (let _52_19679 = (let _52_19678 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _52_19678))
in (Microsoft_FStar_ToSMT_Term.mkForall' _52_19679))
in (_52_19680, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19681))
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
(let _52_19685 = (let _52_19684 = (let _52_19683 = (let _52_19682 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _52_19682))
in (_52_19683, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19684))
in (_52_19685)::[])
end
| false -> begin
[]
end)
in (let _52_19691 = (let _52_19690 = (let _52_19689 = (let _52_19688 = (let _52_19687 = (let _52_19686 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _52_19686))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19687))
in (_52_19688, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19689))
in (_52_19690)::[])
in (Support.List.append (Support.List.append decls karr) _52_19691)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _52_19692 = (projection_axioms tapp vars)
in (Support.List.append kindingAx _52_19692))
end
| false -> begin
(let _52_19699 = (let _52_19697 = (let _52_19695 = (let _52_19693 = (primitive_type_axioms t tname tapp)
in (Support.List.append kindingAx _52_19693))
in (let _52_19694 = (inversion_axioms tapp vars)
in (Support.List.append _52_19695 _52_19694)))
in (let _52_19696 = (projection_axioms tapp vars)
in (Support.List.append _52_19697 _52_19696)))
in (let _52_19698 = (pretype_axioms tapp vars)
in (Support.List.append _52_19699 _52_19698)))
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
(let _52_19701 = (mk_typ_projector_name d a)
in (_52_19701, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_19702 = (mk_term_projector_name d x)
in (_52_19702, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _52_19704 = (let _52_19703 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _52_19703))
in (Support.Prims.pipe_right _52_19704 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
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
(let _52_19706 = (let _52_19705 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _52_19705))
in (_52_19706)::[])
end)
in (let encode_elim = (fun ( _50_2405 ) -> (match (()) with
| () -> begin
(let _50_2408 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_50_2408) with
| (head, args) -> begin
(match ((let _52_19709 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _52_19709.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _50_2414 = (encode_args args env')
in (match (_50_2414) with
| (encoded_args, arg_decls) -> begin
(let _50_2438 = (Support.List.fold_left (fun ( _50_2418 ) ( arg ) -> (match (_50_2418) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _50_2426 = (let _52_19712 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _52_19712))
in (match (_50_2426) with
| (_, tv, env) -> begin
(let _52_19714 = (let _52_19713 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_52_19713)::eqns)
in (env, (tv)::arg_vars, _52_19714))
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _50_2433 = (let _52_19715 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _52_19715))
in (match (_50_2433) with
| (_, xv, env) -> begin
(let _52_19717 = (let _52_19716 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_52_19716)::eqns)
in (env, (xv)::arg_vars, _52_19717))
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
in (let typing_inversion = (let _52_19724 = (let _52_19723 = (let _52_19722 = (let _52_19721 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _52_19720 = (let _52_19719 = (let _52_19718 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards))
in (ty_pred, _52_19718))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19719))
in ((ty_pred)::[], _52_19721, _52_19720)))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19722))
in (_52_19723, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19724))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _52_19725 = (varops.fresh "x")
in (_52_19725, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _52_19734 = (let _52_19733 = (let _52_19732 = (let _52_19731 = (let _52_19726 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_52_19726)::[])
in (let _52_19730 = (let _52_19729 = (let _52_19728 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _52_19727 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_52_19728, _52_19727)))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19729))
in (_52_19731, (x)::[], _52_19730)))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19732))
in (_52_19733, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19734))))
end
| false -> begin
(let prec = (Support.Prims.pipe_right vars (Support.List.collect (fun ( v ) -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _52_19737 = (let _52_19736 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _52_19736 dapp))
in (_52_19737)::[])
end
| _ -> begin
(failwith ("unexpected sort"))
end))))
in (let _52_19744 = (let _52_19743 = (let _52_19742 = (let _52_19741 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _52_19740 = (let _52_19739 = (let _52_19738 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _52_19738))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19739))
in ((ty_pred)::[], _52_19741, _52_19740)))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19742))
in (_52_19743, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19744)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _ -> begin
(let _50_2458 = (let _52_19747 = (let _52_19746 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _52_19745 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" _52_19746 _52_19745)))
in (Microsoft_FStar_Tc_Errors.warn drange _52_19747))
in ([], []))
end)
end))
end))
in (let _50_2462 = (encode_elim ())
in (match (_50_2462) with
| (decls2, elim) -> begin
(let g = (let _52_19772 = (let _52_19771 = (let _52_19756 = (let _52_19755 = (let _52_19754 = (let _52_19753 = (let _52_19752 = (let _52_19751 = (let _52_19750 = (let _52_19749 = (let _52_19748 = (Microsoft_FStar_Absyn_Print.sli d)
in (Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" _52_19748))
in Some (_52_19749))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _52_19750))
in Microsoft_FStar_ToSMT_Term.DeclFun (_52_19751))
in (_52_19752)::[])
in (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) _52_19753))
in (Support.List.append _52_19754 proxy_fresh))
in (Support.List.append _52_19755 decls_formals))
in (Support.List.append _52_19756 decls_pred))
in (let _52_19770 = (let _52_19769 = (let _52_19768 = (let _52_19760 = (let _52_19759 = (let _52_19758 = (let _52_19757 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _52_19757))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19758))
in (_52_19759, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19760))
in (let _52_19767 = (let _52_19766 = (let _52_19765 = (let _52_19764 = (let _52_19763 = (let _52_19762 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _52_19761 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _52_19762, _52_19761)))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19763))
in (_52_19764, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19765))
in (_52_19766)::[])
in (_52_19768)::_52_19767))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_52_19769)
in (Support.List.append _52_19771 _52_19770)))
in (Support.List.append _52_19772 elim))
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
(let _52_19785 = (let _52_19784 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _52_19784))
in Support.Microsoft.FStar.Util.Inl (_52_19785))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _52_19787 = (let _52_19786 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _52_19786))
in Support.Microsoft.FStar.Util.Inr (_52_19787))
end
| _ -> begin
(failwith ("Impossible"))
end)) formals binders)
in (let extra_formals = (let _52_19788 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (Support.Prims.pipe_right _52_19788 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _52_19794 = (let _52_19790 = (let _52_19789 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (Support.Prims.pipe_left Support.Prims.snd _52_19789))
in (body, _52_19790))
in (let _52_19793 = (let _52_19792 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (Support.Prims.pipe_left (fun ( _52_19791 ) -> Some (_52_19791)) _52_19792))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _52_19794 _52_19793 body.Microsoft_FStar_Absyn_Syntax.pos)))
in ((Support.List.append binders extra_formals), body))))
end))))
in (let destruct_bound_function = (fun ( flid ) ( t_norm ) ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _, _))) | (Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body))) -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let nformals = (Support.List.length formals)
in (let nbinders = (Support.List.length binders)
in (let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (match ((let _52_19801 = (Microsoft_FStar_Absyn_Util.is_total_comp c)
in ((nformals < nbinders) && _52_19801))) with
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
(let _52_19804 = (let _52_19803 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _52_19802 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _52_19803 _52_19802)))
in (failwith (_52_19804)))
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
(let _52_19810 = (Support.Prims.pipe_right bindings (Support.List.collect (fun ( lb ) -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _52_19809 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _52_19809 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(raise (Let_rec_unencodeable))
end))))
in (_52_19810, env))
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
in (let t_norm = (let _52_19813 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.Prims.pipe_right _52_19813 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _50_2609 = (let _52_19814 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _52_19814 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_50_2609) with
| (tok, decl, env) -> begin
(let _52_19817 = (let _52_19816 = (let _52_19815 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_52_19815, tok))
in (_52_19816)::toks)
in (_52_19817, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_50_2614) with
| (toks, typs, decls, env) -> begin
(let toks = (Support.List.rev toks)
in (let decls = (Support.Prims.pipe_right (Support.List.rev decls) Support.List.flatten)
in (let typs = (Support.List.rev typs)
in (match ((let _52_19824 = (Support.Prims.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _50_27 ) -> (match (_50_27) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))))
in (let _52_19823 = (Support.Prims.pipe_right typs (Support.Microsoft.FStar.Util.for_some (fun ( t ) -> (let _52_19822 = (Microsoft_FStar_Absyn_Util.is_lemma t)
in (let _52_19821 = (let _52_19820 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_19820))
in (_52_19822 || _52_19821))))))
in (_52_19824 || _52_19823)))) with
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
(let _52_19826 = (let _52_19825 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _52_19825))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19826))
end)
in (let _50_2659 = (encode_exp body env')
in (match (_50_2659) with
| (body, decls2) -> begin
(let eqn = (let _52_19835 = (let _52_19834 = (let _52_19831 = (let _52_19830 = (let _52_19829 = (let _52_19828 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _52_19827 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_52_19828, _52_19827)))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19829))
in ((app)::[], vars, _52_19830))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19831))
in (let _52_19833 = (let _52_19832 = (Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_52_19832))
in (_52_19834, _52_19833)))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19835))
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
(let fuel = (let _52_19836 = (varops.fresh "fuel")
in (_52_19836, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _50_2679 = (Support.Prims.pipe_right toks (Support.List.fold_left (fun ( _50_2668 ) ( _50_2673 ) -> (match ((_50_2668, _50_2673)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _52_19841 = (let _52_19840 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (Support.Prims.pipe_left (fun ( _52_19839 ) -> Some (_52_19839)) _52_19840))
in (push_free_var env flid gtok _52_19841))
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
(let decl_g = (let _52_19852 = (let _52_19851 = (let _52_19850 = (Support.List.map Support.Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_52_19850)
in (g, _52_19851, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_52_19852))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _52_19855 = (let _52_19854 = (let _52_19853 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_52_19853)::vars_tm)
in (g, _52_19854))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19855))
in (let gmax = (let _52_19858 = (let _52_19857 = (let _52_19856 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_52_19856)::vars_tm)
in (g, _52_19857))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19858))
in (let _50_2719 = (encode_exp body env')
in (match (_50_2719) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _52_19867 = (let _52_19866 = (let _52_19863 = (let _52_19862 = (let _52_19861 = (let _52_19860 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _52_19859 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_52_19860, _52_19859)))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19861))
in ((gsapp)::[], (fuel)::vars, _52_19862))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19863))
in (let _52_19865 = (let _52_19864 = (Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_52_19864))
in (_52_19866, _52_19865)))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19867))
in (let eqn_f = (let _52_19871 = (let _52_19870 = (let _52_19869 = (let _52_19868 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _52_19868))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19869))
in (_52_19870, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19871))
in (let eqn_g' = (let _52_19880 = (let _52_19879 = (let _52_19878 = (let _52_19877 = (let _52_19876 = (let _52_19875 = (let _52_19874 = (let _52_19873 = (let _52_19872 = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (_52_19872)::vars_tm)
in (g, _52_19873))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19874))
in (gsapp, _52_19875))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19876))
in ((gsapp)::[], (fuel)::vars, _52_19877))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19878))
in (_52_19879, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19880))
in (let _50_2742 = (let _50_2729 = (encode_binders None formals env0)
in (match (_50_2729) with
| (vars, v_guards, env, binder_decls, _) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _52_19881 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _52_19881 ((fuel)::vars)))
in (let _52_19885 = (let _52_19884 = (let _52_19883 = (let _52_19882 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _52_19882))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19883))
in (_52_19884, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19885)))
in (let _50_2739 = (let _50_2736 = (encode_typ_pred' None tres env gapp)
in (match (_50_2736) with
| (g_typing, d3) -> begin
(let _52_19893 = (let _52_19892 = (let _52_19891 = (let _52_19890 = (let _52_19889 = (let _52_19888 = (let _52_19887 = (let _52_19886 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_52_19886, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _52_19887))
in ((gapp)::[], (fuel)::vars, _52_19888))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19889))
in (_52_19890, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19891))
in (_52_19892)::[])
in (d3, _52_19893))
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
in (let _50_2758 = (let _52_19896 = (Support.List.zip3 gtoks typs bindings)
in (Support.List.fold_left (fun ( _50_2746 ) ( _50_2750 ) -> (match ((_50_2746, _50_2750)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _50_2754 = (encode_one_binding env0 gtok ty bs)
in (match (_50_2754) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _52_19896))
in (match (_50_2758) with
| (decls, eqns, env0) -> begin
(let _50_2767 = (let _52_19898 = (Support.Prims.pipe_right decls Support.List.flatten)
in (Support.Prims.pipe_right _52_19898 (Support.List.partition (fun ( _50_28 ) -> (match (_50_28) with
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
(let msg = (let _52_19901 = (Support.Prims.pipe_right bindings (Support.List.map (fun ( lb ) -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (Support.Prims.pipe_right _52_19901 (Support.String.concat " and ")))
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
and encode_free_var = (fun ( env ) ( lid ) ( tt ) ( t_norm ) ( quals ) -> (match ((let _52_19916 = (let _52_19914 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (Support.Prims.pipe_left Support.Prims.op_Negation _52_19914))
in (let _52_19915 = (Microsoft_FStar_Absyn_Util.is_lemma t_norm)
in (_52_19916 || _52_19915)))) with
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
(let _52_19918 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _52_19918))
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
in (let _52_19931 = (let _52_19930 = (let _52_19929 = (let _52_19928 = (let _52_19927 = (let _52_19926 = (let _52_19925 = (let _52_19924 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (Support.Prims.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _52_19924))
in (vapp, _52_19925))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19926))
in ((vapp)::[], vars, _52_19927))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19928))
in (_52_19929, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19930))
in (_52_19931)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _50_2887 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_50_2887) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _52_19940 = (let _52_19939 = (let _52_19938 = (let _52_19937 = (let _52_19936 = (let _52_19935 = (let _52_19934 = (let _52_19933 = (let _52_19932 = (mk_term_projector_name d f)
in (_52_19932, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19933))
in (vapp, _52_19934))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_19935))
in ((vapp)::[], vars, _52_19936))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19937))
in (_52_19938, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19939))
in (_52_19940)::[]))
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
(let _52_19941 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_52_19941, decls1))
end
| Some (p) -> begin
(let _50_2903 = (encode_formula p env')
in (match (_50_2903) with
| (g, ds) -> begin
(let _52_19942 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_52_19942, (Support.List.append decls1 ds)))
end))
end)
in (match (_50_2906) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _52_19944 = (let _52_19943 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _52_19943))
in (Microsoft_FStar_ToSMT_Term.mkApp _52_19944))
in (let _50_2937 = (let vname_decl = (let _52_19947 = (let _52_19946 = (Support.Prims.pipe_right formals (Support.List.map (fun ( _50_31 ) -> (match (_50_31) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _ -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _52_19946, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_52_19947))
in (let _50_2924 = (let env = (let _50_2919 = env
in {bindings = _50_2919.bindings; depth = _50_2919.depth; tcenv = _50_2919.tcenv; warn = _50_2919.warn; cache = _50_2919.cache; nolabels = _50_2919.nolabels; use_zfuel_name = _50_2919.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((let _52_19948 = (head_normal env tt)
in (not (_52_19948)))) with
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
(let _52_19952 = (let _52_19951 = (let _52_19950 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Support.Prims.pipe_left (fun ( _52_19949 ) -> Some (_52_19949)) _52_19950))
in (push_free_var env lid vname _52_19951))
in ((Support.List.append decls2 ((tok_typing)::[])), _52_19952))
end
| _ -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _52_19953 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _52_19953))
in (let name_tok_corr = (let _52_19957 = (let _52_19956 = (let _52_19955 = (let _52_19954 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _52_19954))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19955))
in (_52_19956, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19957))
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
(let typingAx = (let _52_19961 = (let _52_19960 = (let _52_19959 = (let _52_19958 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _52_19958))
in (Microsoft_FStar_ToSMT_Term.mkForall _52_19959))
in (_52_19960, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_19961))
in (let g = (let _52_19963 = (let _52_19962 = (mk_disc_proj_axioms vapp vars)
in (typingAx)::_52_19962)
in (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) _52_19963))
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
(let _52_19979 = (let _52_19978 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _52_19977 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _52_19976 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" _52_19978 _52_19977 _52_19976))))
in Some (_52_19979))
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
(let g = (let _52_19985 = (let _52_19984 = (let _52_19983 = (let _52_19982 = (let _52_19981 = (let _52_19980 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_52_19980))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _52_19981))
in Microsoft_FStar_ToSMT_Term.DeclFun (_52_19982))
in (_52_19983)::[])
in (Support.List.append _52_19984 decls'))
in (Support.List.append _52_19985 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
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
(let _52_19993 = (Support.Prims.pipe_left (fun ( _52_19989 ) -> Microsoft_FStar_ToSMT_Term.Echo (_52_19989)) (Support.Prims.fst l))
in (let _52_19992 = (let _52_19991 = (let _52_19990 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_52_19990))
in (_52_19991)::[])
in (_52_19993)::_52_19992))
end))))
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun ( tcenv ) -> (let _52_19998 = (let _52_19997 = (let _52_19996 = (Support.Microsoft.FStar.Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _52_19996; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_52_19997)::[])
in (Support.ST.op_Colon_Equals last_env _52_19998)))

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

let pop = (fun ( msg ) -> (let _50_3071 = (let _52_20019 = (pop_env ())
in (Support.Prims.pipe_left Support.Prims.ignore _52_20019))
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
(let _52_20033 = (let _52_20032 = (let _52_20031 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.String.strcat "encoding sigelt " _52_20031))
in Microsoft_FStar_ToSMT_Term.Caption (_52_20032))
in (_52_20033)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _50_3097 = (encode_sigelt env se)
in (match (_50_3097) with
| (decls, env) -> begin
(let _50_3098 = (set_env env)
in (let _52_20034 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _52_20034)))
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
(let _52_20039 = (Support.Prims.pipe_right (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name _52_20039))
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

let solve = (fun ( tcenv ) ( q ) -> (let _50_3123 = (let _52_20048 = (let _52_20047 = (let _52_20046 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _52_20046))
in (Support.Microsoft.FStar.Util.format1 "Starting query at %s" _52_20047))
in (push _52_20048))
in (let pop = (fun ( _50_3126 ) -> (match (()) with
| () -> begin
(let _52_20053 = (let _52_20052 = (let _52_20051 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.Prims.pipe_left Support.Microsoft.FStar.Range.string_of_range _52_20051))
in (Support.Microsoft.FStar.Util.format1 "Ending query at %s" _52_20052))
in (pop _52_20053))
end))
in (let _50_3156 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun ( bs ) ( b ) -> (b)::bs) [])
in (let _50_3139 = (let _52_20057 = (Support.List.filter (fun ( _50_32 ) -> (match (_50_32) with
| Microsoft_FStar_Tc_Env.Binding_sig (_) -> begin
false
end
| _ -> begin
true
end)) bindings)
in (encode_env_bindings env _52_20057))
in (match (_50_3139) with
| (env_decls, env) -> begin
(let _50_3140 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _52_20058 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" _52_20058))
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
in (let qry = (let _52_20060 = (let _52_20059 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_52_20059, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_52_20060))
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
(let _52_20082 = (let _52_20081 = (let _52_20066 = (let _52_20065 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" _52_20065))
in Microsoft_FStar_ToSMT_Term.Caption (_52_20066))
in (let _52_20080 = (let _52_20079 = (let _52_20071 = (let _52_20070 = (let _52_20069 = (let _52_20068 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _52_20067 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_52_20068, _52_20067)))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_20069))
in (_52_20070, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_20071))
in (let _52_20078 = (let _52_20077 = (let _52_20076 = (let _52_20075 = (let _52_20074 = (let _52_20073 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _52_20072 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_52_20073, _52_20072)))
in (Microsoft_FStar_ToSMT_Term.mkEq _52_20074))
in (_52_20075, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_20076))
in (_52_20077)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_52_20079)::_52_20078))
in (_52_20081)::_52_20080))
in (Support.List.append _52_20082 suffix))
end))
in (let check = (fun ( p ) -> (let initial_config = (let _52_20086 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _52_20085 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_52_20086, _52_20085)))
in (let alt_configs = (let _52_20119 = (let _52_20118 = (match ((let _52_20088 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (let _52_20087 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_52_20088 > _52_20087)))) with
| true -> begin
(let _52_20091 = (let _52_20090 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _52_20089 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_52_20090, _52_20089)))
in (_52_20091)::[])
end
| false -> begin
[]
end)
in (let _52_20117 = (let _52_20116 = (match ((let _52_20094 = (let _52_20092 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (_52_20092 / 2))
in (let _52_20093 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (_52_20094 > _52_20093)))) with
| true -> begin
(let _52_20098 = (let _52_20097 = (let _52_20095 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (_52_20095 / 2))
in (let _52_20096 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_52_20097, _52_20096)))
in (_52_20098)::[])
end
| false -> begin
[]
end)
in (let _52_20115 = (let _52_20114 = (match ((let _52_20104 = (let _52_20100 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _52_20099 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (_52_20100 > _52_20099)))
in (let _52_20103 = (let _52_20102 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (let _52_20101 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_52_20102 > _52_20101)))
in (_52_20104 && _52_20103)))) with
| true -> begin
(let _52_20107 = (let _52_20106 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _52_20105 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_52_20106, _52_20105)))
in (_52_20107)::[])
end
| false -> begin
[]
end)
in (let _52_20113 = (let _52_20112 = (match ((let _52_20109 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (let _52_20108 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (_52_20109 < _52_20108)))) with
| true -> begin
(let _52_20111 = (let _52_20110 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (_52_20110, 1))
in (_52_20111)::[])
end
| false -> begin
[]
end)
in (_52_20112)::[])
in (_52_20114)::_52_20113))
in (_52_20116)::_52_20115))
in (_52_20118)::_52_20117))
in (Support.List.flatten _52_20119))
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
(let _52_20131 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _52_20131 (cb p [])))
end
| _ -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(let _52_20133 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _52_20133 (fun ( _50_3218 ) -> (match (_50_3218) with
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
in (let _52_20137 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _52_20137 (cb p alt_configs))))))))
in (let process_query = (fun ( q ) -> (match ((let _52_20140 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (_52_20140 > 0))) with
| true -> begin
(let _50_3231 = (let _52_20144 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _52_20144 q))
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





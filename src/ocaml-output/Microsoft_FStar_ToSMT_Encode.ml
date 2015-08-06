
let add_fuel = (fun ( x ) ( tl ) -> (match ((Support.ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
tl
end
| false -> begin
(x)::tl
end))

let withenv = (fun ( c ) ( _52_39 ) -> (match (_52_39) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun ( args ) -> (Support.List.filter (fun ( _52_1 ) -> (match (_52_1) with
| (Support.Microsoft.FStar.Util.Inl (_52_43), _52_46) -> begin
false
end
| _52_49 -> begin
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

let mk_typ_projector_name = (fun ( lid ) ( a ) -> (let _70_21403 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _70_21403)))

let mk_term_projector_name = (fun ( lid ) ( a ) -> (let a = (let _70_21408 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _70_21408; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _70_21409 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _70_21409))))

let primitive_projector_by_pos = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _52_61 ) -> (match (()) with
| () -> begin
(let _70_21419 = (let _70_21418 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" _70_21418 lid.Microsoft_FStar_Absyn_Syntax.str))
in (Support.All.failwith _70_21419))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _70_21420 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_21420.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _52_65)) -> begin
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
| _52_74 -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun ( lid ) ( i ) -> (let _70_21426 = (let _70_21425 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _70_21425))
in (Support.All.pipe_left escape _70_21426)))

let mk_typ_projector = (fun ( lid ) ( a ) -> (let _70_21432 = (let _70_21431 = (mk_typ_projector_name lid a)
in (_70_21431, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_21432)))

let mk_term_projector = (fun ( lid ) ( a ) -> (let _70_21438 = (let _70_21437 = (mk_term_projector_name lid a)
in (_70_21437, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_21438)))

let mk_term_projector_by_pos = (fun ( lid ) ( i ) -> (let _70_21444 = (let _70_21443 = (mk_term_projector_name_by_pos lid i)
in (_70_21443, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_21444)))

let mk_data_tester = (fun ( env ) ( l ) ( x ) -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let is_Mkvarops_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun ( _52_100 ) -> (match (()) with
| () -> begin
(let _70_21548 = (Support.Microsoft.FStar.Util.smap_create 100)
in (let _70_21547 = (Support.Microsoft.FStar.Util.smap_create 100)
in (_70_21548, _70_21547)))
end))
in (let scopes = (let _70_21550 = (let _70_21549 = (new_scope ())
in (_70_21549)::[])
in (Support.Microsoft.FStar.Util.mk_ref _70_21550))
in (let mk_unique = (fun ( y ) -> (let y = (escape y)
in (let y = (match ((let _70_21554 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _70_21554 (fun ( _52_108 ) -> (match (_52_108) with
| (names, _52_107) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_52_111) -> begin
(let _52_113 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _70_21556 = (let _70_21555 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _70_21555))
in (Support.String.strcat (Support.String.strcat y "__") _70_21556)))
end)
in (let top_scope = (let _70_21558 = (let _70_21557 = (Support.ST.read scopes)
in (Support.List.hd _70_21557))
in (Support.All.pipe_left Support.Prims.fst _70_21558))
in (let _52_117 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun ( pp ) ( rn ) -> (let _70_21564 = (let _70_21563 = (Support.All.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.String.strcat _70_21563 "__"))
in (Support.String.strcat _70_21564 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun ( lid ) -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun ( _52_125 ) -> (match (()) with
| () -> begin
(let _52_126 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
end))
in (let fresh = (fun ( pfx ) -> (let _70_21572 = (let _70_21571 = (next_id ())
in (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int _70_21571))
in (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx _70_21572)))
in (let string_const = (fun ( s ) -> (match ((let _70_21576 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _70_21576 (fun ( _52_135 ) -> (match (_52_135) with
| (_52_133, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _70_21577 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxString _70_21577))
in (let top_scope = (let _70_21579 = (let _70_21578 = (Support.ST.read scopes)
in (Support.List.hd _70_21578))
in (Support.All.pipe_left Support.Prims.snd _70_21579))
in (let _52_142 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun ( _52_145 ) -> (match (()) with
| () -> begin
(let _70_21584 = (let _70_21583 = (new_scope ())
in (let _70_21582 = (Support.ST.read scopes)
in (_70_21583)::_70_21582))
in (Support.ST.op_Colon_Equals scopes _70_21584))
end))
in (let pop = (fun ( _52_147 ) -> (match (()) with
| () -> begin
(let _70_21588 = (let _70_21587 = (Support.ST.read scopes)
in (Support.List.tl _70_21587))
in (Support.ST.op_Colon_Equals scopes _70_21588))
end))
in (let mark = (fun ( _52_149 ) -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun ( _52_151 ) -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun ( _52_153 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _52_166 = (Support.Microsoft.FStar.Util.smap_fold hd1 (fun ( key ) ( value ) ( v ) -> (Support.Microsoft.FStar.Util.smap_add next1 key value)) ())
in (let _52_171 = (Support.Microsoft.FStar.Util.smap_fold hd2 (fun ( key ) ( value ) ( v ) -> (Support.Microsoft.FStar.Util.smap_add next2 key value)) ())
in (Support.ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _52_174 -> begin
(Support.All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun ( x ) -> (let _70_21604 = (let _70_21603 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _70_21602 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_70_21603, _70_21602)))
in (Microsoft_FStar_Absyn_Util.mkbvd _70_21604)))

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

let is_Mkenv_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkenv_t"))

let print_env = (fun ( e ) -> (let _70_21662 = (Support.All.pipe_right e.bindings (Support.List.map (fun ( _52_2 ) -> (match (_52_2) with
| Binding_var ((x, t)) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Binding_tvar ((a, t)) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Binding_fvar ((l, s, t, _52_209)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| Binding_ftvar ((l, s, t)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end))))
in (Support.All.pipe_right _70_21662 (Support.String.concat ", "))))

let lookup_binding = (fun ( env ) ( f ) -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun ( env ) ( t ) -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_21672 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_70_21672))
end
| false -> begin
None
end))

let fresh_fvar = (fun ( x ) ( s ) -> (let xsym = (varops.fresh x)
in (let _70_21677 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _70_21677))))

let gen_term_var = (fun ( env ) ( x ) -> (let ysym = (let _70_21682 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@x" _70_21682))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _52_228 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _52_228.tcenv; warn = _52_228.warn; cache = _52_228.cache; nolabels = _52_228.nolabels; use_zfuel_name = _52_228.use_zfuel_name; encode_non_total_function_typ = _52_228.encode_non_total_function_typ})))))

let new_term_constant = (fun ( env ) ( x ) -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _52_234 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _52_234.depth; tcenv = _52_234.tcenv; warn = _52_234.warn; cache = _52_234.cache; nolabels = _52_234.nolabels; use_zfuel_name = _52_234.use_zfuel_name; encode_non_total_function_typ = _52_234.encode_non_total_function_typ})))))

let push_term_var = (fun ( env ) ( x ) ( t ) -> (let _52_239 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _52_239.depth; tcenv = _52_239.tcenv; warn = _52_239.warn; cache = _52_239.cache; nolabels = _52_239.nolabels; use_zfuel_name = _52_239.use_zfuel_name; encode_non_total_function_typ = _52_239.encode_non_total_function_typ}))

let lookup_term_var = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_3 ) -> (match (_52_3) with
| Binding_var ((b, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _52_249 -> begin
None
end)))) with
| None -> begin
(let _70_21697 = (let _70_21696 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" _70_21696))
in (Support.All.failwith _70_21697))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun ( env ) ( x ) -> (let ysym = (let _70_21702 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@a" _70_21702))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _52_259 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _52_259.tcenv; warn = _52_259.warn; cache = _52_259.cache; nolabels = _52_259.nolabels; use_zfuel_name = _52_259.use_zfuel_name; encode_non_total_function_typ = _52_259.encode_non_total_function_typ})))))

let new_typ_constant = (fun ( env ) ( x ) -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _52_265 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _52_265.depth; tcenv = _52_265.tcenv; warn = _52_265.warn; cache = _52_265.cache; nolabels = _52_265.nolabels; use_zfuel_name = _52_265.use_zfuel_name; encode_non_total_function_typ = _52_265.encode_non_total_function_typ})))))

let push_typ_var = (fun ( env ) ( x ) ( t ) -> (let _52_270 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _52_270.depth; tcenv = _52_270.tcenv; warn = _52_270.warn; cache = _52_270.cache; nolabels = _52_270.nolabels; use_zfuel_name = _52_270.use_zfuel_name; encode_non_total_function_typ = _52_270.encode_non_total_function_typ}))

let lookup_typ_var = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_4 ) -> (match (_52_4) with
| Binding_tvar ((b, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _52_280 -> begin
None
end)))) with
| None -> begin
(let _70_21717 = (let _70_21716 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" _70_21716))
in (Support.All.failwith _70_21717))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _70_21728 = (let _52_290 = env
in (let _70_21727 = (let _70_21726 = (let _70_21725 = (let _70_21724 = (let _70_21723 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _70_21722 ) -> Some (_70_21722)) _70_21723))
in (x, fname, _70_21724, None))
in Binding_fvar (_70_21725))
in (_70_21726)::env.bindings)
in {bindings = _70_21727; depth = _52_290.depth; tcenv = _52_290.tcenv; warn = _52_290.warn; cache = _52_290.cache; nolabels = _52_290.nolabels; use_zfuel_name = _52_290.use_zfuel_name; encode_non_total_function_typ = _52_290.encode_non_total_function_typ}))
in (fname, ftok, _70_21728)))))

let try_lookup_lid = (fun ( env ) ( a ) -> (lookup_binding env (fun ( _52_5 ) -> (match (_52_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _52_302 -> begin
None
end))))

let lookup_lid = (fun ( env ) ( a ) -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _70_21739 = (let _70_21738 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _70_21738))
in (Support.All.failwith _70_21739))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_312 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _52_312.depth; tcenv = _52_312.tcenv; warn = _52_312.warn; cache = _52_312.cache; nolabels = _52_312.nolabels; use_zfuel_name = _52_312.use_zfuel_name; encode_non_total_function_typ = _52_312.encode_non_total_function_typ}))

let push_zfuel_name = (fun ( env ) ( x ) ( f ) -> (let _52_321 = (lookup_lid env x)
in (match (_52_321) with
| (t1, t2, _52_320) -> begin
(let t3 = (let _70_21756 = (let _70_21755 = (let _70_21754 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_70_21754)::[])
in (f, _70_21755))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_21756))
in (let _52_323 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _52_323.depth; tcenv = _52_323.tcenv; warn = _52_323.warn; cache = _52_323.cache; nolabels = _52_323.nolabels; use_zfuel_name = _52_323.use_zfuel_name; encode_non_total_function_typ = _52_323.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun ( env ) ( a ) -> (let _52_330 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_330) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _52_334 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((_52_338, fuel::[])) -> begin
(match ((let _70_21760 = (let _70_21759 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (Support.All.pipe_right _70_21759 Support.Prims.fst))
in (Support.Microsoft.FStar.Util.starts_with _70_21760 "fuel"))) with
| true -> begin
(let _70_21761 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _70_21761 fuel))
end
| false -> begin
t
end)
end
| _52_344 -> begin
t
end)
end
| _52_346 -> begin
(let _70_21763 = (let _70_21762 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _70_21762))
in (Support.All.failwith _70_21763))
end)
end)
end)))

let lookup_free_var_name = (fun ( env ) ( a ) -> (let _52_354 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_354) with
| (x, _52_351, _52_353) -> begin
x
end)))

let lookup_free_var_sym = (fun ( env ) ( a ) -> (let _52_360 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_360) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((g, zf)); Microsoft_FStar_ToSMT_Term.hash = _52_364; Microsoft_FStar_ToSMT_Term.freevars = _52_362}) when env.use_zfuel_name -> begin
(g, zf)
end
| _52_372 -> begin
(match (sym) with
| None -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((g, fuel::[])) -> begin
(g, (fuel)::[])
end
| _52_382 -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _70_21778 = (let _52_387 = env
in (let _70_21777 = (let _70_21776 = (let _70_21775 = (let _70_21774 = (let _70_21773 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _70_21772 ) -> Some (_70_21772)) _70_21773))
in (x, fname, _70_21774))
in Binding_ftvar (_70_21775))
in (_70_21776)::env.bindings)
in {bindings = _70_21777; depth = _52_387.depth; tcenv = _52_387.tcenv; warn = _52_387.warn; cache = _52_387.cache; nolabels = _52_387.nolabels; use_zfuel_name = _52_387.use_zfuel_name; encode_non_total_function_typ = _52_387.encode_non_total_function_typ}))
in (fname, ftok, _70_21778)))))

let lookup_tlid = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_6 ) -> (match (_52_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _52_398 -> begin
None
end)))) with
| None -> begin
(let _70_21785 = (let _70_21784 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _70_21784))
in (Support.All.failwith _70_21785))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_406 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _52_406.depth; tcenv = _52_406.tcenv; warn = _52_406.warn; cache = _52_406.cache; nolabels = _52_406.nolabels; use_zfuel_name = _52_406.use_zfuel_name; encode_non_total_function_typ = _52_406.encode_non_total_function_typ}))

let lookup_free_tvar = (fun ( env ) ( a ) -> (match ((let _70_21796 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_21796 Support.Prims.snd))) with
| None -> begin
(let _70_21798 = (let _70_21797 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _70_21797))
in (Support.All.failwith _70_21798))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun ( env ) ( a ) -> (let _70_21801 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_21801 Support.Prims.fst)))

let tok_of_name = (fun ( env ) ( nm ) -> (Support.Microsoft.FStar.Util.find_map env.bindings (fun ( _52_7 ) -> (match (_52_7) with
| (Binding_fvar ((_, nm', tok, _))) | (Binding_ftvar ((_, nm', tok))) when (nm = nm') -> begin
tok
end
| _52_431 -> begin
None
end))))

let mkForall_fuel' = (fun ( n ) ( _52_436 ) -> (match (_52_436) with
| (pats, vars, body) -> begin
(let fallback = (fun ( _52_438 ) -> (match (()) with
| () -> begin
(Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in (match ((Support.ST.read Microsoft_FStar_Options.unthrottle_inductives)) with
| true -> begin
(fallback ())
end
| false -> begin
(let _52_441 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_441) with
| (fsym, fterm) -> begin
(let pats = (Support.All.pipe_right pats (Support.List.map (fun ( p ) -> (match (p.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var ("HasType"), args)) -> begin
(Microsoft_FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _52_449 -> begin
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
(let _70_21817 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_21817 Support.Option.isNone))
end
| _52_487 -> begin
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

let trivial_post = (fun ( t ) -> (let _70_21839 = (let _70_21838 = (let _70_21836 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_21836)::[])
in (let _70_21837 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_70_21838, _70_21837)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_21839 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun ( e ) ( vars ) -> (Support.All.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _70_21846 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _70_21846))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _70_21847 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _70_21847))
end
| _52_504 -> begin
(let _70_21848 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _70_21848))
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
(let _70_21861 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _70_21861))
end
| _52_519 -> begin
(let _70_21862 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _70_21862))
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
| _52_538 -> begin
false
end))

let is_eta = (fun ( env ) ( vars ) ( t ) -> (let rec aux = (fun ( t ) ( xs ) -> (match ((t.Microsoft_FStar_ToSMT_Term.tm, xs)) with
| (Microsoft_FStar_ToSMT_Term.App ((app, f::{Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.FreeV (y); Microsoft_FStar_ToSMT_Term.hash = _52_549; Microsoft_FStar_ToSMT_Term.freevars = _52_547}::[])), x::xs) when ((is_app app) && (Microsoft_FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var (f), args)), _52_567) -> begin
(match ((((Support.List.length args) = (Support.List.length vars)) && (Support.List.forall2 (fun ( a ) ( v ) -> (match (a.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (fv) -> begin
(Microsoft_FStar_ToSMT_Term.fv_eq fv v)
end
| _52_574 -> begin
false
end)) args vars))) with
| true -> begin
(tok_of_name env f)
end
| false -> begin
None
end)
end
| (_52_576, []) -> begin
(let fvs = (Microsoft_FStar_ToSMT_Term.free_variables t)
in (match ((Support.All.pipe_right fvs (Support.List.for_all (fun ( fv ) -> (not ((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_ToSMT_Term.fv_eq fv) vars))))))) with
| true -> begin
Some (t)
end
| false -> begin
None
end))
end
| _52_582 -> begin
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
(let _70_21918 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _70_21918))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _70_21919 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _70_21919))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _70_21920 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _70_21920))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _70_21924 = (let _70_21923 = (let _70_21922 = (let _70_21921 = (Microsoft_FStar_ToSMT_Term.mkInteger' i)
in (Microsoft_FStar_ToSMT_Term.boxInt _70_21921))
in (_70_21922)::[])
in ("Int32.Int32", _70_21923))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_21924))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _52_604)) -> begin
(let _70_21925 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_bytes bytes)
in (varops.string_const _70_21925))
end
| c -> begin
(let _70_21927 = (let _70_21926 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" _70_21926))
in (Support.All.failwith _70_21927))
end))

let as_function_typ = (fun ( env ) ( t0 ) -> (let rec aux = (fun ( norm ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_52_615) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_618) -> begin
(let _70_21936 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _70_21936))
end
| _52_621 -> begin
(match (norm) with
| true -> begin
(let _70_21937 = (whnf env t)
in (aux false _70_21937))
end
| false -> begin
(let _70_21940 = (let _70_21939 = (Support.Microsoft.FStar.Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_21938 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Support.Microsoft.FStar.Util.format2 "(%s) Expected a function typ; got %s" _70_21939 _70_21938)))
in (Support.All.failwith _70_21940))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun ( k ) ( env ) -> (match ((let _70_21972 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _70_21972.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_52_626, k0)) -> begin
(let _52_630 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _70_21974 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _70_21973 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _70_21974 _70_21973)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _52_634)) -> begin
(let _70_21976 = (let _70_21975 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _70_21975))
in (_70_21976, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, kbody)) -> begin
(let tsym = (let _70_21977 = (varops.fresh "t")
in (_70_21977, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let t = (Microsoft_FStar_ToSMT_Term.mkFreeV tsym)
in (let _52_649 = (encode_binders None bs env)
in (match (_52_649) with
| (vars, guards, env', decls, _52_648) -> begin
(let app = (mk_ApplyT t vars)
in (let _52_653 = (encode_knd kbody env' app)
in (match (_52_653) with
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
| _52_672 -> begin
(let _70_21986 = (let _70_21985 = (let _70_21984 = (Microsoft_FStar_ToSMT_Term.mk_PreKind app)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_21984))
in (_70_21985, body))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_21986))
end)
in (let _70_21988 = (let _70_21987 = (Microsoft_FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _70_21987))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_21988)))))
end
| _52_675 -> begin
(Support.All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _70_21990 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (Support.All.pipe_right _70_21990 (Support.List.filter (fun ( _52_680 ) -> (match (_52_680) with
| (x, _52_679) -> begin
(x <> (Support.Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((k', sorts, _52_686)) -> begin
(let _70_21993 = (let _70_21992 = (let _70_21991 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _70_21991))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_21992))
in (_70_21993, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_21994 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_70_21994))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _70_21996 = (let _70_21995 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _70_21995))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_21996))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _70_22005 = (let _70_22004 = (let _70_22003 = (let _70_22002 = (let _70_22001 = (let _70_22000 = (let _70_21999 = (let _70_21998 = (let _70_21997 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_21997))
in (_70_21998, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_21999))
in (t_has_k, _70_22000))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22001))
in ((t_has_k)::[], (tsym)::cvars, _70_22002))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22003))
in (_70_22004, Some ((Support.String.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22005))
in (let k_decls = (Support.List.append (Support.List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _52_698 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _52_701 -> begin
(let _70_22007 = (let _70_22006 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" _70_22006))
in (Support.All.failwith _70_22007))
end))
and encode_knd = (fun ( k ) ( env ) ( t ) -> (let _52_707 = (encode_knd_term k env)
in (match (_52_707) with
| (k, decls) -> begin
(let _70_22011 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_70_22011, decls))
end)))
and encode_binders = (fun ( fuel_opt ) ( bs ) ( env ) -> (let _52_711 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_22015 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" _70_22015))
end
| false -> begin
()
end)
in (let _52_761 = (Support.All.pipe_right bs (Support.List.fold_left (fun ( _52_718 ) ( b ) -> (match (_52_718) with
| (vars, guards, env, decls, names) -> begin
(let _52_755 = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = a; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _52_721}) -> begin
(let a = (unmangle a)
in (let _52_730 = (gen_typ_var env a)
in (match (_52_730) with
| (aasym, aa, env') -> begin
(let _52_731 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _70_22019 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _70_22018 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _70_22019 aasym _70_22018)))
end
| false -> begin
()
end)
in (let _52_735 = (encode_knd k env aa)
in (match (_52_735) with
| (guard_a_k, decls') -> begin
((aasym, Microsoft_FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', Support.Microsoft.FStar.Util.Inl (a))
end)))
end)))
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _52_737}) -> begin
(let x = (unmangle x)
in (let _52_746 = (gen_term_var env x)
in (match (_52_746) with
| (xxsym, xx, env') -> begin
(let _52_749 = (let _70_22020 = (norm_t env t)
in (encode_typ_pred' fuel_opt _70_22020 env xx))
in (match (_52_749) with
| (guard_x_t, decls') -> begin
((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', Support.Microsoft.FStar.Util.Inr (x))
end))
end)))
end)
in (match (_52_755) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (Support.List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_52_761) with
| (vars, guards, env, decls, names) -> begin
((Support.List.rev vars), (Support.List.rev guards), env, decls, (Support.List.rev names))
end))))
and encode_typ_pred' = (fun ( fuel_opt ) ( t ) ( env ) ( e ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _52_769 = (encode_typ_term t env)
in (match (_52_769) with
| (t, decls) -> begin
(let _70_22025 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_70_22025, decls))
end))))
and encode_typ_term = (fun ( t ) ( env ) -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _70_22028 = (lookup_typ_var env a)
in (_70_22028, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _70_22029 = (lookup_free_tvar env fv)
in (_70_22029, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
(match (((env.encode_non_total_function_typ && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _52_787 = (encode_binders None binders env)
in (match (_52_787) with
| (vars, guards, env', decls, _52_786) -> begin
(let fsym = (let _70_22030 = (varops.fresh "f")
in (_70_22030, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _52_793 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_52_793) with
| (pre_opt, res_t) -> begin
(let _52_796 = (encode_typ_pred' None res_t env' app)
in (match (_52_796) with
| (res_pred, decls') -> begin
(let _52_805 = (match (pre_opt) with
| None -> begin
(let _70_22031 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_22031, decls))
end
| Some (pre) -> begin
(let _52_802 = (encode_formula pre env')
in (match (_52_802) with
| (guard, decls0) -> begin
(let _70_22032 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_70_22032, (Support.List.append decls decls0)))
end))
end)
in (match (_52_805) with
| (guards, guard_decls) -> begin
(let t_interp = (let _70_22034 = (let _70_22033 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _70_22033))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22034))
in (let cvars = (let _70_22036 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (Support.All.pipe_right _70_22036 (Support.List.filter (fun ( _52_810 ) -> (match (_52_810) with
| (x, _52_809) -> begin
(x <> (Support.Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _52_816)) -> begin
(let _70_22039 = (let _70_22038 = (let _70_22037 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _70_22037))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22038))
in (_70_22039, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_22040 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_70_22040))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _70_22042 = (let _70_22041 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_22041))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22042))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _70_22044 = (let _70_22043 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_70_22043, Some ((Support.String.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22044))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let pre_typing = (let _70_22051 = (let _70_22050 = (let _70_22049 = (let _70_22048 = (let _70_22047 = (let _70_22046 = (let _70_22045 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _70_22045))
in (f_has_t, _70_22046))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22047))
in ((f_has_t)::[], (fsym)::cvars, _70_22048))
in (mkForall_fuel _70_22049))
in (_70_22050, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22051))
in (let t_interp = (let _70_22055 = (let _70_22054 = (let _70_22053 = (let _70_22052 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t, t_interp))
in ((f_has_t)::[], (fsym)::cvars, _70_22052))
in (mkForall_fuel _70_22053))
in (_70_22054, Some ((Support.String.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22055))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _52_831 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
in (let t_kinding = (let _70_22057 = (let _70_22056 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_70_22056, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22057))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _70_22064 = (let _70_22063 = (let _70_22062 = (let _70_22061 = (let _70_22060 = (let _70_22059 = (let _70_22058 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _70_22058))
in (f_has_t, _70_22059))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22060))
in ((f_has_t)::[], (fsym)::[], _70_22061))
in (mkForall_fuel _70_22062))
in (_70_22063, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22064))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_842) -> begin
(let _52_861 = (match ((Microsoft_FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, f)); Microsoft_FStar_Absyn_Syntax.tk = _52_851; Microsoft_FStar_Absyn_Syntax.pos = _52_849; Microsoft_FStar_Absyn_Syntax.fvs = _52_847; Microsoft_FStar_Absyn_Syntax.uvs = _52_845} -> begin
(x, f)
end
| _52_858 -> begin
(Support.All.failwith "impossible")
end)
in (match (_52_861) with
| (x, f) -> begin
(let _52_864 = (encode_typ_term x.Microsoft_FStar_Absyn_Syntax.sort env)
in (match (_52_864) with
| (base_t, decls) -> begin
(let _52_868 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_868) with
| (x, xtm, env') -> begin
(let _52_871 = (encode_formula f env')
in (match (_52_871) with
| (refinement, decls') -> begin
(let encoding = (let _70_22066 = (let _70_22065 = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t)
in (_70_22065, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_22066))
in (let cvars = (let _70_22068 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (Support.All.pipe_right _70_22068 (Support.List.filter (fun ( _52_876 ) -> (match (_52_876) with
| (y, _52_875) -> begin
(y <> x)
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_882, _52_884)) -> begin
(let _70_22071 = (let _70_22070 = (let _70_22069 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _70_22069))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22070))
in (_70_22071, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _70_22073 = (let _70_22072 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_22072))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22073))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _70_22075 = (let _70_22074 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (xfv)::cvars, _70_22074))
in (mkForall_fuel _70_22075))
in (let t_decls = (let _70_22082 = (let _70_22081 = (let _70_22080 = (let _70_22079 = (let _70_22078 = (let _70_22077 = (let _70_22076 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_70_22076))
in (assumption, _70_22077))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22078))
in (_70_22079)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_70_22080)
in (tdecl)::_70_22081)
in (Support.List.append (Support.List.append decls decls') _70_22082))
in (let _52_897 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _70_22083 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _70_22083))
in (let _52_906 = (encode_knd k env ttm)
in (match (_52_906) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let is_full_app = (fun ( _52_913 ) -> (match (()) with
| () -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind head)
in (let _52_918 = (Microsoft_FStar_Absyn_Util.kind_formals kk)
in (match (_52_918) with
| (formals, _52_917) -> begin
((Support.List.length formals) = (Support.List.length args))
end)))
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_typ head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _52_925 = (encode_args args env)
in (match (_52_925) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _52_931 = (encode_args args env)
in (match (_52_931) with
| (args, decls) -> begin
(match ((is_full_app ())) with
| true -> begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _70_22088 = (let _70_22087 = (Support.List.map (fun ( _52_10 ) -> (match (_52_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (head, _70_22087))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22088))
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
(let ttm = (let _70_22089 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _70_22089))
in (let _52_947 = (encode_knd k env ttm)
in (match (_52_947) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _52_950 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, body)) -> begin
(let _52_962 = (encode_binders None bs env)
in (match (_52_962) with
| (vars, guards, env, decls, _52_961) -> begin
(let _52_965 = (encode_typ_term body env)
in (match (_52_965) with
| (body, decls') -> begin
(let key_body = (let _70_22093 = (let _70_22092 = (let _70_22091 = (let _70_22090 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_22090, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22091))
in ([], vars, _70_22092))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22093))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_971, _52_973)) -> begin
(let _70_22096 = (let _70_22095 = (let _70_22094 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _70_22094))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22095))
in (_70_22096, []))
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
in (let t = (let _70_22098 = (let _70_22097 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_22097))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22098))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _70_22105 = (let _70_22104 = (let _70_22103 = (let _70_22102 = (let _70_22101 = (let _70_22100 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_22099 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_22100, _70_22099)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22101))
in ((app)::[], (Support.List.append vars cvars), _70_22102))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22103))
in (_70_22104, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22105))
in (let kinding = (let _52_988 = (let _70_22106 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _70_22106 env t))
in (match (_52_988) with
| (ktm, decls'') -> begin
(let _70_22110 = (let _70_22109 = (let _70_22108 = (let _70_22107 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_70_22107, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22108))
in (_70_22109)::[])
in (Support.List.append decls'' _70_22110))
end))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _52_991 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _52_995)) -> begin
(encode_typ_term t env)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_52_999) -> begin
(let _70_22111 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _70_22111 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _70_22116 = (let _70_22115 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_22114 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _70_22113 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _70_22112 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _70_22115 _70_22114 _70_22113 _70_22112)))))
in (Support.All.failwith _70_22116))
end)))
and encode_exp = (fun ( e ) ( env ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_52_1010) -> begin
(let _70_22119 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _70_22119 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _52_1017)) -> begin
(let _70_22120 = (lookup_free_var env v)
in (_70_22120, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _70_22121 = (encode_const c)
in (_70_22121, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _52_1025)) -> begin
(let _52_1028 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _52_1032))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _52_1038)) -> begin
(let e = (let _70_22122 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _70_22122))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun ( _52_1047 ) -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _70_22125 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_70_22125, (decl)::[]))))
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _52_1051 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _70_22126 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (Support.All.pipe_left Support.Prims.op_Negation _70_22126))) with
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
(let _52_1063 = (Support.Microsoft.FStar.Util.first_N nformals bs)
in (match (_52_1063) with
| (bs0, rest) -> begin
(let res_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s (Microsoft_FStar_Absyn_Util.comp_result c))
end
| _52_1067 -> begin
(Support.All.failwith "Impossible")
end)
in (let e = (let _70_22128 = (let _70_22127 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _70_22127))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_22128 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end
| false -> begin
(let _52_1076 = (encode_binders None bs env)
in (match (_52_1076) with
| (vars, guards, envbody, decls, _52_1075) -> begin
(let _52_1079 = (encode_exp body envbody)
in (match (_52_1079) with
| (body, decls') -> begin
(let key_body = (let _70_22132 = (let _70_22131 = (let _70_22130 = (let _70_22129 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_22129, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22130))
in ([], vars, _70_22131))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22132))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_1085, _52_1087)) -> begin
(let _70_22135 = (let _70_22134 = (let _70_22133 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _70_22133))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22134))
in (_70_22135, []))
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
in (let f = (let _70_22137 = (let _70_22136 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _70_22136))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22137))
in (let app = (mk_ApplyE f vars)
in (let _52_1101 = (encode_typ_pred' None tfun env f)
in (match (_52_1101) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _70_22139 = (let _70_22138 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_70_22138, Some ((Support.String.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22139))
in (let interp_f = (let _70_22146 = (let _70_22145 = (let _70_22144 = (let _70_22143 = (let _70_22142 = (let _70_22141 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _70_22140 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_22141, _70_22140)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22142))
in ((app)::[], (Support.List.append vars cvars), _70_22143))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22144))
in (_70_22145, Some ((Support.String.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22146))
in (let f_decls = (Support.List.append (Support.List.append (Support.List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _52_1105 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end))
end
| _52_1108 -> begin
(Support.All.failwith "Impossible")
end))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((l, _52_1119)); Microsoft_FStar_Absyn_Syntax.tk = _52_1116; Microsoft_FStar_Absyn_Syntax.pos = _52_1114; Microsoft_FStar_Absyn_Syntax.fvs = _52_1112; Microsoft_FStar_Absyn_Syntax.uvs = _52_1110}, (Support.Microsoft.FStar.Util.Inl (_52_1134), _52_1137)::(Support.Microsoft.FStar.Util.Inr (v1), _52_1131)::(Support.Microsoft.FStar.Util.Inr (v2), _52_1126)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals l.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
(let _52_1144 = (encode_exp v1 env)
in (match (_52_1144) with
| (v1, decls1) -> begin
(let _52_1147 = (encode_exp v2 env)
in (match (_52_1147) with
| (v2, decls2) -> begin
(let _70_22147 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_70_22147, (Support.List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_52_1157); Microsoft_FStar_Absyn_Syntax.tk = _52_1155; Microsoft_FStar_Absyn_Syntax.pos = _52_1153; Microsoft_FStar_Absyn_Syntax.fvs = _52_1151; Microsoft_FStar_Absyn_Syntax.uvs = _52_1149}, _52_1161)) -> begin
(let _70_22148 = (whnf_e env e)
in (encode_exp _70_22148 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args_e)) -> begin
(let _52_1170 = (encode_args args_e env)
in (match (_52_1170) with
| (args, decls) -> begin
(let encode_partial_app = (fun ( ht_opt ) -> (let _52_1175 = (encode_exp head env)
in (match (_52_1175) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (Support.List.append decls decls'))
end
| Some ((formals, c)) -> begin
(let _52_1184 = (Support.Microsoft.FStar.Util.first_N (Support.List.length args_e) formals)
in (match (_52_1184) with
| (formals, rest) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _70_22151 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _70_22151 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _52_1189 = (encode_typ_pred' None ty env app_tm)
in (match (_52_1189) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _70_22153 = (let _70_22152 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_70_22152, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22153))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun ( fv ) -> (let _52_1196 = (lookup_free_var_sym env fv)
in (match (_52_1196) with
| (fname, fuel_args) -> begin
(let tm = (let _70_22159 = (let _70_22158 = (let _70_22157 = (Support.List.map (fun ( _52_11 ) -> (match (_52_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (Support.List.append fuel_args _70_22157))
in (fname, _70_22158))
in (Microsoft_FStar_ToSMT_Term.mkApp' _70_22159))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _52_1203 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _70_22161 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _70_22160 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _70_22161 _70_22160)))
end
| false -> begin
()
end)
in (let head_type = (let _70_22164 = (let _70_22163 = (let _70_22162 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _70_22162))
in (whnf env _70_22163))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.unrefine _70_22164))
in (let _52_1206 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _70_22167 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _70_22166 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _70_22165 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _70_22167 _70_22166 _70_22165))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _70_22171 = (let _70_22170 = (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_22169 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _70_22168 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" _70_22170 _70_22169 _70_22168))))
in (Support.All.failwith _70_22171))
end
| Some ((formals, c)) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _52_1215)) when ((Support.List.length formals) = (Support.List.length args)) -> begin
(encode_full_app fv)
end
| _52_1219 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (_52_1228); Microsoft_FStar_Absyn_Syntax.lbtyp = _52_1226; Microsoft_FStar_Absyn_Syntax.lbeff = _52_1224; Microsoft_FStar_Absyn_Syntax.lbdef = _52_1222}::[]), _52_1234)) -> begin
(Support.All.failwith "Impossible: already handled by encoding of Sig_let")
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inl (x); Microsoft_FStar_Absyn_Syntax.lbtyp = t1; Microsoft_FStar_Absyn_Syntax.lbeff = _52_1240; Microsoft_FStar_Absyn_Syntax.lbdef = e1}::[]), e2)) -> begin
(let _52_1252 = (encode_exp e1 env)
in (match (_52_1252) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _52_1256 = (encode_exp e2 env')
in (match (_52_1256) with
| (ee2, decls2) -> begin
(ee2, (Support.List.append decls1 decls2))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_52_1258) -> begin
(let _52_1260 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = Microsoft_FStar_ToSMT_Term.DeclFun ((e, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _70_22172 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_70_22172, (decl_e)::[])))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _52_1270 = (encode_exp e env)
in (match (_52_1270) with
| (scr, decls) -> begin
(let _52_1310 = (Support.List.fold_right (fun ( _52_1274 ) ( _52_1277 ) -> (match ((_52_1274, _52_1277)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (Support.List.fold_right (fun ( _52_1281 ) ( _52_1284 ) -> (match ((_52_1281, _52_1284)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (Support.All.pipe_right projections (Support.List.fold_left (fun ( env ) ( _52_1290 ) -> (match (_52_1290) with
| (x, t) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v t)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _52_1304 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _52_1301 = (encode_exp w env)
in (match (_52_1301) with
| (w, decls2) -> begin
(let _70_22183 = (let _70_22182 = (let _70_22181 = (let _70_22180 = (let _70_22179 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _70_22179))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_22180))
in (guard, _70_22181))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_22182))
in (_70_22183, decls2))
end))
end)
in (match (_52_1304) with
| (guard, decls2) -> begin
(let _52_1307 = (encode_exp br env)
in (match (_52_1307) with
| (br, decls3) -> begin
(let _70_22184 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_70_22184, (Support.List.append (Support.List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (Microsoft_FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_52_1310) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (_52_1312) -> begin
(let _70_22187 = (let _70_22186 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_22185 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" _70_22186 _70_22185)))
in (Support.All.failwith _70_22187))
end))))
and encode_pat = (fun ( env ) ( pat ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _52_1319 -> begin
(let _70_22190 = (encode_one_pat env pat)
in (_70_22190)::[])
end))
and encode_one_pat = (fun ( env ) ( pat ) -> (let _52_1322 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_22193 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" _70_22193))
end
| false -> begin
()
end)
in (let _52_1326 = (Microsoft_FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_52_1326) with
| (vars, pat_exp_or_typ) -> begin
(let _52_1347 = (Support.All.pipe_right vars (Support.List.fold_left (fun ( _52_1329 ) ( v ) -> (match (_52_1329) with
| (env, vars) -> begin
(match (v) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _52_1337 = (gen_typ_var env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_1337) with
| (aa, _52_1335, env) -> begin
(env, ((v, (aa, Microsoft_FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _52_1344 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_52_1344) with
| (xx, _52_1342, env) -> begin
(env, ((v, (xx, Microsoft_FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_52_1347) with
| (env, vars) -> begin
(let rec mk_guard = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_1352) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
Microsoft_FStar_ToSMT_Term.mkTrue
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _70_22201 = (let _70_22200 = (encode_const c)
in (scrutinee, _70_22200))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_22201))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _52_1376, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _70_22204 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _70_22204))))))
in (Microsoft_FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun ( pat ) ( scrutinee ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_52_1389) -> begin
(Support.All.failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((Support.Microsoft.FStar.Util.Inr (x), scrutinee))::[]
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((Support.Microsoft.FStar.Util.Inl (a), scrutinee))::[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_52_1409) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _52_1413, args)) -> begin
(let _70_22212 = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( arg ) -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _70_22211 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _70_22211))))))
in (Support.All.pipe_right _70_22212 Support.List.flatten))
end))
in (let pat_term = (fun ( _52_1421 ) -> (match (()) with
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
and encode_args = (fun ( l ) ( env ) -> (let _52_1451 = (Support.All.pipe_right l (Support.List.fold_left (fun ( _52_1431 ) ( x ) -> (match (_52_1431) with
| (tms, decls) -> begin
(match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1436) -> begin
(let _52_1440 = (encode_typ_term t env)
in (match (_52_1440) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inl (t))::tms, (Support.List.append decls decls'))
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1444) -> begin
(let _52_1448 = (encode_exp e env)
in (match (_52_1448) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inr (t))::tms, (Support.List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_52_1451) with
| (l, decls) -> begin
((Support.List.rev l), decls)
end)))
and encode_formula = (fun ( phi ) ( env ) -> (let _52_1457 = (encode_formula_with_labels phi env)
in (match (_52_1457) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _52_1460 -> begin
(Support.All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun ( induction_on ) ( t ) ( env ) -> (let v_or_t_pat = (fun ( p ) -> (match ((let _70_22226 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _70_22226.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1467, (Support.Microsoft.FStar.Util.Inl (_52_1474), _52_1477)::(Support.Microsoft.FStar.Util.Inr (e), _52_1471)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1483, (Support.Microsoft.FStar.Util.Inl (t), _52_1487)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _52_1493 -> begin
(Support.All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun ( p ) -> (match ((let _70_22229 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _70_22229.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1497, _52_1509::(Support.Microsoft.FStar.Util.Inr (hd), _52_1506)::(Support.Microsoft.FStar.Util.Inr (tl), _52_1501)::[])) -> begin
(let _70_22231 = (v_or_t_pat hd)
in (let _70_22230 = (lemma_pats tl)
in (_70_22231)::_70_22230))
end
| _52_1514 -> begin
[]
end))
in (let _52_1553 = (match ((let _70_22232 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_22232.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _52_1523; Microsoft_FStar_Absyn_Syntax.pos = _52_1521; Microsoft_FStar_Absyn_Syntax.fvs = _52_1519; Microsoft_FStar_Absyn_Syntax.uvs = _52_1517})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _52_1542)::(Support.Microsoft.FStar.Util.Inl (post), _52_1537)::(Support.Microsoft.FStar.Util.Inr (pats), _52_1532)::[] -> begin
(let _70_22233 = (lemma_pats pats)
in (binders, pre, post, _70_22233))
end
| _52_1546 -> begin
(Support.All.failwith "impos")
end)
end
| _52_1548 -> begin
(Support.All.failwith "Impos")
end)
in (match (_52_1553) with
| (binders, pre, post, patterns) -> begin
(let _52_1560 = (encode_binders None binders env)
in (match (_52_1560) with
| (vars, guards, env, decls, _52_1559) -> begin
(let _52_1576 = (let _70_22235 = (Support.All.pipe_right patterns (Support.List.map (fun ( _52_12 ) -> (match (_52_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1565) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1570) -> begin
(encode_exp e (let _52_1572 = env
in {bindings = _52_1572.bindings; depth = _52_1572.depth; tcenv = _52_1572.tcenv; warn = _52_1572.warn; cache = _52_1572.cache; nolabels = _52_1572.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1572.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _70_22235 Support.List.unzip))
in (match (_52_1576) with
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
(let _70_22237 = (let _70_22236 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _70_22236 e))
in (_70_22237)::pats)
end
| _52_1584 -> begin
(let rec aux = (fun ( tl ) ( vars ) -> (match (vars) with
| [] -> begin
(let _70_22242 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_70_22242)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _70_22244 = (let _70_22243 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _70_22243 tl))
in (aux _70_22244 vars))
end
| _52_1595 -> begin
pats
end))
in (let _70_22245 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _70_22245 vars)))
end)
end)
in (let env = (let _52_1597 = env
in {bindings = _52_1597.bindings; depth = _52_1597.depth; tcenv = _52_1597.tcenv; warn = _52_1597.warn; cache = _52_1597.cache; nolabels = true; use_zfuel_name = _52_1597.use_zfuel_name; encode_non_total_function_typ = _52_1597.encode_non_total_function_typ})
in (let _52_1602 = (let _70_22246 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _70_22246 env))
in (match (_52_1602) with
| (pre, decls'') -> begin
(let _52_1605 = (let _70_22247 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _70_22247 env))
in (match (_52_1605) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in (let _70_22252 = (let _70_22251 = (let _70_22250 = (let _70_22249 = (let _70_22248 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_70_22248, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22249))
in (pats, vars, _70_22250))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22251))
in (_70_22252, decls)))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun ( phi ) ( env ) -> (let enc = (fun ( f ) -> (fun ( l ) -> (let _52_1626 = (Support.Microsoft.FStar.Util.fold_map (fun ( decls ) ( x ) -> (match ((Support.Prims.fst x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _52_1618 = (encode_typ_term t env)
in (match (_52_1618) with
| (t, decls') -> begin
((Support.List.append decls decls'), t)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _52_1623 = (encode_exp e env)
in (match (_52_1623) with
| (e, decls') -> begin
((Support.List.append decls decls'), e)
end))
end)) [] l)
in (match (_52_1626) with
| (decls, args) -> begin
(let _70_22270 = (f args)
in (_70_22270, [], decls))
end))))
in (let enc_prop_c = (fun ( f ) -> (fun ( l ) -> (let _52_1646 = (Support.List.fold_right (fun ( t ) ( _52_1634 ) -> (match (_52_1634) with
| (phis, labs, decls) -> begin
(match ((Support.Prims.fst t)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _52_1640 = (encode_formula_with_labels t env)
in (match (_52_1640) with
| (phi, labs', decls') -> begin
((phi)::phis, (Support.List.append labs' labs), (Support.List.append decls' decls))
end))
end
| _52_1642 -> begin
(Support.All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_52_1646) with
| (phis, labs, decls) -> begin
(let _70_22286 = (f phis)
in (_70_22286, labs, decls))
end))))
in (let const_op = (fun ( f ) ( _52_1649 ) -> (f, [], []))
in (let un_op = (fun ( f ) ( l ) -> (let _70_22300 = (Support.List.hd l)
in (Support.All.pipe_left f _70_22300)))
in (let bin_op = (fun ( f ) ( _52_13 ) -> (match (_52_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _52_1660 -> begin
(Support.All.failwith "Impossible")
end))
in (let eq_op = (fun ( _52_14 ) -> (match (_52_14) with
| _52_1668::_52_1666::e1::e2::[] -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun ( _52_15 ) -> (match (_52_15) with
| (Support.Microsoft.FStar.Util.Inl (lhs), _52_1681)::(Support.Microsoft.FStar.Util.Inl (rhs), _52_1676)::[] -> begin
(let _52_1687 = (encode_formula_with_labels rhs env)
in (match (_52_1687) with
| (l1, labs1, decls1) -> begin
(match (l1.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _52_1690)) -> begin
(l1, labs1, decls1)
end
| _52_1694 -> begin
(let _52_1698 = (encode_formula_with_labels lhs env)
in (match (_52_1698) with
| (l2, labs2, decls2) -> begin
(let _70_22314 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_70_22314, (Support.List.append labs1 labs2), (Support.List.append decls1 decls2)))
end))
end)
end))
end
| _52_1700 -> begin
(Support.All.failwith "impossible")
end))
in (let mk_ite = (fun ( _52_16 ) -> (match (_52_16) with
| (Support.Microsoft.FStar.Util.Inl (guard), _52_1716)::(Support.Microsoft.FStar.Util.Inl (_then), _52_1711)::(Support.Microsoft.FStar.Util.Inl (_else), _52_1706)::[] -> begin
(let _52_1722 = (encode_formula_with_labels guard env)
in (match (_52_1722) with
| (g, labs1, decls1) -> begin
(let _52_1726 = (encode_formula_with_labels _then env)
in (match (_52_1726) with
| (t, labs2, decls2) -> begin
(let _52_1730 = (encode_formula_with_labels _else env)
in (match (_52_1730) with
| (e, labs3, decls3) -> begin
(let res = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (Support.List.append (Support.List.append labs1 labs2) labs3), (Support.List.append (Support.List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _52_1733 -> begin
(Support.All.failwith "impossible")
end))
in (let unboxInt_l = (fun ( f ) ( l ) -> (let _70_22326 = (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _70_22326)))
in (let connectives = (let _70_22387 = (let _70_22335 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _70_22335))
in (let _70_22386 = (let _70_22385 = (let _70_22341 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _70_22341))
in (let _70_22384 = (let _70_22383 = (let _70_22382 = (let _70_22350 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _70_22350))
in (let _70_22381 = (let _70_22380 = (let _70_22379 = (let _70_22359 = (Support.All.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _70_22359))
in (let _70_22378 = (let _70_22377 = (let _70_22365 = (Support.All.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _70_22365))
in (_70_22377)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_70_22379)::_70_22378))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_70_22380)
in (_70_22382)::_70_22381))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_70_22383)
in (_70_22385)::_70_22384))
in (_70_22387)::_70_22386))
in (let fallback = (fun ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((phi', msg, r, b))) -> begin
(let _52_1751 = (encode_formula_with_labels phi' env)
in (match (_52_1751) with
| (phi, labs, decls) -> begin
(match (env.nolabels) with
| true -> begin
(phi, [], decls)
end
| false -> begin
(let lvar = (let _70_22390 = (varops.fresh "label")
in (_70_22390, Microsoft_FStar_ToSMT_Term.Bool_sort))
in (let lterm = (Microsoft_FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (Microsoft_FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end)
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ih); Microsoft_FStar_Absyn_Syntax.tk = _52_1762; Microsoft_FStar_Absyn_Syntax.pos = _52_1760; Microsoft_FStar_Absyn_Syntax.fvs = _52_1758; Microsoft_FStar_Absyn_Syntax.uvs = _52_1756}, _52_1777::(Support.Microsoft.FStar.Util.Inr (l), _52_1774)::(Support.Microsoft.FStar.Util.Inl (phi), _52_1769)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals ih.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.using_IH) -> begin
(match ((Microsoft_FStar_Absyn_Util.is_lemma phi)) with
| true -> begin
(let _52_1783 = (encode_exp l env)
in (match (_52_1783) with
| (e, decls) -> begin
(let _52_1786 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_52_1786) with
| (f, decls') -> begin
(f, [], (Support.List.append decls decls'))
end))
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.mkTrue, [], [])
end)
end
| _52_1788 -> begin
(let _52_1791 = (encode_typ_term phi env)
in (match (_52_1791) with
| (tt, decls) -> begin
(let _70_22391 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_70_22391, [], decls))
end))
end))
in (let encode_q_body = (fun ( env ) ( bs ) ( ps ) ( body ) -> (let _52_1803 = (encode_binders None bs env)
in (match (_52_1803) with
| (vars, guards, env, decls, _52_1802) -> begin
(let _52_1819 = (let _70_22401 = (Support.All.pipe_right ps (Support.List.map (fun ( _52_17 ) -> (match (_52_17) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1808) -> begin
(encode_typ_term t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1813) -> begin
(encode_exp e (let _52_1815 = env
in {bindings = _52_1815.bindings; depth = _52_1815.depth; tcenv = _52_1815.tcenv; warn = _52_1815.warn; cache = _52_1815.cache; nolabels = _52_1815.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1815.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _70_22401 Support.List.unzip))
in (match (_52_1819) with
| (pats, decls') -> begin
(let _52_1823 = (encode_formula_with_labels body env)
in (match (_52_1823) with
| (body, labs, decls'') -> begin
(let _70_22402 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _70_22402, body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'')))
end))
end))
end)))
in (let _52_1824 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_22403 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" _70_22403))
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
(match ((Support.All.pipe_right connectives (Support.List.tryFind (fun ( _52_1836 ) -> (match (_52_1836) with
| (l, _52_1835) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some ((_52_1839, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, pats, body))) -> begin
(let _52_1849 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_22420 = (Support.All.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" _70_22420))
end
| false -> begin
()
end)
in (let _52_1857 = (encode_q_body env vars pats body)
in (match (_52_1857) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _70_22423 = (let _70_22422 = (let _70_22421 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _70_22421))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22422))
in (_70_22423, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _52_1870 = (encode_q_body env vars pats body)
in (match (_52_1870) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _70_22426 = (let _70_22425 = (let _70_22424 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _70_22424))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_22425))
in (_70_22426, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : Microsoft_FStar_Absyn_Syntax.lident  ->  string  ->  Microsoft_FStar_ToSMT_Term.decl list; is : Microsoft_FStar_Absyn_Syntax.lident  ->  bool}

let is_Mkprims_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkprims_t"))

let prims = (let _52_1876 = (fresh_fvar "a" Microsoft_FStar_ToSMT_Term.Type_sort)
in (match (_52_1876) with
| (asym, a) -> begin
(let _52_1879 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_1879) with
| (xsym, x) -> begin
(let _52_1882 = (fresh_fvar "y" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_1882) with
| (ysym, y) -> begin
(let deffun = (fun ( vars ) ( body ) ( x ) -> (Microsoft_FStar_ToSMT_Term.DefineFun ((x, vars, Microsoft_FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun ( vars ) ( body ) -> (fun ( x ) -> (let t1 = (let _70_22469 = (let _70_22468 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _70_22468))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22469))
in (let vname_decl = (let _70_22471 = (let _70_22470 = (Support.All.pipe_right vars (Support.List.map Support.Prims.snd))
in (x, _70_22470, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_22471))
in (let _70_22477 = (let _70_22476 = (let _70_22475 = (let _70_22474 = (let _70_22473 = (let _70_22472 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _70_22472))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22473))
in (_70_22474, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22475))
in (_70_22476)::[])
in (vname_decl)::_70_22477)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _70_22637 = (let _70_22486 = (let _70_22485 = (let _70_22484 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22484))
in (quant axy _70_22485))
in (Microsoft_FStar_Absyn_Const.op_Eq, _70_22486))
in (let _70_22636 = (let _70_22635 = (let _70_22493 = (let _70_22492 = (let _70_22491 = (let _70_22490 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _70_22490))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22491))
in (quant axy _70_22492))
in (Microsoft_FStar_Absyn_Const.op_notEq, _70_22493))
in (let _70_22634 = (let _70_22633 = (let _70_22502 = (let _70_22501 = (let _70_22500 = (let _70_22499 = (let _70_22498 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22497 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22498, _70_22497)))
in (Microsoft_FStar_ToSMT_Term.mkLT _70_22499))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22500))
in (quant xy _70_22501))
in (Microsoft_FStar_Absyn_Const.op_LT, _70_22502))
in (let _70_22632 = (let _70_22631 = (let _70_22511 = (let _70_22510 = (let _70_22509 = (let _70_22508 = (let _70_22507 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22506 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22507, _70_22506)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _70_22508))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22509))
in (quant xy _70_22510))
in (Microsoft_FStar_Absyn_Const.op_LTE, _70_22511))
in (let _70_22630 = (let _70_22629 = (let _70_22520 = (let _70_22519 = (let _70_22518 = (let _70_22517 = (let _70_22516 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22515 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22516, _70_22515)))
in (Microsoft_FStar_ToSMT_Term.mkGT _70_22517))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22518))
in (quant xy _70_22519))
in (Microsoft_FStar_Absyn_Const.op_GT, _70_22520))
in (let _70_22628 = (let _70_22627 = (let _70_22529 = (let _70_22528 = (let _70_22527 = (let _70_22526 = (let _70_22525 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22524 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22525, _70_22524)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _70_22526))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22527))
in (quant xy _70_22528))
in (Microsoft_FStar_Absyn_Const.op_GTE, _70_22529))
in (let _70_22626 = (let _70_22625 = (let _70_22538 = (let _70_22537 = (let _70_22536 = (let _70_22535 = (let _70_22534 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22533 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22534, _70_22533)))
in (Microsoft_FStar_ToSMT_Term.mkSub _70_22535))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_22536))
in (quant xy _70_22537))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _70_22538))
in (let _70_22624 = (let _70_22623 = (let _70_22545 = (let _70_22544 = (let _70_22543 = (let _70_22542 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _70_22542))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_22543))
in (quant qx _70_22544))
in (Microsoft_FStar_Absyn_Const.op_Minus, _70_22545))
in (let _70_22622 = (let _70_22621 = (let _70_22554 = (let _70_22553 = (let _70_22552 = (let _70_22551 = (let _70_22550 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22549 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22550, _70_22549)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _70_22551))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_22552))
in (quant xy _70_22553))
in (Microsoft_FStar_Absyn_Const.op_Addition, _70_22554))
in (let _70_22620 = (let _70_22619 = (let _70_22563 = (let _70_22562 = (let _70_22561 = (let _70_22560 = (let _70_22559 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22558 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22559, _70_22558)))
in (Microsoft_FStar_ToSMT_Term.mkMul _70_22560))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_22561))
in (quant xy _70_22562))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _70_22563))
in (let _70_22618 = (let _70_22617 = (let _70_22572 = (let _70_22571 = (let _70_22570 = (let _70_22569 = (let _70_22568 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22567 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22568, _70_22567)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _70_22569))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_22570))
in (quant xy _70_22571))
in (Microsoft_FStar_Absyn_Const.op_Division, _70_22572))
in (let _70_22616 = (let _70_22615 = (let _70_22581 = (let _70_22580 = (let _70_22579 = (let _70_22578 = (let _70_22577 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22576 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_22577, _70_22576)))
in (Microsoft_FStar_ToSMT_Term.mkMod _70_22578))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_22579))
in (quant xy _70_22580))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _70_22581))
in (let _70_22614 = (let _70_22613 = (let _70_22590 = (let _70_22589 = (let _70_22588 = (let _70_22587 = (let _70_22586 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _70_22585 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_70_22586, _70_22585)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_22587))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22588))
in (quant xy _70_22589))
in (Microsoft_FStar_Absyn_Const.op_And, _70_22590))
in (let _70_22612 = (let _70_22611 = (let _70_22599 = (let _70_22598 = (let _70_22597 = (let _70_22596 = (let _70_22595 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _70_22594 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_70_22595, _70_22594)))
in (Microsoft_FStar_ToSMT_Term.mkOr _70_22596))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22597))
in (quant xy _70_22598))
in (Microsoft_FStar_Absyn_Const.op_Or, _70_22599))
in (let _70_22610 = (let _70_22609 = (let _70_22606 = (let _70_22605 = (let _70_22604 = (let _70_22603 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _70_22603))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_22604))
in (quant qx _70_22605))
in (Microsoft_FStar_Absyn_Const.op_Negation, _70_22606))
in (_70_22609)::[])
in (_70_22611)::_70_22610))
in (_70_22613)::_70_22612))
in (_70_22615)::_70_22614))
in (_70_22617)::_70_22616))
in (_70_22619)::_70_22618))
in (_70_22621)::_70_22620))
in (_70_22623)::_70_22622))
in (_70_22625)::_70_22624))
in (_70_22627)::_70_22626))
in (_70_22629)::_70_22628))
in (_70_22631)::_70_22630))
in (_70_22633)::_70_22632))
in (_70_22635)::_70_22634))
in (_70_22637)::_70_22636))
in (let mk = (fun ( l ) ( v ) -> (let _70_22669 = (Support.All.pipe_right prims (Support.List.filter (fun ( _52_1902 ) -> (match (_52_1902) with
| (l', _52_1901) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (Support.All.pipe_right _70_22669 (Support.List.collect (fun ( _52_1906 ) -> (match (_52_1906) with
| (_52_1904, b) -> begin
(b v)
end))))))
in (let is = (fun ( l ) -> (Support.All.pipe_right prims (Support.Microsoft.FStar.Util.for_some (fun ( _52_1912 ) -> (match (_52_1912) with
| (l', _52_1911) -> begin
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
in (let mk_unit = (fun ( _52_1918 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let _70_22701 = (let _70_22692 = (let _70_22691 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_70_22691, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22692))
in (let _70_22700 = (let _70_22699 = (let _70_22698 = (let _70_22697 = (let _70_22696 = (let _70_22695 = (let _70_22694 = (let _70_22693 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _70_22693))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22694))
in ((typing_pred)::[], (xx)::[], _70_22695))
in (mkForall_fuel _70_22696))
in (_70_22697, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22698))
in (_70_22699)::[])
in (_70_22701)::_70_22700))))
in (let mk_bool = (fun ( _52_1923 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _70_22721 = (let _70_22711 = (let _70_22710 = (let _70_22709 = (let _70_22708 = (let _70_22707 = (let _70_22706 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _70_22706))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22707))
in ((typing_pred)::[], (xx)::[], _70_22708))
in (mkForall_fuel _70_22709))
in (_70_22710, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22711))
in (let _70_22720 = (let _70_22719 = (let _70_22718 = (let _70_22717 = (let _70_22716 = (let _70_22715 = (let _70_22712 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_70_22712)::[])
in (let _70_22714 = (let _70_22713 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_22713 tt))
in (_70_22715, (bb)::[], _70_22714)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22716))
in (_70_22717, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22718))
in (_70_22719)::[])
in (_70_22721)::_70_22720))))))
in (let mk_int = (fun ( _52_1930 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _70_22733 = (let _70_22732 = (let _70_22731 = (let _70_22730 = (let _70_22729 = (let _70_22728 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _70_22727 = (let _70_22726 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_70_22726)::[])
in (_70_22728)::_70_22727))
in (tt)::_70_22729)
in (tt)::_70_22730)
in ("Prims.Precedes", _70_22731))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22732))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _70_22733))
in (let precedes_y_x = (let _70_22734 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _70_22734))
in (let _70_22775 = (let _70_22740 = (let _70_22739 = (let _70_22738 = (let _70_22737 = (let _70_22736 = (let _70_22735 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _70_22735))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22736))
in ((typing_pred)::[], (xx)::[], _70_22737))
in (mkForall_fuel _70_22738))
in (_70_22739, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22740))
in (let _70_22774 = (let _70_22773 = (let _70_22747 = (let _70_22746 = (let _70_22745 = (let _70_22744 = (let _70_22741 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_70_22741)::[])
in (let _70_22743 = (let _70_22742 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_22742 tt))
in (_70_22744, (bb)::[], _70_22743)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22745))
in (_70_22746, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22747))
in (let _70_22772 = (let _70_22771 = (let _70_22770 = (let _70_22769 = (let _70_22768 = (let _70_22767 = (let _70_22766 = (let _70_22765 = (let _70_22764 = (let _70_22763 = (let _70_22762 = (let _70_22761 = (let _70_22750 = (let _70_22749 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_22748 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_70_22749, _70_22748)))
in (Microsoft_FStar_ToSMT_Term.mkGT _70_22750))
in (let _70_22760 = (let _70_22759 = (let _70_22753 = (let _70_22752 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _70_22751 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_70_22752, _70_22751)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _70_22753))
in (let _70_22758 = (let _70_22757 = (let _70_22756 = (let _70_22755 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _70_22754 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_70_22755, _70_22754)))
in (Microsoft_FStar_ToSMT_Term.mkLT _70_22756))
in (_70_22757)::[])
in (_70_22759)::_70_22758))
in (_70_22761)::_70_22760))
in (typing_pred_y)::_70_22762)
in (typing_pred)::_70_22763)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _70_22764))
in (_70_22765, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22766))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _70_22767))
in (mkForall_fuel _70_22768))
in (_70_22769, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22770))
in (_70_22771)::[])
in (_70_22773)::_70_22772))
in (_70_22775)::_70_22774)))))))))))
in (let mk_int_alias = (fun ( _52_1942 ) ( tt ) -> (let _70_22784 = (let _70_22783 = (let _70_22782 = (let _70_22781 = (let _70_22780 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _70_22780))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_22781))
in (_70_22782, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22783))
in (_70_22784)::[]))
in (let mk_str = (fun ( _52_1946 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _70_22804 = (let _70_22794 = (let _70_22793 = (let _70_22792 = (let _70_22791 = (let _70_22790 = (let _70_22789 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _70_22789))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22790))
in ((typing_pred)::[], (xx)::[], _70_22791))
in (mkForall_fuel _70_22792))
in (_70_22793, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22794))
in (let _70_22803 = (let _70_22802 = (let _70_22801 = (let _70_22800 = (let _70_22799 = (let _70_22798 = (let _70_22795 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_70_22795)::[])
in (let _70_22797 = (let _70_22796 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_22796 tt))
in (_70_22798, (bb)::[], _70_22797)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22799))
in (_70_22800, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22801))
in (_70_22802)::[])
in (_70_22804)::_70_22803))))))
in (let mk_ref = (fun ( reft_name ) ( _52_1954 ) -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _70_22811 = (let _70_22810 = (let _70_22809 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_70_22809)::[])
in (reft_name, _70_22810))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22811))
in (let refb = (let _70_22814 = (let _70_22813 = (let _70_22812 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_70_22812)::[])
in (reft_name, _70_22813))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22814))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _70_22833 = (let _70_22820 = (let _70_22819 = (let _70_22818 = (let _70_22817 = (let _70_22816 = (let _70_22815 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _70_22815))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22816))
in ((typing_pred)::[], (xx)::(aa)::[], _70_22817))
in (mkForall_fuel _70_22818))
in (_70_22819, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22820))
in (let _70_22832 = (let _70_22831 = (let _70_22830 = (let _70_22829 = (let _70_22828 = (let _70_22827 = (let _70_22826 = (let _70_22825 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _70_22824 = (let _70_22823 = (let _70_22822 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _70_22821 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_70_22822, _70_22821)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_22823))
in (_70_22825, _70_22824)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22826))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _70_22827))
in (mkForall_fuel' 2 _70_22828))
in (_70_22829, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22830))
in (_70_22831)::[])
in (_70_22833)::_70_22832))))))))))
in (let mk_false_interp = (fun ( _52_1964 ) ( false_tm ) -> (let valid = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _70_22840 = (let _70_22839 = (let _70_22838 = (Microsoft_FStar_ToSMT_Term.mkIff (Microsoft_FStar_ToSMT_Term.mkFalse, valid))
in (_70_22838, Some ("False interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22839))
in (_70_22840)::[])))
in (let mk_and_interp = (fun ( conj ) ( _52_1970 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_22847 = (let _70_22846 = (let _70_22845 = (Microsoft_FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_70_22845)::[])
in ("Valid", _70_22846))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22847))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_22854 = (let _70_22853 = (let _70_22852 = (let _70_22851 = (let _70_22850 = (let _70_22849 = (let _70_22848 = (Microsoft_FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_70_22848, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22849))
in ((valid)::[], (aa)::(bb)::[], _70_22850))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22851))
in (_70_22852, Some ("/\\ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22853))
in (_70_22854)::[])))))))))
in (let mk_or_interp = (fun ( disj ) ( _52_1981 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_22861 = (let _70_22860 = (let _70_22859 = (Microsoft_FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_70_22859)::[])
in ("Valid", _70_22860))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22861))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_22868 = (let _70_22867 = (let _70_22866 = (let _70_22865 = (let _70_22864 = (let _70_22863 = (let _70_22862 = (Microsoft_FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_70_22862, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22863))
in ((valid)::[], (aa)::(bb)::[], _70_22864))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22865))
in (_70_22866, Some ("\\/ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22867))
in (_70_22868)::[])))))))))
in (let mk_eq2_interp = (fun ( eq2 ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _70_22875 = (let _70_22874 = (let _70_22873 = (Microsoft_FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_70_22873)::[])
in ("Valid", _70_22874))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22875))
in (let _70_22882 = (let _70_22881 = (let _70_22880 = (let _70_22879 = (let _70_22878 = (let _70_22877 = (let _70_22876 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (_70_22876, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22877))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _70_22878))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22879))
in (_70_22880, Some ("Eq2 interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22881))
in (_70_22882)::[])))))))))))
in (let mk_imp_interp = (fun ( imp ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_22889 = (let _70_22888 = (let _70_22887 = (Microsoft_FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_70_22887)::[])
in ("Valid", _70_22888))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22889))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_22896 = (let _70_22895 = (let _70_22894 = (let _70_22893 = (let _70_22892 = (let _70_22891 = (let _70_22890 = (Microsoft_FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_70_22890, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22891))
in ((valid)::[], (aa)::(bb)::[], _70_22892))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22893))
in (_70_22894, Some ("==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22895))
in (_70_22896)::[])))))))))
in (let mk_iff_interp = (fun ( iff ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_22903 = (let _70_22902 = (let _70_22901 = (Microsoft_FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_70_22901)::[])
in ("Valid", _70_22902))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22903))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_22910 = (let _70_22909 = (let _70_22908 = (let _70_22907 = (let _70_22906 = (let _70_22905 = (let _70_22904 = (Microsoft_FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_70_22904, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22905))
in ((valid)::[], (aa)::(bb)::[], _70_22906))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22907))
in (_70_22908, Some ("<==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22909))
in (_70_22910)::[])))))))))
in (let mk_forall_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _70_22917 = (let _70_22916 = (let _70_22915 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_70_22915)::[])
in ("Valid", _70_22916))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22917))
in (let valid_b_x = (let _70_22920 = (let _70_22919 = (let _70_22918 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_70_22918)::[])
in ("Valid", _70_22919))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22920))
in (let _70_22933 = (let _70_22932 = (let _70_22931 = (let _70_22930 = (let _70_22929 = (let _70_22928 = (let _70_22927 = (let _70_22926 = (let _70_22925 = (let _70_22921 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_22921)::[])
in (let _70_22924 = (let _70_22923 = (let _70_22922 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_22922, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22923))
in (_70_22925, (xx)::[], _70_22924)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22926))
in (_70_22927, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22928))
in ((valid)::[], (aa)::(bb)::[], _70_22929))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22930))
in (_70_22931, Some ("forall interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22932))
in (_70_22933)::[]))))))))))
in (let mk_exists_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _70_22940 = (let _70_22939 = (let _70_22938 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_70_22938)::[])
in ("Valid", _70_22939))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22940))
in (let valid_b_x = (let _70_22943 = (let _70_22942 = (let _70_22941 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_70_22941)::[])
in ("Valid", _70_22942))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22943))
in (let _70_22956 = (let _70_22955 = (let _70_22954 = (let _70_22953 = (let _70_22952 = (let _70_22951 = (let _70_22950 = (let _70_22949 = (let _70_22948 = (let _70_22944 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_22944)::[])
in (let _70_22947 = (let _70_22946 = (let _70_22945 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_22945, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22946))
in (_70_22948, (xx)::[], _70_22947)))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_22949))
in (_70_22950, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22951))
in ((valid)::[], (aa)::(bb)::[], _70_22952))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22953))
in (_70_22954, Some ("exists interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22955))
in (_70_22956)::[]))))))))))
in (let mk_foralltyp_interp = (fun ( for_all ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_22963 = (let _70_22962 = (let _70_22961 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_70_22961)::[])
in ("Valid", _70_22962))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22963))
in (let valid_a_b = (let _70_22966 = (let _70_22965 = (let _70_22964 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_70_22964)::[])
in ("Valid", _70_22965))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22966))
in (let _70_22979 = (let _70_22978 = (let _70_22977 = (let _70_22976 = (let _70_22975 = (let _70_22974 = (let _70_22973 = (let _70_22972 = (let _70_22971 = (let _70_22967 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_22967)::[])
in (let _70_22970 = (let _70_22969 = (let _70_22968 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_22968, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22969))
in (_70_22971, (bb)::[], _70_22970)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22972))
in (_70_22973, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22974))
in ((valid)::[], (kk)::(aa)::[], _70_22975))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22976))
in (_70_22977, Some ("ForallTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_22978))
in (_70_22979)::[]))))))))))
in (let mk_existstyp_interp = (fun ( for_some ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_22986 = (let _70_22985 = (let _70_22984 = (Microsoft_FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_70_22984)::[])
in ("Valid", _70_22985))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22986))
in (let valid_a_b = (let _70_22989 = (let _70_22988 = (let _70_22987 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_70_22987)::[])
in ("Valid", _70_22988))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_22989))
in (let _70_23002 = (let _70_23001 = (let _70_23000 = (let _70_22999 = (let _70_22998 = (let _70_22997 = (let _70_22996 = (let _70_22995 = (let _70_22994 = (let _70_22990 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_22990)::[])
in (let _70_22993 = (let _70_22992 = (let _70_22991 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_22991, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_22992))
in (_70_22994, (bb)::[], _70_22993)))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_22995))
in (_70_22996, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_22997))
in ((valid)::[], (kk)::(aa)::[], _70_22998))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_22999))
in (_70_23000, Some ("ExistsTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23001))
in (_70_23002)::[]))))))))))
in (let prims = ((Microsoft_FStar_Absyn_Const.unit_lid, mk_unit))::((Microsoft_FStar_Absyn_Const.bool_lid, mk_bool))::((Microsoft_FStar_Absyn_Const.int_lid, mk_int))::((Microsoft_FStar_Absyn_Const.string_lid, mk_str))::((Microsoft_FStar_Absyn_Const.ref_lid, mk_ref))::((Microsoft_FStar_Absyn_Const.char_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.uint8_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.false_lid, mk_false_interp))::((Microsoft_FStar_Absyn_Const.and_lid, mk_and_interp))::((Microsoft_FStar_Absyn_Const.or_lid, mk_or_interp))::((Microsoft_FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp_interp))::((Microsoft_FStar_Absyn_Const.iff_lid, mk_iff_interp))::((Microsoft_FStar_Absyn_Const.forall_lid, mk_forall_interp))::((Microsoft_FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun ( t ) ( s ) ( tt ) -> (match ((Support.Microsoft.FStar.Util.find_opt (fun ( _52_2074 ) -> (match (_52_2074) with
| (l, _52_2073) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some ((_52_2077, f)) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt = (fun ( env ) ( se ) -> (let _52_2083 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_23145 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") _70_23145))
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
in (let _52_2091 = (encode_sigelt' env se)
in (match (_52_2091) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _70_23148 = (let _70_23147 = (let _70_23146 = (Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_23146))
in (_70_23147)::[])
in (_70_23148, e))
end
| _52_2094 -> begin
(let _70_23155 = (let _70_23154 = (let _70_23150 = (let _70_23149 = (Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_23149))
in (_70_23150)::g)
in (let _70_23153 = (let _70_23152 = (let _70_23151 = (Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_23151))
in (_70_23152)::[])
in (Support.List.append _70_23154 _70_23153)))
in (_70_23155, e))
end)
end)))))
and encode_sigelt' = (fun ( env ) ( se ) -> (let should_skip = (fun ( l ) -> ((((Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.pure_") || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.ex_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.st_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.all_")))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_52_2100, _52_2102, _52_2104, _52_2106, Microsoft_FStar_Absyn_Syntax.Effect::[], _52_2110)) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _52_2115, _52_2117, _52_2119, _52_2121, _52_2123)) when (should_skip lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _52_2128, _52_2130, _52_2132, _52_2134, _52_2136)) when (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.b2t_lid) -> begin
(let _52_2142 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_52_2142) with
| (tname, ttok, env) -> begin
(let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _70_23160 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _70_23160))
in (let decls = (let _70_23168 = (let _70_23167 = (let _70_23166 = (let _70_23165 = (let _70_23164 = (let _70_23163 = (let _70_23162 = (let _70_23161 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _70_23161))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23162))
in ((valid_b2t_x)::[], (xx)::[], _70_23163))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23164))
in (_70_23165, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23166))
in (_70_23167)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_70_23168)
in (decls, env)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _52_2150, t, tags, _52_2154)) -> begin
(let _52_2160 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_52_2160) with
| (tname, ttok, env) -> begin
(let _52_2169 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((tps', body)) -> begin
((Support.List.append tps tps'), body)
end
| _52_2166 -> begin
(tps, t)
end)
in (match (_52_2169) with
| (tps, t) -> begin
(let _52_2176 = (encode_binders None tps env)
in (match (_52_2176) with
| (vars, guards, env', binder_decls, _52_2175) -> begin
(let tok_app = (let _70_23169 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _70_23169 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _70_23171 = (let _70_23170 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _70_23170))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23171))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _52_2182 -> begin
(let _70_23173 = (let _70_23172 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _70_23172))
in (_70_23173)::[])
end)
in (let decls = (let _70_23184 = (let _70_23177 = (let _70_23176 = (let _70_23175 = (let _70_23174 = (Support.List.map Support.Prims.snd vars)
in (tname, _70_23174, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_23175))
in (_70_23176)::(tok_decl)::[])
in (Support.List.append _70_23177 fresh_tok))
in (let _70_23183 = (let _70_23182 = (let _70_23181 = (let _70_23180 = (let _70_23179 = (let _70_23178 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _70_23178))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23179))
in (_70_23180, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23181))
in (_70_23182)::[])
in (Support.List.append _70_23184 _70_23183)))
in (let t = (whnf env t)
in (let _52_2194 = (match ((Support.All.pipe_right tags (Support.Microsoft.FStar.Util.for_some (fun ( _52_18 ) -> (match (_52_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _52_2189 -> begin
false
end))))) with
| true -> begin
(let _70_23187 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _70_23186 = (encode_formula t env')
in (_70_23187, _70_23186)))
end
| false -> begin
(let _70_23188 = (encode_typ_term t env')
in (app, _70_23188))
end)
in (match (_52_2194) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _70_23195 = (let _70_23194 = (let _70_23193 = (let _70_23192 = (let _70_23191 = (let _70_23190 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_23189 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_70_23190, _70_23189)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23191))
in ((def)::[], vars, _70_23192))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23193))
in (_70_23194, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23195))
in (let kindingAx = (let _52_2198 = (let _70_23196 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _70_23196 env' app))
in (match (_52_2198) with
| (k, decls) -> begin
(let _70_23204 = (let _70_23203 = (let _70_23202 = (let _70_23201 = (let _70_23200 = (let _70_23199 = (let _70_23198 = (let _70_23197 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_23197, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23198))
in ((app)::[], vars, _70_23199))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23200))
in (_70_23201, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23202))
in (_70_23203)::[])
in (Support.List.append decls _70_23204))
end))
in (let g = (let _70_23205 = (primitive_type_axioms lid tname app)
in (Support.List.append (Support.List.append (Support.List.append (Support.List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _70_23205))
in (g, env))))
end))))))))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _52_2205)) -> begin
(let tt = (whnf env t)
in (let _52_2211 = (encode_free_var env lid t tt quals)
in (match (_52_2211) with
| (decls, env) -> begin
(match (((Microsoft_FStar_Absyn_Util.is_smt_lemma t) && ((Support.All.pipe_right quals (Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption)) || env.tcenv.Microsoft_FStar_Tc_Env.is_iface))) with
| true -> begin
(let _70_23207 = (let _70_23206 = (encode_smt_lemma env lid t)
in (Support.List.append decls _70_23206))
in (_70_23207, env))
end
| false -> begin
(decls, env)
end)
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((l, f, _52_2215, _52_2217)) -> begin
(let _52_2222 = (encode_formula f env)
in (match (_52_2222) with
| (f, decls) -> begin
(let g = (let _70_23212 = (let _70_23211 = (let _70_23210 = (let _70_23209 = (let _70_23208 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "Assumption: %s" _70_23208))
in Some (_70_23209))
in (f, _70_23210))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23211))
in (_70_23212)::[])
in ((Support.List.append decls g), env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _52_2228, datas, quals, _52_2232)) when (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.precedes_lid) -> begin
(let _52_2238 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2238) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, _52_2241, _52_2243, _52_2245, _52_2247, _52_2249, _52_2251)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.char_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.Microsoft_FStar_Absyn_Syntax.str
in (let tsym = (Microsoft_FStar_ToSMT_Term.mkFreeV (tname, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((tname, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let _70_23214 = (let _70_23213 = (primitive_type_axioms t tname tsym)
in (decl)::_70_23213)
in (_70_23214, (push_free_tvar env t tname (Some (tsym))))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _52_2261, datas, quals, _52_2265)) -> begin
(let is_logical = (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_19 ) -> (match (_52_19) with
| (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _52_2272 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun ( c ) -> (match (is_logical) with
| true -> begin
(let _52_2282 = c
in (match (_52_2282) with
| (name, args, _52_2279, _52_2281) -> begin
(let _70_23220 = (let _70_23219 = (let _70_23218 = (Support.All.pipe_right args (Support.List.map Support.Prims.snd))
in (name, _70_23218, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_23219))
in (_70_23220)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun ( tapp ) ( vars ) -> (match ((((Support.List.length datas) = 0) || (Support.All.pipe_right datas (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (let _70_23226 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (Support.All.pipe_right _70_23226 Support.Option.isNone))))))) with
| true -> begin
[]
end
| false -> begin
(let _52_2289 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_2289) with
| (xxsym, xx) -> begin
(let _52_2332 = (Support.All.pipe_right datas (Support.List.fold_left (fun ( _52_2292 ) ( l ) -> (match (_52_2292) with
| (out, decls) -> begin
(let data_t = (Microsoft_FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _52_2302 = (match ((Microsoft_FStar_Absyn_Util.function_formals data_t)) with
| Some ((formals, res)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_52_2302) with
| (args, res) -> begin
(let indices = (match ((let _70_23229 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _70_23229.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_52_2304, indices)) -> begin
indices
end
| _52_2309 -> begin
[]
end)
in (let env = (Support.All.pipe_right args (Support.List.fold_left (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_23234 = (let _70_23233 = (let _70_23232 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_70_23232, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23233))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _70_23234))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_23237 = (let _70_23236 = (let _70_23235 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_70_23235, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23236))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _70_23237))
end)) env))
in (let _52_2320 = (encode_args indices env)
in (match (_52_2320) with
| (indices, decls') -> begin
(let _52_2321 = (match (((Support.List.length indices) <> (Support.List.length vars))) with
| true -> begin
(Support.All.failwith "Impossible")
end
| false -> begin
()
end)
in (let eqs = (let _70_23244 = (Support.List.map2 (fun ( v ) ( a ) -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_23241 = (let _70_23240 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_70_23240, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23241))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(let _70_23243 = (let _70_23242 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_70_23242, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23243))
end)) vars indices)
in (Support.All.pipe_right _70_23244 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _70_23249 = (let _70_23248 = (let _70_23247 = (let _70_23246 = (let _70_23245 = (mk_data_tester env l xx)
in (_70_23245, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_23246))
in (out, _70_23247))
in (Microsoft_FStar_ToSMT_Term.mkOr _70_23248))
in (_70_23249, (Support.List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_52_2332) with
| (data_ax, decls) -> begin
(let _52_2335 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2335) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _70_23250 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _70_23250 xx tapp))
in (let _70_23257 = (let _70_23256 = (let _70_23255 = (let _70_23254 = (let _70_23253 = (let _70_23252 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _70_23251 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _70_23252, _70_23251)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23253))
in (_70_23254, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23255))
in (_70_23256)::[])
in (Support.List.append decls _70_23257)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _52_2347 = (match ((let _70_23258 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _70_23258.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, res)) -> begin
(true, bs, res)
end
| _52_2343 -> begin
(false, [], k)
end)
in (match (_52_2347) with
| (is_kind_arrow, formals, res) -> begin
(let _52_2354 = (encode_binders None formals env)
in (match (_52_2354) with
| (vars, guards, env', binder_decls, _52_2353) -> begin
(let projection_axioms = (fun ( tapp ) ( vars ) -> (match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.find_opt (fun ( _52_20 ) -> (match (_52_20) with
| Microsoft_FStar_Absyn_Syntax.Projector (_52_2360) -> begin
true
end
| _52_2363 -> begin
false
end))))) with
| Some (Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inl (a)))) -> begin
(let rec projectee = (fun ( i ) ( _52_21 ) -> (match (_52_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (_52_2378) -> begin
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
in (let _52_2393 = (match ((Support.Microsoft.FStar.Util.first_N projectee_pos vars)) with
| (_52_2384, xx::suffix) -> begin
(xx, suffix)
end
| _52_2390 -> begin
(Support.All.failwith "impossible")
end)
in (match (_52_2393) with
| (xx, suffix) -> begin
(let dproj_app = (let _70_23272 = (let _70_23271 = (let _70_23270 = (mk_typ_projector_name d a)
in (let _70_23269 = (let _70_23268 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_70_23268)::[])
in (_70_23270, _70_23269)))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23271))
in (mk_ApplyT _70_23272 suffix))
in (let _70_23277 = (let _70_23276 = (let _70_23275 = (let _70_23274 = (let _70_23273 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _70_23273))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23274))
in (_70_23275, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23276))
in (_70_23277)::[]))
end))))
end
| _52_2396 -> begin
[]
end))
in (let pretype_axioms = (fun ( tapp ) ( vars ) -> (let _52_2402 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_52_2402) with
| (xxsym, xx) -> begin
(let _52_2405 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2405) with
| (ffsym, ff) -> begin
(let xx_has_type = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _70_23290 = (let _70_23289 = (let _70_23288 = (let _70_23287 = (let _70_23286 = (let _70_23285 = (let _70_23284 = (let _70_23283 = (let _70_23282 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _70_23282))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23283))
in (xx_has_type, _70_23284))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23285))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _70_23286))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23287))
in (_70_23288, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23289))
in (_70_23290)::[]))
end))
end)))
in (let _52_2410 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2410) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _70_23292 = (let _70_23291 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _70_23291))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23292))
in (let _52_2435 = (let tname_decl = (let _70_23296 = (let _70_23295 = (Support.All.pipe_right vars (Support.List.map (fun ( _52_2416 ) -> (match (_52_2416) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))))
in (let _70_23294 = (varops.next_id ())
in (tname, _70_23295, Microsoft_FStar_ToSMT_Term.Type_sort, _70_23294)))
in (constructor_or_logic_type_decl _70_23296))
in (let _52_2432 = (match (vars) with
| [] -> begin
(let _70_23300 = (let _70_23299 = (let _70_23298 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (Support.All.pipe_left (fun ( _70_23297 ) -> Some (_70_23297)) _70_23298))
in (push_free_tvar env t tname _70_23299))
in ([], _70_23300))
end
| _52_2420 -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _70_23301 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _70_23301))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = (match (((not (is_logical)) && (Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_22 ) -> (match (_52_22) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _52_2427 -> begin
false
end)))))) with
| true -> begin
((ttok_app)::[])::((tapp)::[])::[]
end
| false -> begin
((ttok_app)::[])::[]
end)
in (let name_tok_corr = (let _70_23306 = (let _70_23305 = (let _70_23304 = (let _70_23303 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _70_23303))
in (Microsoft_FStar_ToSMT_Term.mkForall' _70_23304))
in (_70_23305, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23306))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_52_2432) with
| (tok_decls, env) -> begin
((Support.List.append tname_decl tok_decls), env)
end)))
in (match (_52_2435) with
| (decls, env) -> begin
(let kindingAx = (let _52_2438 = (encode_knd res env' tapp)
in (match (_52_2438) with
| (k, decls) -> begin
(let karr = (match (is_kind_arrow) with
| true -> begin
(let _70_23310 = (let _70_23309 = (let _70_23308 = (let _70_23307 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_23307))
in (_70_23308, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23309))
in (_70_23310)::[])
end
| false -> begin
[]
end)
in (let _70_23316 = (let _70_23315 = (let _70_23314 = (let _70_23313 = (let _70_23312 = (let _70_23311 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _70_23311))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23312))
in (_70_23313, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23314))
in (_70_23315)::[])
in (Support.List.append (Support.List.append decls karr) _70_23316)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _70_23317 = (projection_axioms tapp vars)
in (Support.List.append kindingAx _70_23317))
end
| false -> begin
(let _70_23324 = (let _70_23322 = (let _70_23320 = (let _70_23318 = (primitive_type_axioms t tname tapp)
in (Support.List.append kindingAx _70_23318))
in (let _70_23319 = (inversion_axioms tapp vars)
in (Support.List.append _70_23320 _70_23319)))
in (let _70_23321 = (projection_axioms tapp vars)
in (Support.List.append _70_23322 _70_23321)))
in (let _70_23323 = (pretype_axioms tapp vars)
in (Support.List.append _70_23324 _70_23323)))
end)
in (let g = (Support.List.append (Support.List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, _52_2445, _52_2447, _52_2449, _52_2451, _52_2453)) when (Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, t, _52_2459, quals, _52_2462, drange)) -> begin
(let _52_2469 = (new_term_constant_and_tok_from_lid env d)
in (match (_52_2469) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _52_2478 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(f, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_52_2478) with
| (formals, t_res) -> begin
(let _52_2481 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2481) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _52_2488 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_52_2488) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (Support.All.pipe_right names (Support.List.map (fun ( _52_23 ) -> (match (_52_23) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_23326 = (mk_typ_projector_name d a)
in (_70_23326, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_23327 = (mk_term_projector_name d x)
in (_70_23327, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _70_23329 = (let _70_23328 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _70_23328))
in (Support.All.pipe_right _70_23329 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _52_2502 = (encode_typ_pred' None t env ddtok_tm)
in (match (_52_2502) with
| (tok_typing, decls3) -> begin
(let _52_2509 = (encode_binders (Some (s_fuel_tm)) formals env)
in (match (_52_2509) with
| (vars', guards', env'', decls_formals, _52_2508) -> begin
(let _52_2514 = (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred' (Some (fuel_tm)) t_res env'' dapp)))
in (match (_52_2514) with
| (ty_pred', decls_pred) -> begin
(let guard' = (Microsoft_FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _52_2518 -> begin
(let _70_23331 = (let _70_23330 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _70_23330))
in (_70_23331)::[])
end)
in (let encode_elim = (fun ( _52_2521 ) -> (match (()) with
| () -> begin
(let _52_2524 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_52_2524) with
| (head, args) -> begin
(match ((let _70_23334 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _70_23334.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _52_2530 = (encode_args args env')
in (match (_52_2530) with
| (encoded_args, arg_decls) -> begin
(let _52_2554 = (Support.List.fold_left (fun ( _52_2534 ) ( arg ) -> (match (_52_2534) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _52_2542 = (let _70_23337 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _70_23337))
in (match (_52_2542) with
| (_52_2539, tv, env) -> begin
(let _70_23339 = (let _70_23338 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_70_23338)::eqns)
in (env, (tv)::arg_vars, _70_23339))
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _52_2549 = (let _70_23340 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _70_23340))
in (match (_52_2549) with
| (_52_2546, xv, env) -> begin
(let _70_23342 = (let _70_23341 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_70_23341)::eqns)
in (env, (xv)::arg_vars, _70_23342))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_52_2554) with
| (_52_2551, arg_vars, eqns) -> begin
(let arg_vars = (Support.List.rev arg_vars)
in (let ty = (Microsoft_FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (Support.List.map Microsoft_FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _70_23349 = (let _70_23348 = (let _70_23347 = (let _70_23346 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _70_23345 = (let _70_23344 = (let _70_23343 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards))
in (ty_pred, _70_23343))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23344))
in ((ty_pred)::[], _70_23346, _70_23345)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23347))
in (_70_23348, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23349))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _70_23350 = (varops.fresh "x")
in (_70_23350, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _70_23359 = (let _70_23358 = (let _70_23357 = (let _70_23356 = (let _70_23351 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_70_23351)::[])
in (let _70_23355 = (let _70_23354 = (let _70_23353 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _70_23352 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_70_23353, _70_23352)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23354))
in (_70_23356, (x)::[], _70_23355)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23357))
in (_70_23358, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23359))))
end
| false -> begin
(let prec = (Support.All.pipe_right vars (Support.List.collect (fun ( v ) -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _70_23362 = (let _70_23361 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _70_23361 dapp))
in (_70_23362)::[])
end
| _52_2569 -> begin
(Support.All.failwith "unexpected sort")
end))))
in (let _70_23369 = (let _70_23368 = (let _70_23367 = (let _70_23366 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _70_23365 = (let _70_23364 = (let _70_23363 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _70_23363))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23364))
in ((ty_pred)::[], _70_23366, _70_23365)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23367))
in (_70_23368, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23369)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _52_2573 -> begin
(let _52_2574 = (let _70_23372 = (let _70_23371 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _70_23370 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" _70_23371 _70_23370)))
in (Microsoft_FStar_Tc_Errors.warn drange _70_23372))
in ([], []))
end)
end))
end))
in (let _52_2578 = (encode_elim ())
in (match (_52_2578) with
| (decls2, elim) -> begin
(let g = (let _70_23397 = (let _70_23396 = (let _70_23381 = (let _70_23380 = (let _70_23379 = (let _70_23378 = (let _70_23377 = (let _70_23376 = (let _70_23375 = (let _70_23374 = (let _70_23373 = (Microsoft_FStar_Absyn_Print.sli d)
in (Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" _70_23373))
in Some (_70_23374))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _70_23375))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_23376))
in (_70_23377)::[])
in (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) _70_23378))
in (Support.List.append _70_23379 proxy_fresh))
in (Support.List.append _70_23380 decls_formals))
in (Support.List.append _70_23381 decls_pred))
in (let _70_23395 = (let _70_23394 = (let _70_23393 = (let _70_23385 = (let _70_23384 = (let _70_23383 = (let _70_23382 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _70_23382))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23383))
in (_70_23384, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23385))
in (let _70_23392 = (let _70_23391 = (let _70_23390 = (let _70_23389 = (let _70_23388 = (let _70_23387 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _70_23386 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _70_23387, _70_23386)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23388))
in (_70_23389, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23390))
in (_70_23391)::[])
in (_70_23393)::_70_23392))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_70_23394)
in (Support.List.append _70_23396 _70_23395)))
in (Support.List.append _70_23397 elim))
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
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _52_2582, _52_2584, _52_2586)) -> begin
(let _52_2591 = (encode_signature env ses)
in (match (_52_2591) with
| (g, env) -> begin
(let _52_2603 = (Support.All.pipe_right g (Support.List.partition (fun ( _52_24 ) -> (match (_52_24) with
| Microsoft_FStar_ToSMT_Term.Assume ((_52_2594, Some ("inversion axiom"))) -> begin
false
end
| _52_2600 -> begin
true
end))))
in (match (_52_2603) with
| (g', inversions) -> begin
(let _52_2612 = (Support.All.pipe_right g' (Support.List.partition (fun ( _52_25 ) -> (match (_52_25) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_52_2606) -> begin
true
end
| _52_2609 -> begin
false
end))))
in (match (_52_2612) with
| (decls, rest) -> begin
((Support.List.append (Support.List.append decls rest) inversions), env)
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((is_rec, bindings), _52_2617, _52_2619, quals)) -> begin
(let eta_expand = (fun ( binders ) ( formals ) ( body ) ( t ) -> (let nbinders = (Support.List.length binders)
in (let _52_2631 = (Support.Microsoft.FStar.Util.first_N nbinders formals)
in (match (_52_2631) with
| (formals, extra_formals) -> begin
(let subst = (Support.List.map2 (fun ( formal ) ( binder ) -> (match (((Support.Prims.fst formal), (Support.Prims.fst binder))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
(let _70_23411 = (let _70_23410 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _70_23410))
in Support.Microsoft.FStar.Util.Inl (_70_23411))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _70_23413 = (let _70_23412 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_23412))
in Support.Microsoft.FStar.Util.Inr (_70_23413))
end
| _52_2645 -> begin
(Support.All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _70_23414 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (Support.All.pipe_right _70_23414 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _70_23420 = (let _70_23416 = (let _70_23415 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (Support.All.pipe_left Support.Prims.snd _70_23415))
in (body, _70_23416))
in (let _70_23419 = (let _70_23418 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (Support.All.pipe_left (fun ( _70_23417 ) -> Some (_70_23417)) _70_23418))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _70_23420 _70_23419 body.Microsoft_FStar_Absyn_Syntax.pos)))
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
(let _52_2683 = (Support.Microsoft.FStar.Util.first_N nformals binders)
in (match (_52_2683) with
| (bs0, rest) -> begin
(let tres = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tres)
end
| _52_2687 -> begin
(Support.All.failwith "impossible")
end)
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end
| false -> begin
(match ((nformals > nbinders)) with
| true -> begin
(let _52_2692 = (eta_expand binders formals body tres)
in (match (_52_2692) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end
| false -> begin
(binders, body, formals, tres)
end)
end))))
end
| _52_2694 -> begin
(let _70_23429 = (let _70_23428 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _70_23427 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _70_23428 _70_23427)))
in (Support.All.failwith _70_23429))
end)
end
| _52_2696 -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (let _52_2704 = (eta_expand [] formals e tres)
in (match (_52_2704) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _52_2706 -> begin
([], e, [], t_norm)
end)
end))
in (Support.All.try_with (fun ( _52_2708 ) -> (match (()) with
| () -> begin
(match ((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_26 ) -> (match (_52_26) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _52_2719 -> begin
false
end))))) with
| true -> begin
([], env)
end
| false -> begin
(match ((Support.All.pipe_right bindings (Support.Microsoft.FStar.Util.for_some (fun ( lb ) -> (Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp))))) with
| true -> begin
(let _70_23435 = (Support.All.pipe_right bindings (Support.List.collect (fun ( lb ) -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _70_23434 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _70_23434 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(raise (Let_rec_unencodeable))
end))))
in (_70_23435, env))
end
| false -> begin
(let _52_2739 = (Support.All.pipe_right bindings (Support.List.fold_left (fun ( _52_2726 ) ( lb ) -> (match (_52_2726) with
| (toks, typs, decls, env) -> begin
(let _52_2728 = (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(raise (Let_rec_unencodeable))
end
| false -> begin
()
end)
in (let t_norm = (let _70_23438 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.All.pipe_right _70_23438 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _52_2734 = (let _70_23439 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _70_23439 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_52_2734) with
| (tok, decl, env) -> begin
(let _70_23442 = (let _70_23441 = (let _70_23440 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_70_23440, tok))
in (_70_23441)::toks)
in (_70_23442, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_52_2739) with
| (toks, typs, decls, env) -> begin
(let toks = (Support.List.rev toks)
in (let decls = (Support.All.pipe_right (Support.List.rev decls) Support.List.flatten)
in (let typs = (Support.List.rev typs)
in (match (((Support.All.pipe_right quals (Support.Microsoft.FStar.Util.for_some (fun ( _52_27 ) -> (match (_52_27) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _52_2746 -> begin
false
end)))) || (Support.All.pipe_right typs (Support.Microsoft.FStar.Util.for_some (fun ( t ) -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (let _70_23445 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (Support.All.pipe_left Support.Prims.op_Negation _70_23445)))))))) with
| true -> begin
(decls, env)
end
| false -> begin
(match ((not (is_rec))) with
| true -> begin
(match ((bindings, typs, toks)) with
| ({Microsoft_FStar_Absyn_Syntax.lbname = _52_2754; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_2752; Microsoft_FStar_Absyn_Syntax.lbeff = _52_2750; Microsoft_FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _52_2770 = (destruct_bound_function flid t_norm e)
in (match (_52_2770) with
| (binders, body, formals, tres) -> begin
(let _52_2777 = (encode_binders None binders env)
in (match (_52_2777) with
| (vars, guards, env', binder_decls, _52_2776) -> begin
(let app = (match (vars) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _52_2780 -> begin
(let _70_23447 = (let _70_23446 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _70_23446))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23447))
end)
in (let _52_2784 = (encode_exp body env')
in (match (_52_2784) with
| (body, decls2) -> begin
(let eqn = (let _70_23456 = (let _70_23455 = (let _70_23452 = (let _70_23451 = (let _70_23450 = (let _70_23449 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_23448 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_23449, _70_23448)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23450))
in ((app)::[], vars, _70_23451))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23452))
in (let _70_23454 = (let _70_23453 = (Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_70_23453))
in (_70_23455, _70_23454)))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23456))
in ((Support.List.append (Support.List.append (Support.List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _52_2787 -> begin
(Support.All.failwith "Impossible")
end)
end
| false -> begin
(let fuel = (let _70_23457 = (varops.fresh "fuel")
in (_70_23457, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _52_2804 = (Support.All.pipe_right toks (Support.List.fold_left (fun ( _52_2793 ) ( _52_2798 ) -> (match ((_52_2793, _52_2798)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _70_23462 = (let _70_23461 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (Support.All.pipe_left (fun ( _70_23460 ) -> Some (_70_23460)) _70_23461))
in (push_free_var env flid gtok _70_23462))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_52_2804) with
| (gtoks, env) -> begin
(let gtoks = (Support.List.rev gtoks)
in (let encode_one_binding = (fun ( env0 ) ( _52_2813 ) ( t_norm ) ( _52_2822 ) -> (match ((_52_2813, _52_2822)) with
| ((flid, f, ftok, g, gtok), {Microsoft_FStar_Absyn_Syntax.lbname = _52_2821; Microsoft_FStar_Absyn_Syntax.lbtyp = _52_2819; Microsoft_FStar_Absyn_Syntax.lbeff = _52_2817; Microsoft_FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _52_2827 = (destruct_bound_function flid t_norm e)
in (match (_52_2827) with
| (binders, body, formals, tres) -> begin
(let _52_2834 = (encode_binders None binders env)
in (match (_52_2834) with
| (vars, guards, env', binder_decls, _52_2833) -> begin
(let decl_g = (let _70_23473 = (let _70_23472 = (let _70_23471 = (Support.List.map Support.Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_70_23471)
in (g, _70_23472, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_23473))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _70_23476 = (let _70_23475 = (let _70_23474 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_70_23474)::vars_tm)
in (g, _70_23475))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23476))
in (let gmax = (let _70_23479 = (let _70_23478 = (let _70_23477 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_70_23477)::vars_tm)
in (g, _70_23478))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23479))
in (let _52_2844 = (encode_exp body env')
in (match (_52_2844) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _70_23488 = (let _70_23487 = (let _70_23484 = (let _70_23483 = (let _70_23482 = (let _70_23481 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_23480 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_70_23481, _70_23480)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23482))
in ((gsapp)::[], (fuel)::vars, _70_23483))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23484))
in (let _70_23486 = (let _70_23485 = (Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_70_23485))
in (_70_23487, _70_23486)))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23488))
in (let eqn_f = (let _70_23492 = (let _70_23491 = (let _70_23490 = (let _70_23489 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _70_23489))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23490))
in (_70_23491, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23492))
in (let eqn_g' = (let _70_23501 = (let _70_23500 = (let _70_23499 = (let _70_23498 = (let _70_23497 = (let _70_23496 = (let _70_23495 = (let _70_23494 = (let _70_23493 = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (_70_23493)::vars_tm)
in (g, _70_23494))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23495))
in (gsapp, _70_23496))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23497))
in ((gsapp)::[], (fuel)::vars, _70_23498))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23499))
in (_70_23500, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23501))
in (let _52_2867 = (let _52_2854 = (encode_binders None formals env0)
in (match (_52_2854) with
| (vars, v_guards, env, binder_decls, _52_2853) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _70_23502 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _70_23502 ((fuel)::vars)))
in (let _70_23506 = (let _70_23505 = (let _70_23504 = (let _70_23503 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _70_23503))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23504))
in (_70_23505, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23506)))
in (let _52_2864 = (let _52_2861 = (encode_typ_pred' None tres env gapp)
in (match (_52_2861) with
| (g_typing, d3) -> begin
(let _70_23514 = (let _70_23513 = (let _70_23512 = (let _70_23511 = (let _70_23510 = (let _70_23509 = (let _70_23508 = (let _70_23507 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_70_23507, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_23508))
in ((gapp)::[], (fuel)::vars, _70_23509))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23510))
in (_70_23511, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23512))
in (_70_23513)::[])
in (d3, _70_23514))
end))
in (match (_52_2864) with
| (aux_decls, typing_corr) -> begin
((Support.List.append binder_decls aux_decls), (Support.List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_52_2867) with
| (aux_decls, g_typing) -> begin
((Support.List.append (Support.List.append (Support.List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (Support.List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _52_2883 = (let _70_23517 = (Support.List.zip3 gtoks typs bindings)
in (Support.List.fold_left (fun ( _52_2871 ) ( _52_2875 ) -> (match ((_52_2871, _52_2875)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _52_2879 = (encode_one_binding env0 gtok ty bs)
in (match (_52_2879) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _70_23517))
in (match (_52_2883) with
| (decls, eqns, env0) -> begin
(let _52_2892 = (let _70_23519 = (Support.All.pipe_right decls Support.List.flatten)
in (Support.All.pipe_right _70_23519 (Support.List.partition (fun ( _52_28 ) -> (match (_52_28) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_52_2886) -> begin
true
end
| _52_2889 -> begin
false
end)))))
in (match (_52_2892) with
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
end)) (fun ( _52_2707 ) -> (match (_52_2707) with
| Let_rec_unencodeable -> begin
(let msg = (let _70_23522 = (Support.All.pipe_right bindings (Support.List.map (fun ( lb ) -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (Support.All.pipe_right _70_23522 (Support.String.concat " and ")))
in (let decl = Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun ( env ) ( x ) ( t ) ( t_norm ) -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _52_2919 = (encode_free_var env x t t_norm [])
in (match (_52_2919) with
| (decls, env) -> begin
(let _52_2924 = (lookup_lid env x)
in (match (_52_2924) with
| (n, x', _52_2923) -> begin
((n, x'), decls, env)
end))
end))
end
| Some ((n, x, _52_2928)) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun ( env ) ( lid ) ( t ) -> (let _52_2936 = (encode_function_type_as_formula None t env)
in (match (_52_2936) with
| (form, decls) -> begin
(Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume ((form, Some ((Support.String.strcat "Lemma: " lid.Microsoft_FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun ( env ) ( lid ) ( tt ) ( t_norm ) ( quals ) -> (match (((let _70_23535 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (Support.All.pipe_left Support.Prims.op_Negation _70_23535)) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm))) with
| true -> begin
(let _52_2945 = (new_term_constant_and_tok_from_lid env lid)
in (match (_52_2945) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _52_2948)) -> begin
(Support.All.pipe_right binders (Support.List.map (fun ( _52_29 ) -> (match (_52_29) with
| (Support.Microsoft.FStar.Util.Inl (_52_2953), _52_2956) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_2959 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
end
| _52_2961 -> begin
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
in (let _52_2978 = (match ((Microsoft_FStar_Absyn_Util.function_formals t_norm)) with
| Some ((args, comp)) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(let _70_23537 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _70_23537))
end
| false -> begin
(args, (None, (Microsoft_FStar_Absyn_Util.comp_result comp)))
end)
end
| None -> begin
([], (None, t_norm))
end)
in (match (_52_2978) with
| (formals, (pre_opt, res_t)) -> begin
(let _52_2982 = (new_term_constant_and_tok_from_lid env lid)
in (match (_52_2982) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _52_2985 -> begin
(Microsoft_FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun ( vapp ) ( vars ) -> (Support.All.pipe_right quals (Support.List.collect (fun ( _52_30 ) -> (match (_52_30) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _52_2999 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_52_2999) with
| (_52_2994, (xxsym, _52_2997)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _70_23550 = (let _70_23549 = (let _70_23548 = (let _70_23547 = (let _70_23546 = (let _70_23545 = (let _70_23544 = (let _70_23543 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_23543))
in (vapp, _70_23544))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23545))
in ((vapp)::[], vars, _70_23546))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23547))
in (_70_23548, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23549))
in (_70_23550)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _52_3012 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_52_3012) with
| (_52_3007, (xxsym, _52_3010)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _70_23559 = (let _70_23558 = (let _70_23557 = (let _70_23556 = (let _70_23555 = (let _70_23554 = (let _70_23553 = (let _70_23552 = (let _70_23551 = (mk_term_projector_name d f)
in (_70_23551, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23552))
in (vapp, _70_23553))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23554))
in ((vapp)::[], vars, _70_23555))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23556))
in (_70_23557, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23558))
in (_70_23559)::[]))
end))
end
| _52_3015 -> begin
[]
end)))))
in (let _52_3022 = (encode_binders None formals env)
in (match (_52_3022) with
| (vars, guards, env', decls1, _52_3021) -> begin
(let _52_3031 = (match (pre_opt) with
| None -> begin
(let _70_23560 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_23560, decls1))
end
| Some (p) -> begin
(let _52_3028 = (encode_formula p env')
in (match (_52_3028) with
| (g, ds) -> begin
(let _70_23561 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_70_23561, (Support.List.append decls1 ds)))
end))
end)
in (match (_52_3031) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _70_23563 = (let _70_23562 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _70_23562))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_23563))
in (let _52_3062 = (let vname_decl = (let _70_23566 = (let _70_23565 = (Support.All.pipe_right formals (Support.List.map (fun ( _52_31 ) -> (match (_52_31) with
| (Support.Microsoft.FStar.Util.Inl (_52_3036), _52_3039) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_3042 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _70_23565, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_23566))
in (let _52_3049 = (let env = (let _52_3044 = env
in {bindings = _52_3044.bindings; depth = _52_3044.depth; tcenv = _52_3044.tcenv; warn = _52_3044.warn; cache = _52_3044.cache; nolabels = _52_3044.nolabels; use_zfuel_name = _52_3044.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (match ((not ((head_normal env tt)))) with
| true -> begin
(encode_typ_pred' None tt env vtok_tm)
end
| false -> begin
(encode_typ_pred' None t_norm env vtok_tm)
end))
in (match (_52_3049) with
| (tok_typing, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _52_3059 = (match (formals) with
| [] -> begin
(let _70_23570 = (let _70_23569 = (let _70_23568 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Support.All.pipe_left (fun ( _70_23567 ) -> Some (_70_23567)) _70_23568))
in (push_free_var env lid vname _70_23569))
in ((Support.List.append decls2 ((tok_typing)::[])), _70_23570))
end
| _52_3053 -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _70_23571 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _70_23571))
in (let name_tok_corr = (let _70_23575 = (let _70_23574 = (let _70_23573 = (let _70_23572 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _70_23572))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23573))
in (_70_23574, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23575))
in ((Support.List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_52_3059) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_52_3062) with
| (decls2, env) -> begin
(let _52_3065 = (encode_typ_pred' None res_t env' vapp)
in (match (_52_3065) with
| (ty_pred, decls3) -> begin
(let typingAx = (let _70_23579 = (let _70_23578 = (let _70_23577 = (let _70_23576 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _70_23576))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_23577))
in (_70_23578, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23579))
in (let g = (let _70_23581 = (let _70_23580 = (mk_disc_proj_axioms vapp vars)
in (typingAx)::_70_23580)
in (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) _70_23581))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end)
end))
and encode_signature = (fun ( env ) ( ses ) -> (Support.All.pipe_right ses (Support.List.fold_left (fun ( _52_3072 ) ( se ) -> (match (_52_3072) with
| (g, env) -> begin
(let _52_3076 = (encode_sigelt env se)
in (match (_52_3076) with
| (g', env) -> begin
((Support.List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings = (fun ( env ) ( bindings ) -> (let encode_binding = (fun ( b ) ( _52_3083 ) -> (match (_52_3083) with
| (decls, env) -> begin
(match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t0)) -> begin
(let _52_3091 = (new_term_constant env x)
in (match (_52_3091) with
| (xxsym, xx, env') -> begin
(let t1 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _52_3095 = (encode_typ_pred' None t1 env xx)
in (match (_52_3095) with
| (t, decls') -> begin
(let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_23597 = (let _70_23596 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _70_23595 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _70_23594 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" _70_23596 _70_23595 _70_23594))))
in Some (_70_23597))
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
(let _52_3105 = (new_typ_constant env a)
in (match (_52_3105) with
| (aasym, aa, env') -> begin
(let _52_3108 = (encode_knd k env aa)
in (match (_52_3108) with
| (k, decls') -> begin
(let g = (let _70_23603 = (let _70_23602 = (let _70_23601 = (let _70_23600 = (let _70_23599 = (let _70_23598 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_70_23598))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _70_23599))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_23600))
in (_70_23601)::[])
in (Support.List.append _70_23602 decls'))
in (Support.List.append _70_23603 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((Support.List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((x, t)) -> begin
(let t_norm = (whnf env t)
in (let _52_3117 = (encode_free_var env x t t_norm [])
in (match (_52_3117) with
| (g, env') -> begin
((Support.List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _52_3122 = (encode_sigelt env se)
in (match (_52_3122) with
| (g, env') -> begin
((Support.List.append decls g), env')
end))
end)
end))
in (Support.List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun ( labs ) -> (let prefix = (Support.All.pipe_right labs (Support.List.map (fun ( _52_3129 ) -> (match (_52_3129) with
| (l, _52_3126, _52_3128) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Support.Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (Support.All.pipe_right labs (Support.List.collect (fun ( _52_3136 ) -> (match (_52_3136) with
| (l, _52_3133, _52_3135) -> begin
(let _70_23611 = (Support.All.pipe_left (fun ( _70_23607 ) -> Microsoft_FStar_ToSMT_Term.Echo (_70_23607)) (Support.Prims.fst l))
in (let _70_23610 = (let _70_23609 = (let _70_23608 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_70_23608))
in (_70_23609)::[])
in (_70_23611)::_70_23610))
end))))
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun ( tcenv ) -> (let _70_23616 = (let _70_23615 = (let _70_23614 = (Support.Microsoft.FStar.Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _70_23614; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_70_23615)::[])
in (Support.ST.op_Colon_Equals last_env _70_23616)))

let get_env = (fun ( tcenv ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "No env; call init first!")
end
| e::_52_3142 -> begin
(let _52_3145 = e
in {bindings = _52_3145.bindings; depth = _52_3145.depth; tcenv = tcenv; warn = _52_3145.warn; cache = _52_3145.cache; nolabels = _52_3145.nolabels; use_zfuel_name = _52_3145.use_zfuel_name; encode_non_total_function_typ = _52_3145.encode_non_total_function_typ})
end))

let set_env = (fun ( env ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Empty env stack")
end
| _52_3151::tl -> begin
(Support.ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun ( _52_3153 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Empty env stack")
end
| hd::tl -> begin
(let _52_3158 = (Microsoft_FStar_ToSMT_Term.push ())
in (let refs = (Support.Microsoft.FStar.Util.smap_copy hd.cache)
in (let top = (let _52_3161 = hd
in {bindings = _52_3161.bindings; depth = _52_3161.depth; tcenv = _52_3161.tcenv; warn = _52_3161.warn; cache = refs; nolabels = _52_3161.nolabels; use_zfuel_name = _52_3161.use_zfuel_name; encode_non_total_function_typ = _52_3161.encode_non_total_function_typ})
in (Support.ST.op_Colon_Equals last_env ((top)::(hd)::tl)))))
end)
end))

let pop_env = (fun ( _52_3164 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Popping an empty stack")
end
| _52_3168::tl -> begin
(let _52_3170 = (Microsoft_FStar_ToSMT_Term.pop ())
in (Support.ST.op_Colon_Equals last_env tl))
end)
end))

let mark_env = (fun ( _52_3172 ) -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun ( _52_3173 ) -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun ( _52_3174 ) -> (match (()) with
| () -> begin
(let _52_3175 = (Microsoft_FStar_ToSMT_Term.commit_mark ())
in (match ((Support.ST.read last_env)) with
| hd::_52_3179::tl -> begin
(Support.ST.op_Colon_Equals last_env ((hd)::tl))
end
| _52_3184 -> begin
(Support.All.failwith "Impossible")
end))
end))

let init = (fun ( tcenv ) -> (let _52_3186 = (init_env tcenv)
in (let _52_3188 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun ( msg ) -> (let _52_3191 = (push_env ())
in (let _52_3193 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun ( msg ) -> (let _52_3196 = (let _70_23637 = (pop_env ())
in (Support.All.pipe_left Support.Prims.ignore _70_23637))
in (let _52_3198 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun ( msg ) -> (let _52_3201 = (mark_env ())
in (let _52_3203 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun ( msg ) -> (let _52_3206 = (reset_mark_env ())
in (let _52_3208 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun ( msg ) -> (let _52_3211 = (commit_mark_env ())
in (let _52_3213 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun ( tcenv ) ( se ) -> (let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_23651 = (let _70_23650 = (let _70_23649 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.String.strcat "encoding sigelt " _70_23649))
in Microsoft_FStar_ToSMT_Term.Caption (_70_23650))
in (_70_23651)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _52_3222 = (encode_sigelt env se)
in (match (_52_3222) with
| (decls, env) -> begin
(let _52_3223 = (set_env env)
in (let _70_23652 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _70_23652)))
end)))))

let encode_modul = (fun ( tcenv ) ( modul ) -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _52_3228 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_23657 = (Support.All.pipe_right (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name _70_23657))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _52_3235 = (encode_signature (let _52_3231 = env
in {bindings = _52_3231.bindings; depth = _52_3231.depth; tcenv = _52_3231.tcenv; warn = false; cache = _52_3231.cache; nolabels = _52_3231.nolabels; use_zfuel_name = _52_3231.use_zfuel_name; encode_non_total_function_typ = _52_3231.encode_non_total_function_typ}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_52_3235) with
| (decls, env) -> begin
(let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let msg = (Support.String.strcat "Externals for " name)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _52_3241 = (set_env (let _52_3239 = env
in {bindings = _52_3239.bindings; depth = _52_3239.depth; tcenv = _52_3239.tcenv; warn = true; cache = _52_3239.cache; nolabels = _52_3239.nolabels; use_zfuel_name = _52_3239.use_zfuel_name; encode_non_total_function_typ = _52_3239.encode_non_total_function_typ}))
in (let _52_3243 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun ( tcenv ) ( q ) -> (let _52_3248 = (let _70_23666 = (let _70_23665 = (let _70_23664 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_23664))
in (Support.Microsoft.FStar.Util.format1 "Starting query at %s" _70_23665))
in (push _70_23666))
in (let pop = (fun ( _52_3251 ) -> (match (()) with
| () -> begin
(let _70_23671 = (let _70_23670 = (let _70_23669 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_23669))
in (Support.Microsoft.FStar.Util.format1 "Ending query at %s" _70_23670))
in (pop _70_23671))
end))
in (let _52_3281 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun ( bs ) ( b ) -> (b)::bs) [])
in (let _52_3264 = (let _70_23675 = (Support.List.filter (fun ( _52_32 ) -> (match (_52_32) with
| Microsoft_FStar_Tc_Env.Binding_sig (_52_3258) -> begin
false
end
| _52_3261 -> begin
true
end)) bindings)
in (encode_env_bindings env _70_23675))
in (match (_52_3264) with
| (env_decls, env) -> begin
(let _52_3265 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_23676 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" _70_23676))
end
| false -> begin
()
end)
in (let _52_3270 = (encode_formula_with_labels q env)
in (match (_52_3270) with
| (phi, labels, qdecls) -> begin
(let _52_3273 = (encode_labels labels)
in (match (_52_3273) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Support.List.append (Support.List.append env_decls label_prefix) qdecls)
in (let qry = (let _70_23678 = (let _70_23677 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_70_23677, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23678))
in (let suffix = (Support.List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_52_3281) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume (({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.False, _52_3288)); Microsoft_FStar_ToSMT_Term.hash = _52_3285; Microsoft_FStar_ToSMT_Term.freevars = _52_3283}, _52_3293)) -> begin
(let _52_3296 = (pop ())
in ())
end
| _52_3299 when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
(let _52_3300 = (pop ())
in ())
end
| Microsoft_FStar_ToSMT_Term.Assume ((q, _52_3304)) -> begin
(let fresh = ((Support.String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _52_3308 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun ( p ) ( _52_3314 ) -> (match (_52_3314) with
| (n, i) -> begin
(let _70_23700 = (let _70_23699 = (let _70_23684 = (let _70_23683 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" _70_23683))
in Microsoft_FStar_ToSMT_Term.Caption (_70_23684))
in (let _70_23698 = (let _70_23697 = (let _70_23689 = (let _70_23688 = (let _70_23687 = (let _70_23686 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _70_23685 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_70_23686, _70_23685)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23687))
in (_70_23688, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23689))
in (let _70_23696 = (let _70_23695 = (let _70_23694 = (let _70_23693 = (let _70_23692 = (let _70_23691 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _70_23690 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_70_23691, _70_23690)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_23692))
in (_70_23693, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_23694))
in (_70_23695)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_70_23697)::_70_23696))
in (_70_23699)::_70_23698))
in (Support.List.append _70_23700 suffix))
end))
in (let check = (fun ( p ) -> (let initial_config = (let _70_23704 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _70_23703 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_70_23704, _70_23703)))
in (let alt_configs = (let _70_23723 = (let _70_23722 = (match (((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel))) with
| true -> begin
(let _70_23707 = (let _70_23706 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _70_23705 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_23706, _70_23705)))
in (_70_23707)::[])
end
| false -> begin
[]
end)
in (let _70_23721 = (let _70_23720 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2) > (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _70_23710 = (let _70_23709 = ((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2)
in (let _70_23708 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_23709, _70_23708)))
in (_70_23710)::[])
end
| false -> begin
[]
end)
in (let _70_23719 = (let _70_23718 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) > (Support.ST.read Microsoft_FStar_Options.initial_fuel)) && ((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel)))) with
| true -> begin
(let _70_23713 = (let _70_23712 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _70_23711 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_23712, _70_23711)))
in (_70_23713)::[])
end
| false -> begin
[]
end)
in (let _70_23717 = (let _70_23716 = (match (((Support.ST.read Microsoft_FStar_Options.min_fuel) < (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _70_23715 = (let _70_23714 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (_70_23714, 1))
in (_70_23715)::[])
end
| false -> begin
[]
end)
in (_70_23716)::[])
in (_70_23718)::_70_23717))
in (_70_23720)::_70_23719))
in (_70_23722)::_70_23721))
in (Support.List.flatten _70_23723))
in (let report = (fun ( _52_3322 ) -> (match (_52_3322) with
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
| _52_3325 -> begin
errs
end)
in (Microsoft_FStar_Tc_Errors.add_errors tcenv errs))
end)
end))
in (let rec try_alt_configs = (fun ( p ) ( errs ) ( _52_33 ) -> (match (_52_33) with
| [] -> begin
(report (false, errs))
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _70_23735 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_23735 (cb p [])))
end
| _52_3337 -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(let _70_23737 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_23737 (fun ( _52_3343 ) -> (match (_52_3343) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb p tl (ok, errs'))
end
| _52_3346 -> begin
(cb p tl (ok, errs))
end)
end))))
end))
and cb = (fun ( p ) ( alt ) ( _52_3351 ) -> (match (_52_3351) with
| (ok, errs) -> begin
(match (ok) with
| true -> begin
()
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _70_23741 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_23741 (cb p alt_configs))))))))
in (let process_query = (fun ( q ) -> (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let _52_3356 = (let _70_23747 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _70_23747 q))
in (match (_52_3356) with
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
in (let _52_3357 = (match ((Support.ST.read Microsoft_FStar_Options.admit_smt_queries)) with
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
in (let _52_3362 = (push "query")
in (let _52_3369 = (encode_formula_with_labels q env)
in (match (_52_3369) with
| (f, _52_3366, _52_3368) -> begin
(let _52_3370 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _52_3374)) -> begin
true
end
| _52_3378 -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = commit_mark; Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun ( _52_3379 ) -> ()); Microsoft_FStar_Tc_Env.push = (fun ( _52_3381 ) -> ()); Microsoft_FStar_Tc_Env.pop = (fun ( _52_3383 ) -> ()); Microsoft_FStar_Tc_Env.mark = (fun ( _52_3385 ) -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun ( _52_3387 ) -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun ( _52_3389 ) -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun ( _52_3391 ) ( _52_3393 ) -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun ( _52_3395 ) ( _52_3397 ) -> ()); Microsoft_FStar_Tc_Env.solve = (fun ( _52_3399 ) ( _52_3401 ) -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun ( _52_3403 ) ( _52_3405 ) -> false); Microsoft_FStar_Tc_Env.finish = (fun ( _52_3407 ) -> ()); Microsoft_FStar_Tc_Env.refresh = (fun ( _52_3408 ) -> ())}






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

let mk_typ_projector_name = (fun ( lid ) ( a ) -> (let _70_23910 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _70_23910)))

let mk_term_projector_name = (fun ( lid ) ( a ) -> (let a = (let _70_23915 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _70_23915; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _70_23916 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _70_23916))))

let primitive_projector_by_pos = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _52_62 ) -> (match (()) with
| () -> begin
(let _70_23926 = (let _70_23925 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" _70_23925 lid.Microsoft_FStar_Absyn_Syntax.str))
in (Support.All.failwith _70_23926))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _70_23927 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_23927.Microsoft_FStar_Absyn_Syntax.n)) with
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

let mk_term_projector_name_by_pos = (fun ( lid ) ( i ) -> (let _70_23933 = (let _70_23932 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _70_23932))
in (Support.All.pipe_left escape _70_23933)))

let mk_typ_projector = (fun ( lid ) ( a ) -> (let _70_23939 = (let _70_23938 = (mk_typ_projector_name lid a)
in (_70_23938, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_23939)))

let mk_term_projector = (fun ( lid ) ( a ) -> (let _70_23945 = (let _70_23944 = (mk_term_projector_name lid a)
in (_70_23944, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_23945)))

let mk_term_projector_by_pos = (fun ( lid ) ( i ) -> (let _70_23951 = (let _70_23950 = (mk_term_projector_name_by_pos lid i)
in (_70_23950, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_23951)))

let mk_data_tester = (fun ( env ) ( l ) ( x ) -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let is_Mkvarops_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun ( _52_101 ) -> (match (()) with
| () -> begin
(let _70_24055 = (Support.Microsoft.FStar.Util.smap_create 100)
in (let _70_24054 = (Support.Microsoft.FStar.Util.smap_create 100)
in (_70_24055, _70_24054)))
end))
in (let scopes = (let _70_24057 = (let _70_24056 = (new_scope ())
in (_70_24056)::[])
in (Support.Microsoft.FStar.Util.mk_ref _70_24057))
in (let mk_unique = (fun ( y ) -> (let y = (escape y)
in (let y = (match ((let _70_24061 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _70_24061 (fun ( _52_109 ) -> (match (_52_109) with
| (names, _52_108) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_52_112) -> begin
(let _52_114 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _70_24063 = (let _70_24062 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _70_24062))
in (Support.String.strcat (Support.String.strcat y "__") _70_24063)))
end)
in (let top_scope = (let _70_24065 = (let _70_24064 = (Support.ST.read scopes)
in (Support.List.hd _70_24064))
in (Support.All.pipe_left Support.Prims.fst _70_24065))
in (let _52_118 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun ( pp ) ( rn ) -> (let _70_24071 = (let _70_24070 = (Support.All.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.String.strcat _70_24070 "__"))
in (Support.String.strcat _70_24071 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun ( lid ) -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun ( _52_126 ) -> (match (()) with
| () -> begin
(let _52_127 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
end))
in (let fresh = (fun ( pfx ) -> (let _70_24079 = (let _70_24078 = (next_id ())
in (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int _70_24078))
in (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx _70_24079)))
in (let string_const = (fun ( s ) -> (match ((let _70_24083 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _70_24083 (fun ( _52_136 ) -> (match (_52_136) with
| (_52_134, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _70_24084 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxString _70_24084))
in (let top_scope = (let _70_24086 = (let _70_24085 = (Support.ST.read scopes)
in (Support.List.hd _70_24085))
in (Support.All.pipe_left Support.Prims.snd _70_24086))
in (let _52_143 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun ( _52_146 ) -> (match (()) with
| () -> begin
(let _70_24091 = (let _70_24090 = (new_scope ())
in (let _70_24089 = (Support.ST.read scopes)
in (_70_24090)::_70_24089))
in (Support.ST.op_Colon_Equals scopes _70_24091))
end))
in (let pop = (fun ( _52_148 ) -> (match (()) with
| () -> begin
(let _70_24095 = (let _70_24094 = (Support.ST.read scopes)
in (Support.List.tl _70_24094))
in (Support.ST.op_Colon_Equals scopes _70_24095))
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

let unmangle = (fun ( x ) -> (let _70_24111 = (let _70_24110 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _70_24109 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_70_24110, _70_24109)))
in (Microsoft_FStar_Absyn_Util.mkbvd _70_24111)))

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

let print_env = (fun ( e ) -> (let _70_24197 = (Support.All.pipe_right e.bindings (Support.List.map (fun ( _52_2 ) -> (match (_52_2) with
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
in (Support.All.pipe_right _70_24197 (Support.String.concat ", "))))

let lookup_binding = (fun ( env ) ( f ) -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun ( env ) ( t ) -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_24207 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_70_24207))
end
| false -> begin
None
end))

let fresh_fvar = (fun ( x ) ( s ) -> (let xsym = (varops.fresh x)
in (let _70_24212 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _70_24212))))

let gen_term_var = (fun ( env ) ( x ) -> (let ysym = (let _70_24217 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@x" _70_24217))
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
(let _70_24232 = (let _70_24231 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" _70_24231))
in (Support.All.failwith _70_24232))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun ( env ) ( x ) -> (let ysym = (let _70_24237 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@a" _70_24237))
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
(let _70_24252 = (let _70_24251 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" _70_24251))
in (Support.All.failwith _70_24252))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _70_24263 = (let _52_295 = env
in (let _70_24262 = (let _70_24261 = (let _70_24260 = (let _70_24259 = (let _70_24258 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _70_24257 ) -> Some (_70_24257)) _70_24258))
in (x, fname, _70_24259, None))
in Binding_fvar (_70_24260))
in (_70_24261)::env.bindings)
in {bindings = _70_24262; depth = _52_295.depth; tcenv = _52_295.tcenv; warn = _52_295.warn; cache = _52_295.cache; nolabels = _52_295.nolabels; use_zfuel_name = _52_295.use_zfuel_name; encode_non_total_function_typ = _52_295.encode_non_total_function_typ}))
in (fname, ftok, _70_24263)))))

let try_lookup_lid = (fun ( env ) ( a ) -> (lookup_binding env (fun ( _52_5 ) -> (match (_52_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _52_307 -> begin
None
end))))

let lookup_lid = (fun ( env ) ( a ) -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _70_24274 = (let _70_24273 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _70_24273))
in (Support.All.failwith _70_24274))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _52_317.depth; tcenv = _52_317.tcenv; warn = _52_317.warn; cache = _52_317.cache; nolabels = _52_317.nolabels; use_zfuel_name = _52_317.use_zfuel_name; encode_non_total_function_typ = _52_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun ( env ) ( x ) ( f ) -> (let _52_326 = (lookup_lid env x)
in (match (_52_326) with
| (t1, t2, _52_325) -> begin
(let t3 = (let _70_24291 = (let _70_24290 = (let _70_24289 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_70_24289)::[])
in (f, _70_24290))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24291))
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
(match ((let _70_24295 = (let _70_24294 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (Support.All.pipe_right _70_24294 Support.Prims.fst))
in (Support.Microsoft.FStar.Util.starts_with _70_24295 "fuel"))) with
| true -> begin
(let _70_24296 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _70_24296 fuel))
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
(let _70_24298 = (let _70_24297 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _70_24297))
in (Support.All.failwith _70_24298))
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
in (let _70_24313 = (let _52_392 = env
in (let _70_24312 = (let _70_24311 = (let _70_24310 = (let _70_24309 = (let _70_24308 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _70_24307 ) -> Some (_70_24307)) _70_24308))
in (x, fname, _70_24309))
in Binding_ftvar (_70_24310))
in (_70_24311)::env.bindings)
in {bindings = _70_24312; depth = _52_392.depth; tcenv = _52_392.tcenv; warn = _52_392.warn; cache = _52_392.cache; nolabels = _52_392.nolabels; use_zfuel_name = _52_392.use_zfuel_name; encode_non_total_function_typ = _52_392.encode_non_total_function_typ}))
in (fname, ftok, _70_24313)))))

let lookup_tlid = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_6 ) -> (match (_52_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _52_403 -> begin
None
end)))) with
| None -> begin
(let _70_24320 = (let _70_24319 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _70_24319))
in (Support.All.failwith _70_24320))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _52_411.depth; tcenv = _52_411.tcenv; warn = _52_411.warn; cache = _52_411.cache; nolabels = _52_411.nolabels; use_zfuel_name = _52_411.use_zfuel_name; encode_non_total_function_typ = _52_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun ( env ) ( a ) -> (match ((let _70_24331 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_24331 Support.Prims.snd))) with
| None -> begin
(let _70_24333 = (let _70_24332 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _70_24332))
in (Support.All.failwith _70_24333))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun ( env ) ( a ) -> (let _70_24336 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_24336 Support.Prims.fst)))

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
(let _70_24352 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_24352 Support.Option.isNone))
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

let trivial_post = (fun ( t ) -> (let _70_24374 = (let _70_24373 = (let _70_24371 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_24371)::[])
in (let _70_24372 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_70_24373, _70_24372)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_24374 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun ( e ) ( vars ) -> (Support.All.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _70_24381 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _70_24381))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _70_24382 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _70_24382))
end
| _52_509 -> begin
(let _70_24383 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _70_24383))
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
(let _70_24396 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _70_24396))
end
| _52_524 -> begin
(let _70_24397 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _70_24397))
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
(let _70_24453 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _70_24453))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _70_24454 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _70_24454))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _70_24455 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _70_24455))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _70_24459 = (let _70_24458 = (let _70_24457 = (let _70_24456 = (Microsoft_FStar_ToSMT_Term.mkInteger' i)
in (Microsoft_FStar_ToSMT_Term.boxInt _70_24456))
in (_70_24457)::[])
in ("Int32.Int32", _70_24458))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24459))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _52_609)) -> begin
(let _70_24460 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_bytes bytes)
in (varops.string_const _70_24460))
end
| c -> begin
(let _70_24462 = (let _70_24461 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" _70_24461))
in (Support.All.failwith _70_24462))
end))

let as_function_typ = (fun ( env ) ( t0 ) -> (let rec aux = (fun ( norm ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_52_620) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_623) -> begin
(let _70_24471 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _70_24471))
end
| _52_626 -> begin
(match (norm) with
| true -> begin
(let _70_24472 = (whnf env t)
in (aux false _70_24472))
end
| false -> begin
(let _70_24475 = (let _70_24474 = (Support.Microsoft.FStar.Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_24473 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Support.Microsoft.FStar.Util.format2 "(%s) Expected a function typ; got %s" _70_24474 _70_24473)))
in (Support.All.failwith _70_24475))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun ( k ) ( env ) -> (match ((let _70_24507 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _70_24507.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_52_631, k0)) -> begin
(let _52_635 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _70_24509 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _70_24508 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _70_24509 _70_24508)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _52_639)) -> begin
(let _70_24511 = (let _70_24510 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _70_24510))
in (_70_24511, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, kbody)) -> begin
(let tsym = (let _70_24512 = (varops.fresh "t")
in (_70_24512, Microsoft_FStar_ToSMT_Term.Type_sort))
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
(let _70_24521 = (let _70_24520 = (let _70_24519 = (Microsoft_FStar_ToSMT_Term.mk_PreKind app)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_24519))
in (_70_24520, body))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_24521))
end)
in (let _70_24523 = (let _70_24522 = (Microsoft_FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _70_24522))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24523)))))
end
| _52_680 -> begin
(Support.All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _70_24525 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (Support.All.pipe_right _70_24525 (Support.List.filter (fun ( _52_685 ) -> (match (_52_685) with
| (x, _52_684) -> begin
(x <> (Support.Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((k', sorts, _52_691)) -> begin
(let _70_24528 = (let _70_24527 = (let _70_24526 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _70_24526))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24527))
in (_70_24528, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_24529 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_70_24529))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _70_24531 = (let _70_24530 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _70_24530))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24531))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _70_24540 = (let _70_24539 = (let _70_24538 = (let _70_24537 = (let _70_24536 = (let _70_24535 = (let _70_24534 = (let _70_24533 = (let _70_24532 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_24532))
in (_70_24533, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_24534))
in (t_has_k, _70_24535))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_24536))
in ((t_has_k)::[], (tsym)::cvars, _70_24537))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24538))
in (_70_24539, Some ((Support.String.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24540))
in (let k_decls = (Support.List.append (Support.List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _52_703 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _52_706 -> begin
(let _70_24542 = (let _70_24541 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" _70_24541))
in (Support.All.failwith _70_24542))
end))
and encode_knd = (fun ( k ) ( env ) ( t ) -> (let _52_712 = (encode_knd_term k env)
in (match (_52_712) with
| (k, decls) -> begin
(let _70_24546 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_70_24546, decls))
end)))
and encode_binders = (fun ( fuel_opt ) ( bs ) ( env ) -> (let _52_716 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_24550 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" _70_24550))
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
(let _70_24554 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _70_24553 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _70_24554 aasym _70_24553)))
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
(let _52_754 = (let _70_24555 = (norm_t env t)
in (encode_typ_pred' fuel_opt _70_24555 env xx))
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
(let _70_24560 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_70_24560, decls))
end))))
and encode_typ_term = (fun ( t ) ( env ) -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _70_24563 = (lookup_typ_var env a)
in (_70_24563, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _70_24564 = (lookup_free_tvar env fv)
in (_70_24564, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
(match (((env.encode_non_total_function_typ && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _52_792 = (encode_binders None binders env)
in (match (_52_792) with
| (vars, guards, env', decls, _52_791) -> begin
(let fsym = (let _70_24565 = (varops.fresh "f")
in (_70_24565, Microsoft_FStar_ToSMT_Term.Term_sort))
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
(let _70_24566 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_24566, decls))
end
| Some (pre) -> begin
(let _52_807 = (encode_formula pre env')
in (match (_52_807) with
| (guard, decls0) -> begin
(let _70_24567 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_70_24567, (Support.List.append decls decls0)))
end))
end)
in (match (_52_810) with
| (guards, guard_decls) -> begin
(let t_interp = (let _70_24569 = (let _70_24568 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _70_24568))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24569))
in (let cvars = (let _70_24571 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (Support.All.pipe_right _70_24571 (Support.List.filter (fun ( _52_815 ) -> (match (_52_815) with
| (x, _52_814) -> begin
(x <> (Support.Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _52_821)) -> begin
(let _70_24574 = (let _70_24573 = (let _70_24572 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _70_24572))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24573))
in (_70_24574, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_24575 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_70_24575))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _70_24577 = (let _70_24576 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_24576))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24577))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _70_24579 = (let _70_24578 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_70_24578, Some ((Support.String.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24579))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let pre_typing = (let _70_24586 = (let _70_24585 = (let _70_24584 = (let _70_24583 = (let _70_24582 = (let _70_24581 = (let _70_24580 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _70_24580))
in (f_has_t, _70_24581))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24582))
in ((f_has_t)::[], (fsym)::cvars, _70_24583))
in (mkForall_fuel _70_24584))
in (_70_24585, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24586))
in (let t_interp = (let _70_24590 = (let _70_24589 = (let _70_24588 = (let _70_24587 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t, t_interp))
in ((f_has_t)::[], (fsym)::cvars, _70_24587))
in (mkForall_fuel _70_24588))
in (_70_24589, Some ((Support.String.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24590))
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
in (let t_kinding = (let _70_24592 = (let _70_24591 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_70_24591, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24592))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _70_24599 = (let _70_24598 = (let _70_24597 = (let _70_24596 = (let _70_24595 = (let _70_24594 = (let _70_24593 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _70_24593))
in (f_has_t, _70_24594))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24595))
in ((f_has_t)::[], (fsym)::[], _70_24596))
in (mkForall_fuel _70_24597))
in (_70_24598, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24599))
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
(let encoding = (let _70_24601 = (let _70_24600 = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t)
in (_70_24600, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_24601))
in (let cvars = (let _70_24603 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (Support.All.pipe_right _70_24603 (Support.List.filter (fun ( _52_881 ) -> (match (_52_881) with
| (y, _52_880) -> begin
(y <> x)
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_887, _52_889)) -> begin
(let _70_24606 = (let _70_24605 = (let _70_24604 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _70_24604))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24605))
in (_70_24606, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _70_24608 = (let _70_24607 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_24607))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24608))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _70_24610 = (let _70_24609 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (xfv)::cvars, _70_24609))
in (mkForall_fuel _70_24610))
in (let t_decls = (let _70_24617 = (let _70_24616 = (let _70_24615 = (let _70_24614 = (let _70_24613 = (let _70_24612 = (let _70_24611 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_70_24611))
in (assumption, _70_24612))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24613))
in (_70_24614)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_70_24615)
in (tdecl)::_70_24616)
in (Support.List.append (Support.List.append decls decls') _70_24617))
in (let _52_902 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _70_24618 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _70_24618))
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
in (let t = (let _70_24623 = (let _70_24622 = (Support.List.map (fun ( _52_10 ) -> (match (_52_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (head, _70_24622))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24623))
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
(let ttm = (let _70_24624 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _70_24624))
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
(let key_body = (let _70_24628 = (let _70_24627 = (let _70_24626 = (let _70_24625 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_24625, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24626))
in ([], vars, _70_24627))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24628))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_976, _52_978)) -> begin
(let _70_24631 = (let _70_24630 = (let _70_24629 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _70_24629))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24630))
in (_70_24631, []))
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
in (let t = (let _70_24633 = (let _70_24632 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_24632))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24633))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _70_24640 = (let _70_24639 = (let _70_24638 = (let _70_24637 = (let _70_24636 = (let _70_24635 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_24634 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_24635, _70_24634)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24636))
in ((app)::[], (Support.List.append vars cvars), _70_24637))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24638))
in (_70_24639, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24640))
in (let kinding = (let _52_993 = (let _70_24641 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _70_24641 env t))
in (match (_52_993) with
| (ktm, decls'') -> begin
(let _70_24645 = (let _70_24644 = (let _70_24643 = (let _70_24642 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_70_24642, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24643))
in (_70_24644)::[])
in (Support.List.append decls'' _70_24645))
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
(let _70_24646 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _70_24646 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _70_24651 = (let _70_24650 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_24649 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _70_24648 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _70_24647 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _70_24650 _70_24649 _70_24648 _70_24647)))))
in (Support.All.failwith _70_24651))
end)))
and encode_exp = (fun ( e ) ( env ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_52_1015) -> begin
(let _70_24654 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _70_24654 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _52_1022)) -> begin
(let _70_24655 = (lookup_free_var env v)
in (_70_24655, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _70_24656 = (encode_const c)
in (_70_24656, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _52_1030)) -> begin
(let _52_1033 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _52_1037))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _52_1043)) -> begin
(let e = (let _70_24657 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _70_24657))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun ( _52_1052 ) -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _70_24660 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_70_24660, (decl)::[]))))
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _52_1056 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _70_24661 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (Support.All.pipe_left Support.Prims.op_Negation _70_24661))) with
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
in (let e = (let _70_24663 = (let _70_24662 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _70_24662))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_24663 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
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
(let key_body = (let _70_24667 = (let _70_24666 = (let _70_24665 = (let _70_24664 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_24664, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24665))
in ([], vars, _70_24666))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24667))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_1090, _52_1092)) -> begin
(let _70_24670 = (let _70_24669 = (let _70_24668 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _70_24668))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24669))
in (_70_24670, []))
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
in (let f = (let _70_24672 = (let _70_24671 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _70_24671))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24672))
in (let app = (mk_ApplyE f vars)
in (let _52_1106 = (encode_typ_pred' None tfun env f)
in (match (_52_1106) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _70_24674 = (let _70_24673 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_70_24673, Some ((Support.String.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24674))
in (let interp_f = (let _70_24681 = (let _70_24680 = (let _70_24679 = (let _70_24678 = (let _70_24677 = (let _70_24676 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _70_24675 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_24676, _70_24675)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24677))
in ((app)::[], (Support.List.append vars cvars), _70_24678))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24679))
in (_70_24680, Some ((Support.String.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24681))
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
(let _70_24682 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_70_24682, (Support.List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_52_1162); Microsoft_FStar_Absyn_Syntax.tk = _52_1160; Microsoft_FStar_Absyn_Syntax.pos = _52_1158; Microsoft_FStar_Absyn_Syntax.fvs = _52_1156; Microsoft_FStar_Absyn_Syntax.uvs = _52_1154}, _52_1166)) -> begin
(let _70_24683 = (whnf_e env e)
in (encode_exp _70_24683 env))
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
in (let ty = (let _70_24686 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _70_24686 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _52_1194 = (encode_typ_pred' None ty env app_tm)
in (match (_52_1194) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _70_24688 = (let _70_24687 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_70_24687, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24688))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun ( fv ) -> (let _52_1201 = (lookup_free_var_sym env fv)
in (match (_52_1201) with
| (fname, fuel_args) -> begin
(let tm = (let _70_24694 = (let _70_24693 = (let _70_24692 = (Support.List.map (fun ( _52_11 ) -> (match (_52_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (Support.List.append fuel_args _70_24692))
in (fname, _70_24693))
in (Microsoft_FStar_ToSMT_Term.mkApp' _70_24694))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _52_1208 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _70_24696 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _70_24695 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _70_24696 _70_24695)))
end
| false -> begin
()
end)
in (let head_type = (let _70_24699 = (let _70_24698 = (let _70_24697 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _70_24697))
in (whnf env _70_24698))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.unrefine _70_24699))
in (let _52_1211 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _70_24702 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _70_24701 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _70_24700 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _70_24702 _70_24701 _70_24700))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _70_24706 = (let _70_24705 = (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_24704 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _70_24703 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" _70_24705 _70_24704 _70_24703))))
in (Support.All.failwith _70_24706))
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
in (let _70_24707 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_70_24707, (decl_e)::[])))))
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
(let _70_24718 = (let _70_24717 = (let _70_24716 = (let _70_24715 = (let _70_24714 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _70_24714))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_24715))
in (guard, _70_24716))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_24717))
in (_70_24718, decls2))
end))
end)
in (match (_52_1309) with
| (guard, decls2) -> begin
(let _52_1312 = (encode_exp br env)
in (match (_52_1312) with
| (br, decls3) -> begin
(let _70_24719 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_70_24719, (Support.List.append (Support.List.append decls decls2) decls3)))
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
(let _70_24722 = (let _70_24721 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_24720 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" _70_24721 _70_24720)))
in (Support.All.failwith _70_24722))
end))))
and encode_pat = (fun ( env ) ( pat ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _52_1324 -> begin
(let _70_24725 = (encode_one_pat env pat)
in (_70_24725)::[])
end))
and encode_one_pat = (fun ( env ) ( pat ) -> (let _52_1327 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_24728 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" _70_24728))
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
(let _70_24736 = (let _70_24735 = (encode_const c)
in (scrutinee, _70_24735))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_24736))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _52_1381, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( _52_1390 ) -> (match (_52_1390) with
| (arg, _52_1389) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _70_24739 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _70_24739)))
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
(let _70_24747 = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( _52_1426 ) -> (match (_52_1426) with
| (arg, _52_1425) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _70_24746 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _70_24746)))
end))))
in (Support.All.pipe_right _70_24747 Support.List.flatten))
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
and encode_function_type_as_formula = (fun ( induction_on ) ( t ) ( env ) -> (let v_or_t_pat = (fun ( p ) -> (match ((let _70_24761 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _70_24761.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1475, (Support.Microsoft.FStar.Util.Inl (_52_1482), _52_1485)::(Support.Microsoft.FStar.Util.Inr (e), _52_1479)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1491, (Support.Microsoft.FStar.Util.Inl (t), _52_1495)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _52_1501 -> begin
(Support.All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun ( p ) -> (match ((let _70_24764 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _70_24764.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1505, _52_1517::(Support.Microsoft.FStar.Util.Inr (hd), _52_1514)::(Support.Microsoft.FStar.Util.Inr (tl), _52_1509)::[])) -> begin
(let _70_24766 = (v_or_t_pat hd)
in (let _70_24765 = (lemma_pats tl)
in (_70_24766)::_70_24765))
end
| _52_1522 -> begin
[]
end))
in (let _52_1561 = (match ((let _70_24767 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_24767.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _52_1531; Microsoft_FStar_Absyn_Syntax.pos = _52_1529; Microsoft_FStar_Absyn_Syntax.fvs = _52_1527; Microsoft_FStar_Absyn_Syntax.uvs = _52_1525})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _52_1550)::(Support.Microsoft.FStar.Util.Inl (post), _52_1545)::(Support.Microsoft.FStar.Util.Inr (pats), _52_1540)::[] -> begin
(let _70_24768 = (lemma_pats pats)
in (binders, pre, post, _70_24768))
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
(let _52_1584 = (let _70_24770 = (Support.All.pipe_right patterns (Support.List.map (fun ( _52_12 ) -> (match (_52_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1573) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1578) -> begin
(encode_exp e (let _52_1580 = env
in {bindings = _52_1580.bindings; depth = _52_1580.depth; tcenv = _52_1580.tcenv; warn = _52_1580.warn; cache = _52_1580.cache; nolabels = _52_1580.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1580.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _70_24770 Support.List.unzip))
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
(let _70_24772 = (let _70_24771 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _70_24771 e))
in (_70_24772)::pats)
end
| _52_1592 -> begin
(let rec aux = (fun ( tl ) ( vars ) -> (match (vars) with
| [] -> begin
(let _70_24777 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_70_24777)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _70_24779 = (let _70_24778 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _70_24778 tl))
in (aux _70_24779 vars))
end
| _52_1603 -> begin
pats
end))
in (let _70_24780 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _70_24780 vars)))
end)
end)
in (let env = (let _52_1605 = env
in {bindings = _52_1605.bindings; depth = _52_1605.depth; tcenv = _52_1605.tcenv; warn = _52_1605.warn; cache = _52_1605.cache; nolabels = true; use_zfuel_name = _52_1605.use_zfuel_name; encode_non_total_function_typ = _52_1605.encode_non_total_function_typ})
in (let _52_1610 = (let _70_24781 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _70_24781 env))
in (match (_52_1610) with
| (pre, decls'') -> begin
(let _52_1613 = (let _70_24782 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _70_24782 env))
in (match (_52_1613) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in (let _70_24787 = (let _70_24786 = (let _70_24785 = (let _70_24784 = (let _70_24783 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_70_24783, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24784))
in (pats, vars, _70_24785))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24786))
in (_70_24787, decls)))
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
(let _70_24805 = (f args)
in (_70_24805, [], decls))
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
(let _70_24821 = (f phis)
in (_70_24821, labs, decls))
end))))
in (let const_op = (fun ( f ) ( _52_1657 ) -> (f, [], []))
in (let un_op = (fun ( f ) ( l ) -> (let _70_24835 = (Support.List.hd l)
in (Support.All.pipe_left f _70_24835)))
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
(let _70_24849 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_70_24849, (Support.List.append labs1 labs2), (Support.List.append decls1 decls2)))
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
in (let unboxInt_l = (fun ( f ) ( l ) -> (let _70_24861 = (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _70_24861)))
in (let connectives = (let _70_24922 = (let _70_24870 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _70_24870))
in (let _70_24921 = (let _70_24920 = (let _70_24876 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _70_24876))
in (let _70_24919 = (let _70_24918 = (let _70_24917 = (let _70_24885 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _70_24885))
in (let _70_24916 = (let _70_24915 = (let _70_24914 = (let _70_24894 = (Support.All.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _70_24894))
in (let _70_24913 = (let _70_24912 = (let _70_24900 = (Support.All.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _70_24900))
in (_70_24912)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_70_24914)::_70_24913))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_70_24915)
in (_70_24917)::_70_24916))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_70_24918)
in (_70_24920)::_70_24919))
in (_70_24922)::_70_24921))
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
(let lvar = (let _70_24925 = (varops.fresh "label")
in (_70_24925, Microsoft_FStar_ToSMT_Term.Bool_sort))
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
(let _70_24926 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_70_24926, [], decls))
end))
end))
in (let encode_q_body = (fun ( env ) ( bs ) ( ps ) ( body ) -> (let _52_1811 = (encode_binders None bs env)
in (match (_52_1811) with
| (vars, guards, env, decls, _52_1810) -> begin
(let _52_1827 = (let _70_24936 = (Support.All.pipe_right ps (Support.List.map (fun ( _52_17 ) -> (match (_52_17) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1816) -> begin
(encode_typ_term t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1821) -> begin
(encode_exp e (let _52_1823 = env
in {bindings = _52_1823.bindings; depth = _52_1823.depth; tcenv = _52_1823.tcenv; warn = _52_1823.warn; cache = _52_1823.cache; nolabels = _52_1823.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1823.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _70_24936 Support.List.unzip))
in (match (_52_1827) with
| (pats, decls') -> begin
(let _52_1831 = (encode_formula_with_labels body env)
in (match (_52_1831) with
| (body, labs, decls'') -> begin
(let _70_24937 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _70_24937, body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'')))
end))
end))
end)))
in (let _52_1832 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_24938 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" _70_24938))
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
(let _70_24955 = (Support.All.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" _70_24955))
end
| false -> begin
()
end)
in (let _52_1865 = (encode_q_body env vars pats body)
in (match (_52_1865) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _70_24958 = (let _70_24957 = (let _70_24956 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _70_24956))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24957))
in (_70_24958, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _52_1878 = (encode_q_body env vars pats body)
in (match (_52_1878) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _70_24961 = (let _70_24960 = (let _70_24959 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _70_24959))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_24960))
in (_70_24961, labs, decls))
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
in (let quant = (fun ( vars ) ( body ) -> (fun ( x ) -> (let t1 = (let _70_25004 = (let _70_25003 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _70_25003))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25004))
in (let vname_decl = (let _70_25006 = (let _70_25005 = (Support.All.pipe_right vars (Support.List.map Support.Prims.snd))
in (x, _70_25005, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_25006))
in (let _70_25012 = (let _70_25011 = (let _70_25010 = (let _70_25009 = (let _70_25008 = (let _70_25007 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _70_25007))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25008))
in (_70_25009, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25010))
in (_70_25011)::[])
in (vname_decl)::_70_25012)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _70_25172 = (let _70_25021 = (let _70_25020 = (let _70_25019 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25019))
in (quant axy _70_25020))
in (Microsoft_FStar_Absyn_Const.op_Eq, _70_25021))
in (let _70_25171 = (let _70_25170 = (let _70_25028 = (let _70_25027 = (let _70_25026 = (let _70_25025 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _70_25025))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25026))
in (quant axy _70_25027))
in (Microsoft_FStar_Absyn_Const.op_notEq, _70_25028))
in (let _70_25169 = (let _70_25168 = (let _70_25037 = (let _70_25036 = (let _70_25035 = (let _70_25034 = (let _70_25033 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25032 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25033, _70_25032)))
in (Microsoft_FStar_ToSMT_Term.mkLT _70_25034))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25035))
in (quant xy _70_25036))
in (Microsoft_FStar_Absyn_Const.op_LT, _70_25037))
in (let _70_25167 = (let _70_25166 = (let _70_25046 = (let _70_25045 = (let _70_25044 = (let _70_25043 = (let _70_25042 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25041 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25042, _70_25041)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _70_25043))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25044))
in (quant xy _70_25045))
in (Microsoft_FStar_Absyn_Const.op_LTE, _70_25046))
in (let _70_25165 = (let _70_25164 = (let _70_25055 = (let _70_25054 = (let _70_25053 = (let _70_25052 = (let _70_25051 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25050 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25051, _70_25050)))
in (Microsoft_FStar_ToSMT_Term.mkGT _70_25052))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25053))
in (quant xy _70_25054))
in (Microsoft_FStar_Absyn_Const.op_GT, _70_25055))
in (let _70_25163 = (let _70_25162 = (let _70_25064 = (let _70_25063 = (let _70_25062 = (let _70_25061 = (let _70_25060 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25059 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25060, _70_25059)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _70_25061))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25062))
in (quant xy _70_25063))
in (Microsoft_FStar_Absyn_Const.op_GTE, _70_25064))
in (let _70_25161 = (let _70_25160 = (let _70_25073 = (let _70_25072 = (let _70_25071 = (let _70_25070 = (let _70_25069 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25068 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25069, _70_25068)))
in (Microsoft_FStar_ToSMT_Term.mkSub _70_25070))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25071))
in (quant xy _70_25072))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _70_25073))
in (let _70_25159 = (let _70_25158 = (let _70_25080 = (let _70_25079 = (let _70_25078 = (let _70_25077 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _70_25077))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25078))
in (quant qx _70_25079))
in (Microsoft_FStar_Absyn_Const.op_Minus, _70_25080))
in (let _70_25157 = (let _70_25156 = (let _70_25089 = (let _70_25088 = (let _70_25087 = (let _70_25086 = (let _70_25085 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25084 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25085, _70_25084)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _70_25086))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25087))
in (quant xy _70_25088))
in (Microsoft_FStar_Absyn_Const.op_Addition, _70_25089))
in (let _70_25155 = (let _70_25154 = (let _70_25098 = (let _70_25097 = (let _70_25096 = (let _70_25095 = (let _70_25094 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25093 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25094, _70_25093)))
in (Microsoft_FStar_ToSMT_Term.mkMul _70_25095))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25096))
in (quant xy _70_25097))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _70_25098))
in (let _70_25153 = (let _70_25152 = (let _70_25107 = (let _70_25106 = (let _70_25105 = (let _70_25104 = (let _70_25103 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25102 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25103, _70_25102)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _70_25104))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25105))
in (quant xy _70_25106))
in (Microsoft_FStar_Absyn_Const.op_Division, _70_25107))
in (let _70_25151 = (let _70_25150 = (let _70_25116 = (let _70_25115 = (let _70_25114 = (let _70_25113 = (let _70_25112 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25111 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25112, _70_25111)))
in (Microsoft_FStar_ToSMT_Term.mkMod _70_25113))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25114))
in (quant xy _70_25115))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _70_25116))
in (let _70_25149 = (let _70_25148 = (let _70_25125 = (let _70_25124 = (let _70_25123 = (let _70_25122 = (let _70_25121 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _70_25120 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_70_25121, _70_25120)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_25122))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25123))
in (quant xy _70_25124))
in (Microsoft_FStar_Absyn_Const.op_And, _70_25125))
in (let _70_25147 = (let _70_25146 = (let _70_25134 = (let _70_25133 = (let _70_25132 = (let _70_25131 = (let _70_25130 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _70_25129 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_70_25130, _70_25129)))
in (Microsoft_FStar_ToSMT_Term.mkOr _70_25131))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25132))
in (quant xy _70_25133))
in (Microsoft_FStar_Absyn_Const.op_Or, _70_25134))
in (let _70_25145 = (let _70_25144 = (let _70_25141 = (let _70_25140 = (let _70_25139 = (let _70_25138 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _70_25138))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25139))
in (quant qx _70_25140))
in (Microsoft_FStar_Absyn_Const.op_Negation, _70_25141))
in (_70_25144)::[])
in (_70_25146)::_70_25145))
in (_70_25148)::_70_25147))
in (_70_25150)::_70_25149))
in (_70_25152)::_70_25151))
in (_70_25154)::_70_25153))
in (_70_25156)::_70_25155))
in (_70_25158)::_70_25157))
in (_70_25160)::_70_25159))
in (_70_25162)::_70_25161))
in (_70_25164)::_70_25163))
in (_70_25166)::_70_25165))
in (_70_25168)::_70_25167))
in (_70_25170)::_70_25169))
in (_70_25172)::_70_25171))
in (let mk = (fun ( l ) ( v ) -> (let _70_25204 = (Support.All.pipe_right prims (Support.List.filter (fun ( _52_1910 ) -> (match (_52_1910) with
| (l', _52_1909) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (Support.All.pipe_right _70_25204 (Support.List.collect (fun ( _52_1914 ) -> (match (_52_1914) with
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
in (let _70_25236 = (let _70_25227 = (let _70_25226 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_70_25226, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25227))
in (let _70_25235 = (let _70_25234 = (let _70_25233 = (let _70_25232 = (let _70_25231 = (let _70_25230 = (let _70_25229 = (let _70_25228 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _70_25228))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25229))
in ((typing_pred)::[], (xx)::[], _70_25230))
in (mkForall_fuel _70_25231))
in (_70_25232, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25233))
in (_70_25234)::[])
in (_70_25236)::_70_25235))))
in (let mk_bool = (fun ( _52_1931 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _70_25256 = (let _70_25246 = (let _70_25245 = (let _70_25244 = (let _70_25243 = (let _70_25242 = (let _70_25241 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _70_25241))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25242))
in ((typing_pred)::[], (xx)::[], _70_25243))
in (mkForall_fuel _70_25244))
in (_70_25245, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25246))
in (let _70_25255 = (let _70_25254 = (let _70_25253 = (let _70_25252 = (let _70_25251 = (let _70_25250 = (let _70_25247 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_70_25247)::[])
in (let _70_25249 = (let _70_25248 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_25248 tt))
in (_70_25250, (bb)::[], _70_25249)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25251))
in (_70_25252, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25253))
in (_70_25254)::[])
in (_70_25256)::_70_25255))))))
in (let mk_int = (fun ( _52_1938 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _70_25268 = (let _70_25267 = (let _70_25266 = (let _70_25265 = (let _70_25264 = (let _70_25263 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _70_25262 = (let _70_25261 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_70_25261)::[])
in (_70_25263)::_70_25262))
in (tt)::_70_25264)
in (tt)::_70_25265)
in ("Prims.Precedes", _70_25266))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25267))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _70_25268))
in (let precedes_y_x = (let _70_25269 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _70_25269))
in (let _70_25310 = (let _70_25275 = (let _70_25274 = (let _70_25273 = (let _70_25272 = (let _70_25271 = (let _70_25270 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _70_25270))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25271))
in ((typing_pred)::[], (xx)::[], _70_25272))
in (mkForall_fuel _70_25273))
in (_70_25274, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25275))
in (let _70_25309 = (let _70_25308 = (let _70_25282 = (let _70_25281 = (let _70_25280 = (let _70_25279 = (let _70_25276 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_70_25276)::[])
in (let _70_25278 = (let _70_25277 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_25277 tt))
in (_70_25279, (bb)::[], _70_25278)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25280))
in (_70_25281, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25282))
in (let _70_25307 = (let _70_25306 = (let _70_25305 = (let _70_25304 = (let _70_25303 = (let _70_25302 = (let _70_25301 = (let _70_25300 = (let _70_25299 = (let _70_25298 = (let _70_25297 = (let _70_25296 = (let _70_25285 = (let _70_25284 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25283 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_70_25284, _70_25283)))
in (Microsoft_FStar_ToSMT_Term.mkGT _70_25285))
in (let _70_25295 = (let _70_25294 = (let _70_25288 = (let _70_25287 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _70_25286 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_70_25287, _70_25286)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _70_25288))
in (let _70_25293 = (let _70_25292 = (let _70_25291 = (let _70_25290 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _70_25289 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_70_25290, _70_25289)))
in (Microsoft_FStar_ToSMT_Term.mkLT _70_25291))
in (_70_25292)::[])
in (_70_25294)::_70_25293))
in (_70_25296)::_70_25295))
in (typing_pred_y)::_70_25297)
in (typing_pred)::_70_25298)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _70_25299))
in (_70_25300, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25301))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _70_25302))
in (mkForall_fuel _70_25303))
in (_70_25304, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25305))
in (_70_25306)::[])
in (_70_25308)::_70_25307))
in (_70_25310)::_70_25309)))))))))))
in (let mk_int_alias = (fun ( _52_1950 ) ( tt ) -> (let _70_25319 = (let _70_25318 = (let _70_25317 = (let _70_25316 = (let _70_25315 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _70_25315))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25316))
in (_70_25317, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25318))
in (_70_25319)::[]))
in (let mk_str = (fun ( _52_1954 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _70_25339 = (let _70_25329 = (let _70_25328 = (let _70_25327 = (let _70_25326 = (let _70_25325 = (let _70_25324 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _70_25324))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25325))
in ((typing_pred)::[], (xx)::[], _70_25326))
in (mkForall_fuel _70_25327))
in (_70_25328, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25329))
in (let _70_25338 = (let _70_25337 = (let _70_25336 = (let _70_25335 = (let _70_25334 = (let _70_25333 = (let _70_25330 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_70_25330)::[])
in (let _70_25332 = (let _70_25331 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_25331 tt))
in (_70_25333, (bb)::[], _70_25332)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25334))
in (_70_25335, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25336))
in (_70_25337)::[])
in (_70_25339)::_70_25338))))))
in (let mk_ref = (fun ( reft_name ) ( _52_1962 ) -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _70_25346 = (let _70_25345 = (let _70_25344 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_70_25344)::[])
in (reft_name, _70_25345))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25346))
in (let refb = (let _70_25349 = (let _70_25348 = (let _70_25347 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_70_25347)::[])
in (reft_name, _70_25348))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25349))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _70_25368 = (let _70_25355 = (let _70_25354 = (let _70_25353 = (let _70_25352 = (let _70_25351 = (let _70_25350 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _70_25350))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25351))
in ((typing_pred)::[], (xx)::(aa)::[], _70_25352))
in (mkForall_fuel _70_25353))
in (_70_25354, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25355))
in (let _70_25367 = (let _70_25366 = (let _70_25365 = (let _70_25364 = (let _70_25363 = (let _70_25362 = (let _70_25361 = (let _70_25360 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _70_25359 = (let _70_25358 = (let _70_25357 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _70_25356 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_70_25357, _70_25356)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25358))
in (_70_25360, _70_25359)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25361))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _70_25362))
in (mkForall_fuel' 2 _70_25363))
in (_70_25364, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25365))
in (_70_25366)::[])
in (_70_25368)::_70_25367))))))))))
in (let mk_false_interp = (fun ( _52_1972 ) ( false_tm ) -> (let valid = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _70_25375 = (let _70_25374 = (let _70_25373 = (Microsoft_FStar_ToSMT_Term.mkIff (Microsoft_FStar_ToSMT_Term.mkFalse, valid))
in (_70_25373, Some ("False interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25374))
in (_70_25375)::[])))
in (let mk_and_interp = (fun ( conj ) ( _52_1978 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25382 = (let _70_25381 = (let _70_25380 = (Microsoft_FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_70_25380)::[])
in ("Valid", _70_25381))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25382))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_25389 = (let _70_25388 = (let _70_25387 = (let _70_25386 = (let _70_25385 = (let _70_25384 = (let _70_25383 = (Microsoft_FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_70_25383, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25384))
in ((valid)::[], (aa)::(bb)::[], _70_25385))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25386))
in (_70_25387, Some ("/\\ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25388))
in (_70_25389)::[])))))))))
in (let mk_or_interp = (fun ( disj ) ( _52_1989 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25396 = (let _70_25395 = (let _70_25394 = (Microsoft_FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_70_25394)::[])
in ("Valid", _70_25395))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25396))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_25403 = (let _70_25402 = (let _70_25401 = (let _70_25400 = (let _70_25399 = (let _70_25398 = (let _70_25397 = (Microsoft_FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_70_25397, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25398))
in ((valid)::[], (aa)::(bb)::[], _70_25399))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25400))
in (_70_25401, Some ("\\/ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25402))
in (_70_25403)::[])))))))))
in (let mk_eq2_interp = (fun ( eq2 ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _70_25410 = (let _70_25409 = (let _70_25408 = (Microsoft_FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_70_25408)::[])
in ("Valid", _70_25409))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25410))
in (let _70_25417 = (let _70_25416 = (let _70_25415 = (let _70_25414 = (let _70_25413 = (let _70_25412 = (let _70_25411 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (_70_25411, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25412))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _70_25413))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25414))
in (_70_25415, Some ("Eq2 interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25416))
in (_70_25417)::[])))))))))))
in (let mk_imp_interp = (fun ( imp ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25424 = (let _70_25423 = (let _70_25422 = (Microsoft_FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_70_25422)::[])
in ("Valid", _70_25423))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25424))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_25431 = (let _70_25430 = (let _70_25429 = (let _70_25428 = (let _70_25427 = (let _70_25426 = (let _70_25425 = (Microsoft_FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_70_25425, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25426))
in ((valid)::[], (aa)::(bb)::[], _70_25427))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25428))
in (_70_25429, Some ("==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25430))
in (_70_25431)::[])))))))))
in (let mk_iff_interp = (fun ( iff ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25438 = (let _70_25437 = (let _70_25436 = (Microsoft_FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_70_25436)::[])
in ("Valid", _70_25437))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25438))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_25445 = (let _70_25444 = (let _70_25443 = (let _70_25442 = (let _70_25441 = (let _70_25440 = (let _70_25439 = (Microsoft_FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_70_25439, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25440))
in ((valid)::[], (aa)::(bb)::[], _70_25441))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25442))
in (_70_25443, Some ("<==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25444))
in (_70_25445)::[])))))))))
in (let mk_forall_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _70_25452 = (let _70_25451 = (let _70_25450 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_70_25450)::[])
in ("Valid", _70_25451))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25452))
in (let valid_b_x = (let _70_25455 = (let _70_25454 = (let _70_25453 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_70_25453)::[])
in ("Valid", _70_25454))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25455))
in (let _70_25468 = (let _70_25467 = (let _70_25466 = (let _70_25465 = (let _70_25464 = (let _70_25463 = (let _70_25462 = (let _70_25461 = (let _70_25460 = (let _70_25456 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_25456)::[])
in (let _70_25459 = (let _70_25458 = (let _70_25457 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_25457, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25458))
in (_70_25460, (xx)::[], _70_25459)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25461))
in (_70_25462, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25463))
in ((valid)::[], (aa)::(bb)::[], _70_25464))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25465))
in (_70_25466, Some ("forall interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25467))
in (_70_25468)::[]))))))))))
in (let mk_exists_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _70_25475 = (let _70_25474 = (let _70_25473 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_70_25473)::[])
in ("Valid", _70_25474))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25475))
in (let valid_b_x = (let _70_25478 = (let _70_25477 = (let _70_25476 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_70_25476)::[])
in ("Valid", _70_25477))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25478))
in (let _70_25491 = (let _70_25490 = (let _70_25489 = (let _70_25488 = (let _70_25487 = (let _70_25486 = (let _70_25485 = (let _70_25484 = (let _70_25483 = (let _70_25479 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_25479)::[])
in (let _70_25482 = (let _70_25481 = (let _70_25480 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_25480, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25481))
in (_70_25483, (xx)::[], _70_25482)))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_25484))
in (_70_25485, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25486))
in ((valid)::[], (aa)::(bb)::[], _70_25487))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25488))
in (_70_25489, Some ("exists interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25490))
in (_70_25491)::[]))))))))))
in (let mk_foralltyp_interp = (fun ( for_all ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25498 = (let _70_25497 = (let _70_25496 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_70_25496)::[])
in ("Valid", _70_25497))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25498))
in (let valid_a_b = (let _70_25501 = (let _70_25500 = (let _70_25499 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_70_25499)::[])
in ("Valid", _70_25500))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25501))
in (let _70_25514 = (let _70_25513 = (let _70_25512 = (let _70_25511 = (let _70_25510 = (let _70_25509 = (let _70_25508 = (let _70_25507 = (let _70_25506 = (let _70_25502 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_25502)::[])
in (let _70_25505 = (let _70_25504 = (let _70_25503 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_25503, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25504))
in (_70_25506, (bb)::[], _70_25505)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25507))
in (_70_25508, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25509))
in ((valid)::[], (kk)::(aa)::[], _70_25510))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25511))
in (_70_25512, Some ("ForallTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25513))
in (_70_25514)::[]))))))))))
in (let mk_existstyp_interp = (fun ( for_some ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25521 = (let _70_25520 = (let _70_25519 = (Microsoft_FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_70_25519)::[])
in ("Valid", _70_25520))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25521))
in (let valid_a_b = (let _70_25524 = (let _70_25523 = (let _70_25522 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_70_25522)::[])
in ("Valid", _70_25523))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25524))
in (let _70_25537 = (let _70_25536 = (let _70_25535 = (let _70_25534 = (let _70_25533 = (let _70_25532 = (let _70_25531 = (let _70_25530 = (let _70_25529 = (let _70_25525 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_25525)::[])
in (let _70_25528 = (let _70_25527 = (let _70_25526 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_25526, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25527))
in (_70_25529, (bb)::[], _70_25528)))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_25530))
in (_70_25531, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25532))
in ((valid)::[], (kk)::(aa)::[], _70_25533))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25534))
in (_70_25535, Some ("ExistsTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25536))
in (_70_25537)::[]))))))))))
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
(let _70_25680 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") _70_25680))
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
(let _70_25683 = (let _70_25682 = (let _70_25681 = (Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_25681))
in (_70_25682)::[])
in (_70_25683, e))
end
| _52_2102 -> begin
(let _70_25690 = (let _70_25689 = (let _70_25685 = (let _70_25684 = (Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_25684))
in (_70_25685)::g)
in (let _70_25688 = (let _70_25687 = (let _70_25686 = (Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_25686))
in (_70_25687)::[])
in (Support.List.append _70_25689 _70_25688)))
in (_70_25690, e))
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
in (let valid_b2t_x = (let _70_25695 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _70_25695))
in (let decls = (let _70_25703 = (let _70_25702 = (let _70_25701 = (let _70_25700 = (let _70_25699 = (let _70_25698 = (let _70_25697 = (let _70_25696 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _70_25696))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25697))
in ((valid_b2t_x)::[], (xx)::[], _70_25698))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25699))
in (_70_25700, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25701))
in (_70_25702)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_70_25703)
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
(let tok_app = (let _70_25704 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _70_25704 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _70_25706 = (let _70_25705 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _70_25705))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25706))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _52_2190 -> begin
(let _70_25708 = (let _70_25707 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _70_25707))
in (_70_25708)::[])
end)
in (let decls = (let _70_25719 = (let _70_25712 = (let _70_25711 = (let _70_25710 = (let _70_25709 = (Support.List.map Support.Prims.snd vars)
in (tname, _70_25709, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_25710))
in (_70_25711)::(tok_decl)::[])
in (Support.List.append _70_25712 fresh_tok))
in (let _70_25718 = (let _70_25717 = (let _70_25716 = (let _70_25715 = (let _70_25714 = (let _70_25713 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _70_25713))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25714))
in (_70_25715, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25716))
in (_70_25717)::[])
in (Support.List.append _70_25719 _70_25718)))
in (let t = (whnf env t)
in (let _52_2202 = (match ((Support.All.pipe_right tags (Support.Microsoft.FStar.Util.for_some (fun ( _52_18 ) -> (match (_52_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _52_2197 -> begin
false
end))))) with
| true -> begin
(let _70_25722 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _70_25721 = (encode_formula t env')
in (_70_25722, _70_25721)))
end
| false -> begin
(let _70_25723 = (encode_typ_term t env')
in (app, _70_25723))
end)
in (match (_52_2202) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _70_25730 = (let _70_25729 = (let _70_25728 = (let _70_25727 = (let _70_25726 = (let _70_25725 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_25724 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_70_25725, _70_25724)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25726))
in ((def)::[], vars, _70_25727))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25728))
in (_70_25729, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25730))
in (let kindingAx = (let _52_2206 = (let _70_25731 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _70_25731 env' app))
in (match (_52_2206) with
| (k, decls) -> begin
(let _70_25739 = (let _70_25738 = (let _70_25737 = (let _70_25736 = (let _70_25735 = (let _70_25734 = (let _70_25733 = (let _70_25732 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_25732, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25733))
in ((app)::[], vars, _70_25734))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25735))
in (_70_25736, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25737))
in (_70_25738)::[])
in (Support.List.append decls _70_25739))
end))
in (let g = (let _70_25740 = (primitive_type_axioms lid tname app)
in (Support.List.append (Support.List.append (Support.List.append (Support.List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _70_25740))
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
(let _70_25742 = (let _70_25741 = (encode_smt_lemma env lid t)
in (Support.List.append decls _70_25741))
in (_70_25742, env))
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
(let g = (let _70_25747 = (let _70_25746 = (let _70_25745 = (let _70_25744 = (let _70_25743 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "Assumption: %s" _70_25743))
in Some (_70_25744))
in (f, _70_25745))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25746))
in (_70_25747)::[])
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
in (let _70_25749 = (let _70_25748 = (primitive_type_axioms t tname tsym)
in (decl)::_70_25748)
in (_70_25749, (push_free_tvar env t tname (Some (tsym))))))))
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
(let _70_25755 = (let _70_25754 = (let _70_25753 = (Support.All.pipe_right args (Support.List.map Support.Prims.snd))
in (name, _70_25753, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_25754))
in (_70_25755)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun ( tapp ) ( vars ) -> (match ((((Support.List.length datas) = 0) || (Support.All.pipe_right datas (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (let _70_25761 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (Support.All.pipe_right _70_25761 Support.Option.isNone))))))) with
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
(let indices = (match ((let _70_25764 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _70_25764.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_52_2312, indices)) -> begin
indices
end
| _52_2317 -> begin
[]
end)
in (let env = (Support.All.pipe_right args (Support.List.fold_left (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_25769 = (let _70_25768 = (let _70_25767 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_70_25767, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25768))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _70_25769))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_25772 = (let _70_25771 = (let _70_25770 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_70_25770, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25771))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _70_25772))
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
in (let eqs = (let _70_25779 = (Support.List.map2 (fun ( v ) ( a ) -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_25776 = (let _70_25775 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_70_25775, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25776))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(let _70_25778 = (let _70_25777 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_70_25777, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25778))
end)) vars indices)
in (Support.All.pipe_right _70_25779 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _70_25784 = (let _70_25783 = (let _70_25782 = (let _70_25781 = (let _70_25780 = (mk_data_tester env l xx)
in (_70_25780, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_25781))
in (out, _70_25782))
in (Microsoft_FStar_ToSMT_Term.mkOr _70_25783))
in (_70_25784, (Support.List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_52_2340) with
| (data_ax, decls) -> begin
(let _52_2343 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2343) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _70_25785 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _70_25785 xx tapp))
in (let _70_25792 = (let _70_25791 = (let _70_25790 = (let _70_25789 = (let _70_25788 = (let _70_25787 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _70_25786 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _70_25787, _70_25786)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25788))
in (_70_25789, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25790))
in (_70_25791)::[])
in (Support.List.append decls _70_25792)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _52_2355 = (match ((let _70_25793 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _70_25793.Microsoft_FStar_Absyn_Syntax.n)) with
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
(let dproj_app = (let _70_25807 = (let _70_25806 = (let _70_25805 = (mk_typ_projector_name d a)
in (let _70_25804 = (let _70_25803 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_70_25803)::[])
in (_70_25805, _70_25804)))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25806))
in (mk_ApplyT _70_25807 suffix))
in (let _70_25812 = (let _70_25811 = (let _70_25810 = (let _70_25809 = (let _70_25808 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _70_25808))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25809))
in (_70_25810, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25811))
in (_70_25812)::[]))
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
in (let _70_25825 = (let _70_25824 = (let _70_25823 = (let _70_25822 = (let _70_25821 = (let _70_25820 = (let _70_25819 = (let _70_25818 = (let _70_25817 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _70_25817))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25818))
in (xx_has_type, _70_25819))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25820))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _70_25821))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25822))
in (_70_25823, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25824))
in (_70_25825)::[]))
end))
end)))
in (let _52_2418 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2418) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _70_25827 = (let _70_25826 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _70_25826))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25827))
in (let _52_2443 = (let tname_decl = (let _70_25831 = (let _70_25830 = (Support.All.pipe_right vars (Support.List.map (fun ( _52_2424 ) -> (match (_52_2424) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))))
in (let _70_25829 = (varops.next_id ())
in (tname, _70_25830, Microsoft_FStar_ToSMT_Term.Type_sort, _70_25829)))
in (constructor_or_logic_type_decl _70_25831))
in (let _52_2440 = (match (vars) with
| [] -> begin
(let _70_25835 = (let _70_25834 = (let _70_25833 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (Support.All.pipe_left (fun ( _70_25832 ) -> Some (_70_25832)) _70_25833))
in (push_free_tvar env t tname _70_25834))
in ([], _70_25835))
end
| _52_2428 -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _70_25836 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _70_25836))
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
in (let name_tok_corr = (let _70_25841 = (let _70_25840 = (let _70_25839 = (let _70_25838 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _70_25838))
in (Microsoft_FStar_ToSMT_Term.mkForall' _70_25839))
in (_70_25840, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25841))
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
(let _70_25845 = (let _70_25844 = (let _70_25843 = (let _70_25842 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_25842))
in (_70_25843, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25844))
in (_70_25845)::[])
end
| false -> begin
[]
end)
in (let _70_25851 = (let _70_25850 = (let _70_25849 = (let _70_25848 = (let _70_25847 = (let _70_25846 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _70_25846))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25847))
in (_70_25848, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25849))
in (_70_25850)::[])
in (Support.List.append (Support.List.append decls karr) _70_25851)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _70_25852 = (projection_axioms tapp vars)
in (Support.List.append kindingAx _70_25852))
end
| false -> begin
(let _70_25859 = (let _70_25857 = (let _70_25855 = (let _70_25853 = (primitive_type_axioms t tname tapp)
in (Support.List.append kindingAx _70_25853))
in (let _70_25854 = (inversion_axioms tapp vars)
in (Support.List.append _70_25855 _70_25854)))
in (let _70_25856 = (projection_axioms tapp vars)
in (Support.List.append _70_25857 _70_25856)))
in (let _70_25858 = (pretype_axioms tapp vars)
in (Support.List.append _70_25859 _70_25858)))
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
(let _70_25861 = (mk_typ_projector_name d a)
in (_70_25861, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_25862 = (mk_term_projector_name d x)
in (_70_25862, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _70_25864 = (let _70_25863 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _70_25863))
in (Support.All.pipe_right _70_25864 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
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
(let _70_25866 = (let _70_25865 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _70_25865))
in (_70_25866)::[])
end)
in (let encode_elim = (fun ( _52_2529 ) -> (match (()) with
| () -> begin
(let _52_2532 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_52_2532) with
| (head, args) -> begin
(match ((let _70_25869 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _70_25869.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _52_2538 = (encode_args args env')
in (match (_52_2538) with
| (encoded_args, arg_decls) -> begin
(let _52_2562 = (Support.List.fold_left (fun ( _52_2542 ) ( arg ) -> (match (_52_2542) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _52_2550 = (let _70_25872 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _70_25872))
in (match (_52_2550) with
| (_52_2547, tv, env) -> begin
(let _70_25874 = (let _70_25873 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_70_25873)::eqns)
in (env, (tv)::arg_vars, _70_25874))
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _52_2557 = (let _70_25875 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _70_25875))
in (match (_52_2557) with
| (_52_2554, xv, env) -> begin
(let _70_25877 = (let _70_25876 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_70_25876)::eqns)
in (env, (xv)::arg_vars, _70_25877))
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
in (let typing_inversion = (let _70_25884 = (let _70_25883 = (let _70_25882 = (let _70_25881 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _70_25880 = (let _70_25879 = (let _70_25878 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards))
in (ty_pred, _70_25878))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25879))
in ((ty_pred)::[], _70_25881, _70_25880)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25882))
in (_70_25883, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25884))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _70_25885 = (varops.fresh "x")
in (_70_25885, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _70_25894 = (let _70_25893 = (let _70_25892 = (let _70_25891 = (let _70_25886 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_70_25886)::[])
in (let _70_25890 = (let _70_25889 = (let _70_25888 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _70_25887 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_70_25888, _70_25887)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25889))
in (_70_25891, (x)::[], _70_25890)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25892))
in (_70_25893, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25894))))
end
| false -> begin
(let prec = (Support.All.pipe_right vars (Support.List.collect (fun ( v ) -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _70_25897 = (let _70_25896 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _70_25896 dapp))
in (_70_25897)::[])
end
| _52_2577 -> begin
(Support.All.failwith "unexpected sort")
end))))
in (let _70_25904 = (let _70_25903 = (let _70_25902 = (let _70_25901 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _70_25900 = (let _70_25899 = (let _70_25898 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _70_25898))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25899))
in ((ty_pred)::[], _70_25901, _70_25900)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25902))
in (_70_25903, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25904)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _52_2581 -> begin
(let _52_2582 = (let _70_25907 = (let _70_25906 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _70_25905 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" _70_25906 _70_25905)))
in (Microsoft_FStar_Tc_Errors.warn drange _70_25907))
in ([], []))
end)
end))
end))
in (let _52_2586 = (encode_elim ())
in (match (_52_2586) with
| (decls2, elim) -> begin
(let g = (let _70_25932 = (let _70_25931 = (let _70_25916 = (let _70_25915 = (let _70_25914 = (let _70_25913 = (let _70_25912 = (let _70_25911 = (let _70_25910 = (let _70_25909 = (let _70_25908 = (Microsoft_FStar_Absyn_Print.sli d)
in (Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" _70_25908))
in Some (_70_25909))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _70_25910))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_25911))
in (_70_25912)::[])
in (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) _70_25913))
in (Support.List.append _70_25914 proxy_fresh))
in (Support.List.append _70_25915 decls_formals))
in (Support.List.append _70_25916 decls_pred))
in (let _70_25930 = (let _70_25929 = (let _70_25928 = (let _70_25920 = (let _70_25919 = (let _70_25918 = (let _70_25917 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _70_25917))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25918))
in (_70_25919, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25920))
in (let _70_25927 = (let _70_25926 = (let _70_25925 = (let _70_25924 = (let _70_25923 = (let _70_25922 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _70_25921 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _70_25922, _70_25921)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25923))
in (_70_25924, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25925))
in (_70_25926)::[])
in (_70_25928)::_70_25927))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_70_25929)
in (Support.List.append _70_25931 _70_25930)))
in (Support.List.append _70_25932 elim))
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
(let _70_25947 = (let _70_25946 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _70_25946))
in Support.Microsoft.FStar.Util.Inl (_70_25947))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _70_25949 = (let _70_25948 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_25948))
in Support.Microsoft.FStar.Util.Inr (_70_25949))
end
| _52_2671 -> begin
(Support.All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _70_25950 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (Support.All.pipe_right _70_25950 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _70_25956 = (let _70_25952 = (let _70_25951 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (Support.All.pipe_left Support.Prims.snd _70_25951))
in (body, _70_25952))
in (let _70_25955 = (let _70_25954 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (Support.All.pipe_left (fun ( _70_25953 ) -> Some (_70_25953)) _70_25954))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _70_25956 _70_25955 body.Microsoft_FStar_Absyn_Syntax.pos)))
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
(let _70_25965 = (let _70_25964 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _70_25963 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _70_25964 _70_25963)))
in (Support.All.failwith _70_25965))
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
(let _70_25971 = (Support.All.pipe_right bindings (Support.List.collect (fun ( lb ) -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _70_25970 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _70_25970 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(raise (Let_rec_unencodeable))
end))))
in (_70_25971, env))
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
in (let t_norm = (let _70_25974 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.All.pipe_right _70_25974 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _52_2760 = (let _70_25975 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _70_25975 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_52_2760) with
| (tok, decl, env) -> begin
(let _70_25978 = (let _70_25977 = (let _70_25976 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_70_25976, tok))
in (_70_25977)::toks)
in (_70_25978, (t_norm)::typs, (decl)::decls, env))
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
end)))) || (Support.All.pipe_right typs (Support.Microsoft.FStar.Util.for_some (fun ( t ) -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (let _70_25981 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (Support.All.pipe_left Support.Prims.op_Negation _70_25981)))))))) with
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
(let _70_25983 = (let _70_25982 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _70_25982))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25983))
end)
in (let _52_2810 = (encode_exp body env')
in (match (_52_2810) with
| (body, decls2) -> begin
(let eqn = (let _70_25992 = (let _70_25991 = (let _70_25988 = (let _70_25987 = (let _70_25986 = (let _70_25985 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_25984 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_25985, _70_25984)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25986))
in ((app)::[], vars, _70_25987))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25988))
in (let _70_25990 = (let _70_25989 = (Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_70_25989))
in (_70_25991, _70_25990)))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25992))
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
(let fuel = (let _70_25993 = (varops.fresh "fuel")
in (_70_25993, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _52_2830 = (Support.All.pipe_right toks (Support.List.fold_left (fun ( _52_2819 ) ( _52_2824 ) -> (match ((_52_2819, _52_2824)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _70_25998 = (let _70_25997 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (Support.All.pipe_left (fun ( _70_25996 ) -> Some (_70_25996)) _70_25997))
in (push_free_var env flid gtok _70_25998))
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
(let decl_g = (let _70_26009 = (let _70_26008 = (let _70_26007 = (Support.List.map Support.Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_70_26007)
in (g, _70_26008, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_26009))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _70_26012 = (let _70_26011 = (let _70_26010 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_70_26010)::vars_tm)
in (g, _70_26011))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26012))
in (let gmax = (let _70_26015 = (let _70_26014 = (let _70_26013 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_70_26013)::vars_tm)
in (g, _70_26014))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26015))
in (let _52_2870 = (encode_exp body env')
in (match (_52_2870) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _70_26024 = (let _70_26023 = (let _70_26020 = (let _70_26019 = (let _70_26018 = (let _70_26017 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_26016 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_70_26017, _70_26016)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_26018))
in ((gsapp)::[], (fuel)::vars, _70_26019))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26020))
in (let _70_26022 = (let _70_26021 = (Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_70_26021))
in (_70_26023, _70_26022)))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26024))
in (let eqn_f = (let _70_26028 = (let _70_26027 = (let _70_26026 = (let _70_26025 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _70_26025))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26026))
in (_70_26027, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26028))
in (let eqn_g' = (let _70_26037 = (let _70_26036 = (let _70_26035 = (let _70_26034 = (let _70_26033 = (let _70_26032 = (let _70_26031 = (let _70_26030 = (let _70_26029 = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (_70_26029)::vars_tm)
in (g, _70_26030))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26031))
in (gsapp, _70_26032))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26033))
in ((gsapp)::[], (fuel)::vars, _70_26034))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26035))
in (_70_26036, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26037))
in (let _52_2893 = (let _52_2880 = (encode_binders None formals env0)
in (match (_52_2880) with
| (vars, v_guards, env, binder_decls, _52_2879) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _70_26038 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _70_26038 ((fuel)::vars)))
in (let _70_26042 = (let _70_26041 = (let _70_26040 = (let _70_26039 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _70_26039))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26040))
in (_70_26041, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26042)))
in (let _52_2890 = (let _52_2887 = (encode_typ_pred' None tres env gapp)
in (match (_52_2887) with
| (g_typing, d3) -> begin
(let _70_26050 = (let _70_26049 = (let _70_26048 = (let _70_26047 = (let _70_26046 = (let _70_26045 = (let _70_26044 = (let _70_26043 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_70_26043, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_26044))
in ((gapp)::[], (fuel)::vars, _70_26045))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26046))
in (_70_26047, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26048))
in (_70_26049)::[])
in (d3, _70_26050))
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
in (let _52_2909 = (let _70_26053 = (Support.List.zip3 gtoks typs bindings)
in (Support.List.fold_left (fun ( _52_2897 ) ( _52_2901 ) -> (match ((_52_2897, _52_2901)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _52_2905 = (encode_one_binding env0 gtok ty bs)
in (match (_52_2905) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _70_26053))
in (match (_52_2909) with
| (decls, eqns, env0) -> begin
(let _52_2918 = (let _70_26055 = (Support.All.pipe_right decls Support.List.flatten)
in (Support.All.pipe_right _70_26055 (Support.List.partition (fun ( _52_29 ) -> (match (_52_29) with
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
(let msg = (let _70_26058 = (Support.All.pipe_right bindings (Support.List.map (fun ( lb ) -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (Support.All.pipe_right _70_26058 (Support.String.concat " and ")))
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
and encode_free_var = (fun ( env ) ( lid ) ( tt ) ( t_norm ) ( quals ) -> (match (((let _70_26071 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (Support.All.pipe_left Support.Prims.op_Negation _70_26071)) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm))) with
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
(let _70_26073 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _70_26073))
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
in (let _70_26086 = (let _70_26085 = (let _70_26084 = (let _70_26083 = (let _70_26082 = (let _70_26081 = (let _70_26080 = (let _70_26079 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_26079))
in (vapp, _70_26080))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26081))
in ((vapp)::[], vars, _70_26082))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26083))
in (_70_26084, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26085))
in (_70_26086)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _52_3038 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_52_3038) with
| (_52_3033, (xxsym, _52_3036)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _70_26095 = (let _70_26094 = (let _70_26093 = (let _70_26092 = (let _70_26091 = (let _70_26090 = (let _70_26089 = (let _70_26088 = (let _70_26087 = (mk_term_projector_name d f)
in (_70_26087, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26088))
in (vapp, _70_26089))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26090))
in ((vapp)::[], vars, _70_26091))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26092))
in (_70_26093, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26094))
in (_70_26095)::[]))
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
(let _70_26096 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_26096, decls1))
end
| Some (p) -> begin
(let _52_3054 = (encode_formula p env')
in (match (_52_3054) with
| (g, ds) -> begin
(let _70_26097 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_70_26097, (Support.List.append decls1 ds)))
end))
end)
in (match (_52_3057) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _70_26099 = (let _70_26098 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _70_26098))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26099))
in (let _52_3088 = (let vname_decl = (let _70_26102 = (let _70_26101 = (Support.All.pipe_right formals (Support.List.map (fun ( _52_32 ) -> (match (_52_32) with
| (Support.Microsoft.FStar.Util.Inl (_52_3062), _52_3065) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_3068 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _70_26101, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_26102))
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
(let _70_26106 = (let _70_26105 = (let _70_26104 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Support.All.pipe_left (fun ( _70_26103 ) -> Some (_70_26103)) _70_26104))
in (push_free_var env lid vname _70_26105))
in ((Support.List.append decls2 ((tok_typing)::[])), _70_26106))
end
| _52_3079 -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _70_26107 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _70_26107))
in (let name_tok_corr = (let _70_26111 = (let _70_26110 = (let _70_26109 = (let _70_26108 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _70_26108))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26109))
in (_70_26110, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26111))
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
(let typingAx = (let _70_26115 = (let _70_26114 = (let _70_26113 = (let _70_26112 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _70_26112))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26113))
in (_70_26114, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26115))
in (let g = (let _70_26117 = (let _70_26116 = (mk_disc_proj_axioms vapp vars)
in (typingAx)::_70_26116)
in (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) _70_26117))
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
(let _70_26132 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _70_26131 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _70_26130 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.fprint3 "Normalized %s : %s to %s\n" _70_26132 _70_26131 _70_26130))))
end
| false -> begin
()
end)
in (let _52_3123 = (encode_typ_pred' None t1 env xx)
in (match (_52_3123) with
| (t, decls') -> begin
(let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_26136 = (let _70_26135 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _70_26134 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _70_26133 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" _70_26135 _70_26134 _70_26133))))
in Some (_70_26136))
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
(let g = (let _70_26142 = (let _70_26141 = (let _70_26140 = (let _70_26139 = (let _70_26138 = (let _70_26137 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_70_26137))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _70_26138))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_26139))
in (_70_26140)::[])
in (Support.List.append _70_26141 decls'))
in (Support.List.append _70_26142 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
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
(let _70_26150 = (Support.All.pipe_left (fun ( _70_26146 ) -> Microsoft_FStar_ToSMT_Term.Echo (_70_26146)) (Support.Prims.fst l))
in (let _70_26149 = (let _70_26148 = (let _70_26147 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_70_26147))
in (_70_26148)::[])
in (_70_26150)::_70_26149))
end))))
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun ( tcenv ) -> (let _70_26155 = (let _70_26154 = (let _70_26153 = (Support.Microsoft.FStar.Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _70_26153; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_70_26154)::[])
in (Support.ST.op_Colon_Equals last_env _70_26155)))

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

let pop = (fun ( msg ) -> (let _52_3224 = (let _70_26176 = (pop_env ())
in (Support.All.pipe_left Support.Prims.ignore _70_26176))
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
(let _70_26190 = (let _70_26189 = (let _70_26188 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.String.strcat "encoding sigelt " _70_26188))
in Microsoft_FStar_ToSMT_Term.Caption (_70_26189))
in (_70_26190)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _52_3250 = (encode_sigelt env se)
in (match (_52_3250) with
| (decls, env) -> begin
(let _52_3251 = (set_env env)
in (let _70_26191 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _70_26191)))
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
(let _70_26196 = (Support.All.pipe_right (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name _70_26196))
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

let solve = (fun ( tcenv ) ( q ) -> (let _52_3276 = (let _70_26205 = (let _70_26204 = (let _70_26203 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_26203))
in (Support.Microsoft.FStar.Util.format1 "Starting query at %s" _70_26204))
in (push _70_26205))
in (let pop = (fun ( _52_3279 ) -> (match (()) with
| () -> begin
(let _70_26210 = (let _70_26209 = (let _70_26208 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_26208))
in (Support.Microsoft.FStar.Util.format1 "Ending query at %s" _70_26209))
in (pop _70_26210))
end))
in (let _52_3309 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun ( bs ) ( b ) -> (b)::bs) [])
in (let _52_3292 = (let _70_26214 = (Support.List.filter (fun ( _52_33 ) -> (match (_52_33) with
| Microsoft_FStar_Tc_Env.Binding_sig (_52_3286) -> begin
false
end
| _52_3289 -> begin
true
end)) bindings)
in (encode_env_bindings env _70_26214))
in (match (_52_3292) with
| (env_decls, env) -> begin
(let _52_3293 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_26215 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" _70_26215))
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
in (let qry = (let _70_26217 = (let _70_26216 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_70_26216, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26217))
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
(let _70_26239 = (let _70_26238 = (let _70_26223 = (let _70_26222 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" _70_26222))
in Microsoft_FStar_ToSMT_Term.Caption (_70_26223))
in (let _70_26237 = (let _70_26236 = (let _70_26228 = (let _70_26227 = (let _70_26226 = (let _70_26225 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _70_26224 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_70_26225, _70_26224)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26226))
in (_70_26227, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26228))
in (let _70_26235 = (let _70_26234 = (let _70_26233 = (let _70_26232 = (let _70_26231 = (let _70_26230 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _70_26229 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_70_26230, _70_26229)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26231))
in (_70_26232, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26233))
in (_70_26234)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_70_26236)::_70_26235))
in (_70_26238)::_70_26237))
in (Support.List.append _70_26239 suffix))
end))
in (let check = (fun ( p ) -> (let initial_config = (let _70_26243 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _70_26242 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_70_26243, _70_26242)))
in (let alt_configs = (let _70_26262 = (let _70_26261 = (match (((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel))) with
| true -> begin
(let _70_26246 = (let _70_26245 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _70_26244 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_26245, _70_26244)))
in (_70_26246)::[])
end
| false -> begin
[]
end)
in (let _70_26260 = (let _70_26259 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2) > (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _70_26249 = (let _70_26248 = ((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2)
in (let _70_26247 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_26248, _70_26247)))
in (_70_26249)::[])
end
| false -> begin
[]
end)
in (let _70_26258 = (let _70_26257 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) > (Support.ST.read Microsoft_FStar_Options.initial_fuel)) && ((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel)))) with
| true -> begin
(let _70_26252 = (let _70_26251 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _70_26250 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_26251, _70_26250)))
in (_70_26252)::[])
end
| false -> begin
[]
end)
in (let _70_26256 = (let _70_26255 = (match (((Support.ST.read Microsoft_FStar_Options.min_fuel) < (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _70_26254 = (let _70_26253 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (_70_26253, 1))
in (_70_26254)::[])
end
| false -> begin
[]
end)
in (_70_26255)::[])
in (_70_26257)::_70_26256))
in (_70_26259)::_70_26258))
in (_70_26261)::_70_26260))
in (Support.List.flatten _70_26262))
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
(let _70_26274 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_26274 (cb p [])))
end
| _52_3365 -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(let _70_26276 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_26276 (fun ( _52_3371 ) -> (match (_52_3371) with
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
in (let _70_26280 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_26280 (cb p alt_configs))))))))
in (let process_query = (fun ( q ) -> (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let _52_3384 = (let _70_26286 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _70_26286 q))
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





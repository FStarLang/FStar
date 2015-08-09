
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

let mk_typ_projector_name = (fun ( lid ) ( a ) -> (let _70_23908 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _70_23908)))

let mk_term_projector_name = (fun ( lid ) ( a ) -> (let a = (let _70_23913 = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname)
in {Microsoft_FStar_Absyn_Syntax.ppname = _70_23913; Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname})
in (let _70_23914 = (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))
in (Support.All.pipe_left escape _70_23914))))

let primitive_projector_by_pos = (fun ( env ) ( lid ) ( i ) -> (let fail = (fun ( _52_62 ) -> (match (()) with
| () -> begin
(let _70_23924 = (let _70_23923 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" _70_23923 lid.Microsoft_FStar_Absyn_Syntax.str))
in (Support.All.failwith _70_23924))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _70_23925 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_23925.Microsoft_FStar_Absyn_Syntax.n)) with
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

let mk_term_projector_name_by_pos = (fun ( lid ) ( i ) -> (let _70_23931 = (let _70_23930 = (Support.Microsoft.FStar.Util.string_of_int i)
in (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str _70_23930))
in (Support.All.pipe_left escape _70_23931)))

let mk_typ_projector = (fun ( lid ) ( a ) -> (let _70_23937 = (let _70_23936 = (mk_typ_projector_name lid a)
in (_70_23936, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_23937)))

let mk_term_projector = (fun ( lid ) ( a ) -> (let _70_23943 = (let _70_23942 = (mk_term_projector_name lid a)
in (_70_23942, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_23943)))

let mk_term_projector_by_pos = (fun ( lid ) ( i ) -> (let _70_23949 = (let _70_23948 = (mk_term_projector_name_by_pos lid i)
in (_70_23948, Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort))))
in (Microsoft_FStar_ToSMT_Term.mkFreeV _70_23949)))

let mk_data_tester = (fun ( env ) ( l ) ( x ) -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let is_Mkvarops_t = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkvarops_t"))

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun ( _52_101 ) -> (match (()) with
| () -> begin
(let _70_24053 = (Support.Microsoft.FStar.Util.smap_create 100)
in (let _70_24052 = (Support.Microsoft.FStar.Util.smap_create 100)
in (_70_24053, _70_24052)))
end))
in (let scopes = (let _70_24055 = (let _70_24054 = (new_scope ())
in (_70_24054)::[])
in (Support.Microsoft.FStar.Util.mk_ref _70_24055))
in (let mk_unique = (fun ( y ) -> (let y = (escape y)
in (let y = (match ((let _70_24059 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _70_24059 (fun ( _52_109 ) -> (match (_52_109) with
| (names, _52_108) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_52_112) -> begin
(let _52_114 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _70_24061 = (let _70_24060 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _70_24060))
in (Support.String.strcat (Support.String.strcat y "__") _70_24061)))
end)
in (let top_scope = (let _70_24063 = (let _70_24062 = (Support.ST.read scopes)
in (Support.List.hd _70_24062))
in (Support.All.pipe_left Support.Prims.fst _70_24063))
in (let _52_118 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun ( pp ) ( rn ) -> (let _70_24069 = (let _70_24068 = (Support.All.pipe_left mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText)
in (Support.String.strcat _70_24068 "__"))
in (Support.String.strcat _70_24069 rn.Microsoft_FStar_Absyn_Syntax.idText)))
in (let new_fvar = (fun ( lid ) -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun ( _52_126 ) -> (match (()) with
| () -> begin
(let _52_127 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.ST.read ctr))
end))
in (let fresh = (fun ( pfx ) -> (let _70_24077 = (let _70_24076 = (next_id ())
in (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int _70_24076))
in (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx _70_24077)))
in (let string_const = (fun ( s ) -> (match ((let _70_24081 = (Support.ST.read scopes)
in (Support.Microsoft.FStar.Util.find_map _70_24081 (fun ( _52_136 ) -> (match (_52_136) with
| (_52_134, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _70_24082 = (Microsoft_FStar_ToSMT_Term.mk_String_const id)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxString _70_24082))
in (let top_scope = (let _70_24084 = (let _70_24083 = (Support.ST.read scopes)
in (Support.List.hd _70_24083))
in (Support.All.pipe_left Support.Prims.snd _70_24084))
in (let _52_143 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun ( _52_146 ) -> (match (()) with
| () -> begin
(let _70_24089 = (let _70_24088 = (new_scope ())
in (let _70_24087 = (Support.ST.read scopes)
in (_70_24088)::_70_24087))
in (Support.ST.op_Colon_Equals scopes _70_24089))
end))
in (let pop = (fun ( _52_148 ) -> (match (()) with
| () -> begin
(let _70_24093 = (let _70_24092 = (Support.ST.read scopes)
in (Support.List.tl _70_24092))
in (Support.ST.op_Colon_Equals scopes _70_24093))
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

let unmangle = (fun ( x ) -> (let _70_24109 = (let _70_24108 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname)
in (let _70_24107 = (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname)
in (_70_24108, _70_24107)))
in (Microsoft_FStar_Absyn_Util.mkbvd _70_24109)))

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

let print_env = (fun ( e ) -> (let _70_24195 = (Support.All.pipe_right e.bindings (Support.List.map (fun ( _52_2 ) -> (match (_52_2) with
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
in (Support.All.pipe_right _70_24195 (Support.String.concat ", "))))

let lookup_binding = (fun ( env ) ( f ) -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun ( env ) ( t ) -> (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_24205 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in Some (_70_24205))
end
| false -> begin
None
end))

let fresh_fvar = (fun ( x ) ( s ) -> (let xsym = (varops.fresh x)
in (let _70_24210 = (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _70_24210))))

let gen_term_var = (fun ( env ) ( x ) -> (let ysym = (let _70_24215 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@x" _70_24215))
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
(let _70_24230 = (let _70_24229 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" _70_24229))
in (Support.All.failwith _70_24230))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun ( env ) ( x ) -> (let ysym = (let _70_24235 = (Support.Microsoft.FStar.Util.string_of_int env.depth)
in (Support.String.strcat "@a" _70_24235))
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
(let _70_24250 = (let _70_24249 = (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" _70_24249))
in (Support.All.failwith _70_24250))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun ( env ) ( x ) -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (let _70_24261 = (let _52_295 = env
in (let _70_24260 = (let _70_24259 = (let _70_24258 = (let _70_24257 = (let _70_24256 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _70_24255 ) -> Some (_70_24255)) _70_24256))
in (x, fname, _70_24257, None))
in Binding_fvar (_70_24258))
in (_70_24259)::env.bindings)
in {bindings = _70_24260; depth = _52_295.depth; tcenv = _52_295.tcenv; warn = _52_295.warn; cache = _52_295.cache; nolabels = _52_295.nolabels; use_zfuel_name = _52_295.use_zfuel_name; encode_non_total_function_typ = _52_295.encode_non_total_function_typ}))
in (fname, ftok, _70_24261)))))

let try_lookup_lid = (fun ( env ) ( a ) -> (lookup_binding env (fun ( _52_5 ) -> (match (_52_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _52_307 -> begin
None
end))))

let lookup_lid = (fun ( env ) ( a ) -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _70_24272 = (let _70_24271 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _70_24271))
in (Support.All.failwith _70_24272))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_317 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _52_317.depth; tcenv = _52_317.tcenv; warn = _52_317.warn; cache = _52_317.cache; nolabels = _52_317.nolabels; use_zfuel_name = _52_317.use_zfuel_name; encode_non_total_function_typ = _52_317.encode_non_total_function_typ}))

let push_zfuel_name = (fun ( env ) ( x ) ( f ) -> (let _52_326 = (lookup_lid env x)
in (match (_52_326) with
| (t1, t2, _52_325) -> begin
(let t3 = (let _70_24289 = (let _70_24288 = (let _70_24287 = (Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_70_24287)::[])
in (f, _70_24288))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24289))
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
(match ((let _70_24293 = (let _70_24292 = (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)
in (Support.All.pipe_right _70_24292 Support.Prims.fst))
in (Support.Microsoft.FStar.Util.starts_with _70_24293 "fuel"))) with
| true -> begin
(let _70_24294 = (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF _70_24294 fuel))
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
(let _70_24296 = (let _70_24295 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Name not found: %s" _70_24295))
in (Support.All.failwith _70_24296))
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
in (let _70_24311 = (let _52_392 = env
in (let _70_24310 = (let _70_24309 = (let _70_24308 = (let _70_24307 = (let _70_24306 = (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))
in (Support.All.pipe_left (fun ( _70_24305 ) -> Some (_70_24305)) _70_24306))
in (x, fname, _70_24307))
in Binding_ftvar (_70_24308))
in (_70_24309)::env.bindings)
in {bindings = _70_24310; depth = _52_392.depth; tcenv = _52_392.tcenv; warn = _52_392.warn; cache = _52_392.cache; nolabels = _52_392.nolabels; use_zfuel_name = _52_392.use_zfuel_name; encode_non_total_function_typ = _52_392.encode_non_total_function_typ}))
in (fname, ftok, _70_24311)))))

let lookup_tlid = (fun ( env ) ( a ) -> (match ((lookup_binding env (fun ( _52_6 ) -> (match (_52_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _52_403 -> begin
None
end)))) with
| None -> begin
(let _70_24318 = (let _70_24317 = (Microsoft_FStar_Absyn_Print.sli a)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _70_24317))
in (Support.All.failwith _70_24318))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun ( env ) ( x ) ( fname ) ( ftok ) -> (let _52_411 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _52_411.depth; tcenv = _52_411.tcenv; warn = _52_411.warn; cache = _52_411.cache; nolabels = _52_411.nolabels; use_zfuel_name = _52_411.use_zfuel_name; encode_non_total_function_typ = _52_411.encode_non_total_function_typ}))

let lookup_free_tvar = (fun ( env ) ( a ) -> (match ((let _70_24329 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_24329 Support.Prims.snd))) with
| None -> begin
(let _70_24331 = (let _70_24330 = (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" _70_24330))
in (Support.All.failwith _70_24331))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun ( env ) ( a ) -> (let _70_24334 = (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_24334 Support.Prims.fst)))

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
(let _70_24350 = (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v)
in (Support.All.pipe_right _70_24350 Support.Option.isNone))
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

let trivial_post = (fun ( t ) -> (let _70_24372 = (let _70_24371 = (let _70_24369 = (Microsoft_FStar_Absyn_Syntax.null_v_binder t)
in (_70_24369)::[])
in (let _70_24370 = (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)
in (_70_24371, _70_24370)))
in (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam _70_24372 None t.Microsoft_FStar_Absyn_Syntax.pos)))

let mk_ApplyE = (fun ( e ) ( vars ) -> (Support.All.pipe_right vars (Support.List.fold_left (fun ( out ) ( var ) -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(let _70_24379 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyET out _70_24379))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(let _70_24380 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEF out _70_24380))
end
| _52_509 -> begin
(let _70_24381 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyEE out _70_24381))
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
(let _70_24394 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTT out _70_24394))
end
| _52_524 -> begin
(let _70_24395 = (Microsoft_FStar_ToSMT_Term.mkFreeV var)
in (Microsoft_FStar_ToSMT_Term.mk_ApplyTE out _70_24395))
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
(let _70_24451 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c))
in (Microsoft_FStar_ToSMT_Term.boxInt _70_24451))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(let _70_24452 = (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i))
in (Microsoft_FStar_ToSMT_Term.boxInt _70_24452))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(let _70_24453 = (Microsoft_FStar_ToSMT_Term.mkInteger i)
in (Microsoft_FStar_ToSMT_Term.boxInt _70_24453))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(let _70_24457 = (let _70_24456 = (let _70_24455 = (let _70_24454 = (Microsoft_FStar_ToSMT_Term.mkInteger' i)
in (Microsoft_FStar_ToSMT_Term.boxInt _70_24454))
in (_70_24455)::[])
in ("Int32.Int32", _70_24456))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24457))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _52_609)) -> begin
(let _70_24458 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_bytes bytes)
in (varops.string_const _70_24458))
end
| c -> begin
(let _70_24460 = (let _70_24459 = (Microsoft_FStar_Absyn_Print.const_to_string c)
in (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" _70_24459))
in (Support.All.failwith _70_24460))
end))

let as_function_typ = (fun ( env ) ( t0 ) -> (let rec aux = (fun ( norm ) ( t ) -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_52_620) -> begin
t
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_52_623) -> begin
(let _70_24469 = (Microsoft_FStar_Absyn_Util.unrefine t)
in (aux true _70_24469))
end
| _52_626 -> begin
(match (norm) with
| true -> begin
(let _70_24470 = (whnf env t)
in (aux false _70_24470))
end
| false -> begin
(let _70_24473 = (let _70_24472 = (Support.Microsoft.FStar.Range.string_of_range t0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_24471 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (Support.Microsoft.FStar.Util.format2 "(%s) Expected a function typ; got %s" _70_24472 _70_24471)))
in (Support.All.failwith _70_24473))
end)
end)))
in (aux true t0)))

let rec encode_knd_term = (fun ( k ) ( env ) -> (match ((let _70_24505 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _70_24505.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
(Microsoft_FStar_ToSMT_Term.mk_Kind_type, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_52_631, k0)) -> begin
(let _52_635 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _70_24507 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (let _70_24506 = (Microsoft_FStar_Absyn_Print.kind_to_string k0)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding kind abbrev %s, expanded to %s\n" _70_24507 _70_24506)))
end
| false -> begin
()
end)
in (encode_knd_term k0 env))
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _52_639)) -> begin
(let _70_24509 = (let _70_24508 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Kind_uvar _70_24508))
in (_70_24509, []))
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, kbody)) -> begin
(let tsym = (let _70_24510 = (varops.fresh "t")
in (_70_24510, Microsoft_FStar_ToSMT_Term.Type_sort))
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
(let _70_24519 = (let _70_24518 = (let _70_24517 = (Microsoft_FStar_ToSMT_Term.mk_PreKind app)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_24517))
in (_70_24518, body))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_24519))
end)
in (let _70_24521 = (let _70_24520 = (Microsoft_FStar_ToSMT_Term.mkImp (g, body))
in ((app)::[], (x)::[], _70_24520))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24521)))))
end
| _52_680 -> begin
(Support.All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _70_24523 = (Microsoft_FStar_ToSMT_Term.free_variables k_interp)
in (Support.All.pipe_right _70_24523 (Support.List.filter (fun ( _52_685 ) -> (match (_52_685) with
| (x, _52_684) -> begin
(x <> (Support.Prims.fst tsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((k', sorts, _52_691)) -> begin
(let _70_24526 = (let _70_24525 = (let _70_24524 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (k', _70_24524))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24525))
in (_70_24526, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_24527 = (Microsoft_FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_70_24527))
end
| false -> begin
None
end)
in (let kdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _70_24529 = (let _70_24528 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _70_24528))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24529))
in (let t_has_k = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _70_24538 = (let _70_24537 = (let _70_24536 = (let _70_24535 = (let _70_24534 = (let _70_24533 = (let _70_24532 = (let _70_24531 = (let _70_24530 = (Microsoft_FStar_ToSMT_Term.mk_PreKind t)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_24530))
in (_70_24531, k_interp))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_24532))
in (t_has_k, _70_24533))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_24534))
in ((t_has_k)::[], (tsym)::cvars, _70_24535))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24536))
in (_70_24537, Some ((Support.String.strcat ksym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24538))
in (let k_decls = (Support.List.append (Support.List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _52_703 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _52_706 -> begin
(let _70_24540 = (let _70_24539 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" _70_24539))
in (Support.All.failwith _70_24540))
end))
and encode_knd = (fun ( k ) ( env ) ( t ) -> (let _52_712 = (encode_knd_term k env)
in (match (_52_712) with
| (k, decls) -> begin
(let _70_24544 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t k)
in (_70_24544, decls))
end)))
and encode_binders = (fun ( fuel_opt ) ( bs ) ( env ) -> (let _52_716 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_24548 = (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" _70_24548))
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
(let _70_24552 = (Microsoft_FStar_Absyn_Print.strBvd a)
in (let _70_24551 = (Microsoft_FStar_Absyn_Print.kind_to_string k)
in (Support.Microsoft.FStar.Util.fprint3 "Encoding type binder %s (%s) at kind %s\n" _70_24552 aasym _70_24551)))
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
(let _52_754 = (let _70_24553 = (norm_t env t)
in (encode_typ_pred' fuel_opt _70_24553 env xx))
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
(let _70_24558 = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_70_24558, decls))
end))))
and encode_typ_term = (fun ( t ) ( env ) -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _70_24561 = (lookup_typ_var env a)
in (_70_24561, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _70_24562 = (lookup_free_tvar env fv)
in (_70_24562, []))
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
(match (((env.encode_non_total_function_typ && (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res))) with
| true -> begin
(let _52_792 = (encode_binders None binders env)
in (match (_52_792) with
| (vars, guards, env', decls, _52_791) -> begin
(let fsym = (let _70_24563 = (varops.fresh "f")
in (_70_24563, Microsoft_FStar_ToSMT_Term.Term_sort))
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
(let _70_24564 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_24564, decls))
end
| Some (pre) -> begin
(let _52_807 = (encode_formula pre env')
in (match (_52_807) with
| (guard, decls0) -> begin
(let _70_24565 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_70_24565, (Support.List.append decls decls0)))
end))
end)
in (match (_52_810) with
| (guards, guard_decls) -> begin
(let t_interp = (let _70_24567 = (let _70_24566 = (Microsoft_FStar_ToSMT_Term.mkImp (guards, res_pred))
in ((app)::[], vars, _70_24566))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24567))
in (let cvars = (let _70_24569 = (Microsoft_FStar_ToSMT_Term.free_variables t_interp)
in (Support.All.pipe_right _70_24569 (Support.List.filter (fun ( _52_815 ) -> (match (_52_815) with
| (x, _52_814) -> begin
(x <> (Support.Prims.fst fsym))
end)))))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _52_821)) -> begin
(let _70_24572 = (let _70_24571 = (let _70_24570 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t', _70_24570))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24571))
in (_70_24572, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_24573 = (Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_70_24573))
end
| false -> begin
None
end)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _70_24575 = (let _70_24574 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_24574))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24575))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _70_24577 = (let _70_24576 = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (_70_24576, Some ((Support.String.strcat tsym " kinding"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24577))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let pre_typing = (let _70_24584 = (let _70_24583 = (let _70_24582 = (let _70_24581 = (let _70_24580 = (let _70_24579 = (let _70_24578 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _70_24578))
in (f_has_t, _70_24579))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24580))
in ((f_has_t)::[], (fsym)::cvars, _70_24581))
in (mkForall_fuel _70_24582))
in (_70_24583, Some ("pre-typing for functions")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24584))
in (let t_interp = (let _70_24588 = (let _70_24587 = (let _70_24586 = (let _70_24585 = (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t, t_interp))
in ((f_has_t)::[], (fsym)::cvars, _70_24585))
in (mkForall_fuel _70_24586))
in (_70_24587, Some ((Support.String.strcat tsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24588))
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
in (let t_kinding = (let _70_24590 = (let _70_24589 = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (_70_24589, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24590))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _70_24597 = (let _70_24596 = (let _70_24595 = (let _70_24594 = (let _70_24593 = (let _70_24592 = (let _70_24591 = (Microsoft_FStar_ToSMT_Term.mk_PreType f)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" _70_24591))
in (f_has_t, _70_24592))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24593))
in ((f_has_t)::[], (fsym)::[], _70_24594))
in (mkForall_fuel _70_24595))
in (_70_24596, Some ("pre-typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24597))
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
(let encoding = (let _70_24599 = (let _70_24598 = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t)
in (_70_24598, refinement))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_24599))
in (let cvars = (let _70_24601 = (Microsoft_FStar_ToSMT_Term.free_variables encoding)
in (Support.All.pipe_right _70_24601 (Support.List.filter (fun ( _52_881 ) -> (match (_52_881) with
| (y, _52_880) -> begin
(y <> x)
end)))))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_887, _52_889)) -> begin
(let _70_24604 = (let _70_24603 = (let _70_24602 = (Support.All.pipe_right cvars (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV))
in (t, _70_24602))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24603))
in (_70_24604, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map Support.Prims.snd cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _70_24606 = (let _70_24605 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_24605))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24606))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (let _70_24608 = (let _70_24607 = (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in ((x_has_t)::[], (xfv)::cvars, _70_24607))
in (mkForall_fuel _70_24608))
in (let t_decls = (let _70_24615 = (let _70_24614 = (let _70_24613 = (let _70_24612 = (let _70_24611 = (let _70_24610 = (let _70_24609 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in Some (_70_24609))
in (assumption, _70_24610))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24611))
in (_70_24612)::[])
in (Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::_70_24613)
in (tdecl)::_70_24614)
in (Support.List.append (Support.List.append decls decls') _70_24615))
in (let _52_902 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (let _70_24616 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _70_24616))
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
in (let t = (let _70_24621 = (let _70_24620 = (Support.List.map (fun ( _52_10 ) -> (match (_52_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (head, _70_24620))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24621))
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
(let ttm = (let _70_24622 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar _70_24622))
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
(let key_body = (let _70_24626 = (let _70_24625 = (let _70_24624 = (let _70_24623 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_24623, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24624))
in ([], vars, _70_24625))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24626))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_976, _52_978)) -> begin
(let _70_24629 = (let _70_24628 = (let _70_24627 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _70_24627))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24628))
in (_70_24629, []))
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
in (let t = (let _70_24631 = (let _70_24630 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _70_24630))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24631))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _70_24638 = (let _70_24637 = (let _70_24636 = (let _70_24635 = (let _70_24634 = (let _70_24633 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_24632 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_24633, _70_24632)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24634))
in ((app)::[], (Support.List.append vars cvars), _70_24635))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24636))
in (_70_24637, Some ("Typ_lam interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24638))
in (let kinding = (let _52_993 = (let _70_24639 = (Microsoft_FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _70_24639 env t))
in (match (_52_993) with
| (ktm, decls'') -> begin
(let _70_24643 = (let _70_24642 = (let _70_24641 = (let _70_24640 = (Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm))
in (_70_24640, Some ("Typ_lam kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24641))
in (_70_24642)::[])
in (Support.List.append decls'' _70_24643))
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
(let _70_24644 = (Microsoft_FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _70_24644 env))
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _70_24649 = (let _70_24648 = (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_24647 = (Microsoft_FStar_Absyn_Print.tag_of_typ t0)
in (let _70_24646 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _70_24645 = (Microsoft_FStar_Absyn_Print.typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _70_24648 _70_24647 _70_24646 _70_24645)))))
in (Support.All.failwith _70_24649))
end)))
and encode_exp = (fun ( e ) ( env ) -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_52_1015) -> begin
(let _70_24652 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in (encode_exp _70_24652 env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _52_1022)) -> begin
(let _70_24653 = (lookup_free_var env v)
in (_70_24653, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _70_24654 = (encode_const c)
in (_70_24654, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _52_1030)) -> begin
(let _52_1033 = (Support.ST.op_Colon_Equals e.Microsoft_FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _52_1037))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _52_1043)) -> begin
(let e = (let _70_24655 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar _70_24655))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun ( _52_1052 ) -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _70_24658 = (Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_70_24658, (decl)::[]))))
end))
in (match ((Support.ST.read e.Microsoft_FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _52_1056 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
(match ((let _70_24659 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (Support.All.pipe_left Support.Prims.op_Negation _70_24659))) with
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
in (let e = (let _70_24661 = (let _70_24660 = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, _70_24660))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs _70_24661 (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos))
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
(let key_body = (let _70_24665 = (let _70_24664 = (let _70_24663 = (let _70_24662 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_24662, body))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24663))
in ([], vars, _70_24664))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24665))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _52_1090, _52_1092)) -> begin
(let _70_24668 = (let _70_24667 = (let _70_24666 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (t, _70_24666))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24667))
in (_70_24668, []))
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
in (let f = (let _70_24670 = (let _70_24669 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _70_24669))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_24670))
in (let app = (mk_ApplyE f vars)
in (let _52_1106 = (encode_typ_pred' None tfun env f)
in (match (_52_1106) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _70_24672 = (let _70_24671 = (Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t))
in (_70_24671, Some ((Support.String.strcat fsym " typing"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24672))
in (let interp_f = (let _70_24679 = (let _70_24678 = (let _70_24677 = (let _70_24676 = (let _70_24675 = (let _70_24674 = (Microsoft_FStar_ToSMT_Term.mk_IsTyped app)
in (let _70_24673 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_24674, _70_24673)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24675))
in ((app)::[], (Support.List.append vars cvars), _70_24676))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24677))
in (_70_24678, Some ((Support.String.strcat fsym " interpretation"))))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24679))
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
(let _70_24680 = (Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_70_24680, (Support.List.append decls1 decls2)))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_52_1162); Microsoft_FStar_Absyn_Syntax.tk = _52_1160; Microsoft_FStar_Absyn_Syntax.pos = _52_1158; Microsoft_FStar_Absyn_Syntax.fvs = _52_1156; Microsoft_FStar_Absyn_Syntax.uvs = _52_1154}, _52_1166)) -> begin
(let _70_24681 = (whnf_e env e)
in (encode_exp _70_24681 env))
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
in (let ty = (let _70_24684 = (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (Support.All.pipe_right _70_24684 (Microsoft_FStar_Absyn_Util.subst_typ subst)))
in (let _52_1194 = (encode_typ_pred' None ty env app_tm)
in (match (_52_1194) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _70_24686 = (let _70_24685 = (Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type))
in (_70_24685, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_24686))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun ( fv ) -> (let _52_1201 = (lookup_free_var_sym env fv)
in (match (_52_1201) with
| (fname, fuel_args) -> begin
(let tm = (let _70_24692 = (let _70_24691 = (let _70_24690 = (Support.List.map (fun ( _52_11 ) -> (match (_52_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)
in (Support.List.append fuel_args _70_24690))
in (fname, _70_24691))
in (Microsoft_FStar_ToSMT_Term.mkApp' _70_24692))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _52_1208 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186")))) with
| true -> begin
(let _70_24694 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _70_24693 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" _70_24694 _70_24693)))
end
| false -> begin
()
end)
in (let head_type = (let _70_24697 = (let _70_24696 = (let _70_24695 = (Microsoft_FStar_Tc_Recheck.recompute_typ head)
in (Microsoft_FStar_Absyn_Util.unrefine _70_24695))
in (whnf env _70_24696))
in (Support.All.pipe_left Microsoft_FStar_Absyn_Util.unrefine _70_24697))
in (let _52_1211 = (match ((Support.All.pipe_left (Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding")))) with
| true -> begin
(let _70_24700 = (Microsoft_FStar_Absyn_Print.exp_to_string head)
in (let _70_24699 = (Microsoft_FStar_Absyn_Print.tag_of_exp head)
in (let _70_24698 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" _70_24700 _70_24699 _70_24698))))
end
| false -> begin
()
end)
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _70_24704 = (let _70_24703 = (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_24702 = (Microsoft_FStar_Absyn_Print.exp_to_string e0)
in (let _70_24701 = (Microsoft_FStar_Absyn_Print.typ_to_string head_type)
in (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" _70_24703 _70_24702 _70_24701))))
in (Support.All.failwith _70_24704))
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
in (let _70_24705 = (Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort))
in (_70_24705, (decl_e)::[])))))
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
(let _70_24716 = (let _70_24715 = (let _70_24714 = (let _70_24713 = (let _70_24712 = (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
in (w, _70_24712))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_24713))
in (guard, _70_24714))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_24715))
in (_70_24716, decls2))
end))
end)
in (match (_52_1309) with
| (guard, decls2) -> begin
(let _52_1312 = (encode_exp br env)
in (match (_52_1312) with
| (br, decls3) -> begin
(let _70_24717 = (Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_70_24717, (Support.List.append (Support.List.append decls decls2) decls3)))
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
(let _70_24720 = (let _70_24719 = (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos)
in (let _70_24718 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" _70_24719 _70_24718)))
in (Support.All.failwith _70_24720))
end))))
and encode_pat = (fun ( env ) ( pat ) -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _52_1324 -> begin
(let _70_24723 = (encode_one_pat env pat)
in (_70_24723)::[])
end))
and encode_one_pat = (fun ( env ) ( pat ) -> (let _52_1327 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_24726 = (Microsoft_FStar_Absyn_Print.pat_to_string pat)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" _70_24726))
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
(let _70_24734 = (let _70_24733 = (encode_const c)
in (scrutinee, _70_24733))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_24734))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, _52_1381, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( _52_1390 ) -> (match (_52_1390) with
| (arg, _52_1389) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _70_24737 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _70_24737)))
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
(let _70_24745 = (Support.All.pipe_right args (Support.List.mapi (fun ( i ) ( _52_1426 ) -> (match (_52_1426) with
| (arg, _52_1425) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (let _70_24744 = (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _70_24744)))
end))))
in (Support.All.pipe_right _70_24745 Support.List.flatten))
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
and encode_function_type_as_formula = (fun ( induction_on ) ( t ) ( env ) -> (let v_or_t_pat = (fun ( p ) -> (match ((let _70_24759 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _70_24759.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1475, (Support.Microsoft.FStar.Util.Inl (_52_1482), _52_1485)::(Support.Microsoft.FStar.Util.Inr (e), _52_1479)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1491, (Support.Microsoft.FStar.Util.Inl (t), _52_1495)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _52_1501 -> begin
(Support.All.failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun ( p ) -> (match ((let _70_24762 = (Microsoft_FStar_Absyn_Util.unmeta_exp p)
in _70_24762.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_52_1505, _52_1517::(Support.Microsoft.FStar.Util.Inr (hd), _52_1514)::(Support.Microsoft.FStar.Util.Inr (tl), _52_1509)::[])) -> begin
(let _70_24764 = (v_or_t_pat hd)
in (let _70_24763 = (lemma_pats tl)
in (_70_24764)::_70_24763))
end
| _52_1522 -> begin
[]
end))
in (let _52_1561 = (match ((let _70_24765 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in _70_24765.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _52_1531; Microsoft_FStar_Absyn_Syntax.pos = _52_1529; Microsoft_FStar_Absyn_Syntax.fvs = _52_1527; Microsoft_FStar_Absyn_Syntax.uvs = _52_1525})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _52_1550)::(Support.Microsoft.FStar.Util.Inl (post), _52_1545)::(Support.Microsoft.FStar.Util.Inr (pats), _52_1540)::[] -> begin
(let _70_24766 = (lemma_pats pats)
in (binders, pre, post, _70_24766))
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
(let _52_1584 = (let _70_24768 = (Support.All.pipe_right patterns (Support.List.map (fun ( _52_12 ) -> (match (_52_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1573) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1578) -> begin
(encode_exp e (let _52_1580 = env
in {bindings = _52_1580.bindings; depth = _52_1580.depth; tcenv = _52_1580.tcenv; warn = _52_1580.warn; cache = _52_1580.cache; nolabels = _52_1580.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1580.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _70_24768 Support.List.unzip))
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
(let _70_24770 = (let _70_24769 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _70_24769 e))
in (_70_24770)::pats)
end
| _52_1592 -> begin
(let rec aux = (fun ( tl ) ( vars ) -> (match (vars) with
| [] -> begin
(let _70_24775 = (Microsoft_FStar_ToSMT_Term.mk_Precedes tl e)
in (_70_24775)::pats)
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _70_24777 = (let _70_24776 = (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.mk_LexCons _70_24776 tl))
in (aux _70_24777 vars))
end
| _52_1603 -> begin
pats
end))
in (let _70_24778 = (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort))
in (aux _70_24778 vars)))
end)
end)
in (let env = (let _52_1605 = env
in {bindings = _52_1605.bindings; depth = _52_1605.depth; tcenv = _52_1605.tcenv; warn = _52_1605.warn; cache = _52_1605.cache; nolabels = true; use_zfuel_name = _52_1605.use_zfuel_name; encode_non_total_function_typ = _52_1605.encode_non_total_function_typ})
in (let _52_1610 = (let _70_24779 = (Microsoft_FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _70_24779 env))
in (match (_52_1610) with
| (pre, decls'') -> begin
(let _52_1613 = (let _70_24780 = (Microsoft_FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _70_24780 env))
in (match (_52_1613) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in (let _70_24785 = (let _70_24784 = (let _70_24783 = (let _70_24782 = (let _70_24781 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_70_24781, post))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_24782))
in (pats, vars, _70_24783))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24784))
in (_70_24785, decls)))
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
(let _70_24803 = (f args)
in (_70_24803, [], decls))
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
(let _70_24819 = (f phis)
in (_70_24819, labs, decls))
end))))
in (let const_op = (fun ( f ) ( _52_1657 ) -> (f, [], []))
in (let un_op = (fun ( f ) ( l ) -> (let _70_24833 = (Support.List.hd l)
in (Support.All.pipe_left f _70_24833)))
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
(let _70_24847 = (Microsoft_FStar_ToSMT_Term.mkImp (l2, l1))
in (_70_24847, (Support.List.append labs1 labs2), (Support.List.append decls1 decls2)))
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
in (let unboxInt_l = (fun ( f ) ( l ) -> (let _70_24859 = (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)
in (f _70_24859)))
in (let connectives = (let _70_24920 = (let _70_24868 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))
in (Microsoft_FStar_Absyn_Const.and_lid, _70_24868))
in (let _70_24919 = (let _70_24918 = (let _70_24874 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))
in (Microsoft_FStar_Absyn_Const.or_lid, _70_24874))
in (let _70_24917 = (let _70_24916 = (let _70_24915 = (let _70_24883 = (Support.All.pipe_left enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))
in (Microsoft_FStar_Absyn_Const.iff_lid, _70_24883))
in (let _70_24914 = (let _70_24913 = (let _70_24912 = (let _70_24892 = (Support.All.pipe_left enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))
in (Microsoft_FStar_Absyn_Const.not_lid, _70_24892))
in (let _70_24911 = (let _70_24910 = (let _70_24898 = (Support.All.pipe_left enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))
in (Microsoft_FStar_Absyn_Const.eqT_lid, _70_24898))
in (_70_24910)::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[])
in (_70_24912)::_70_24911))
in ((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::_70_24913)
in (_70_24915)::_70_24914))
in ((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::_70_24916)
in (_70_24918)::_70_24917))
in (_70_24920)::_70_24919))
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
(let lvar = (let _70_24923 = (varops.fresh "label")
in (_70_24923, Microsoft_FStar_ToSMT_Term.Bool_sort))
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
(let _70_24924 = (Microsoft_FStar_ToSMT_Term.mk_Valid tt)
in (_70_24924, [], decls))
end))
end))
in (let encode_q_body = (fun ( env ) ( bs ) ( ps ) ( body ) -> (let _52_1811 = (encode_binders None bs env)
in (match (_52_1811) with
| (vars, guards, env, decls, _52_1810) -> begin
(let _52_1827 = (let _70_24934 = (Support.All.pipe_right ps (Support.List.map (fun ( _52_17 ) -> (match (_52_17) with
| (Support.Microsoft.FStar.Util.Inl (t), _52_1816) -> begin
(encode_typ_term t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _52_1821) -> begin
(encode_exp e (let _52_1823 = env
in {bindings = _52_1823.bindings; depth = _52_1823.depth; tcenv = _52_1823.tcenv; warn = _52_1823.warn; cache = _52_1823.cache; nolabels = _52_1823.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _52_1823.encode_non_total_function_typ}))
end))))
in (Support.All.pipe_right _70_24934 Support.List.unzip))
in (match (_52_1827) with
| (pats, decls') -> begin
(let _52_1831 = (encode_formula_with_labels body env)
in (match (_52_1831) with
| (body, labs, decls'') -> begin
(let _70_24935 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _70_24935, body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'')))
end))
end))
end)))
in (let _52_1832 = (match ((Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_24936 = (Microsoft_FStar_Absyn_Print.formula_to_string phi)
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" _70_24936))
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
(let _70_24953 = (Support.All.pipe_right vars (Microsoft_FStar_Absyn_Print.binders_to_string "; "))
in (Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" _70_24953))
end
| false -> begin
()
end)
in (let _52_1865 = (encode_q_body env vars pats body)
in (match (_52_1865) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _70_24956 = (let _70_24955 = (let _70_24954 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _70_24954))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_24955))
in (_70_24956, labs, decls))
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _52_1878 = (encode_q_body env vars pats body)
in (match (_52_1878) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _70_24959 = (let _70_24958 = (let _70_24957 = (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _70_24957))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_24958))
in (_70_24959, labs, decls))
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
in (let quant = (fun ( vars ) ( body ) -> (fun ( x ) -> (let t1 = (let _70_25002 = (let _70_25001 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (x, _70_25001))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25002))
in (let vname_decl = (let _70_25004 = (let _70_25003 = (Support.All.pipe_right vars (Support.List.map Support.Prims.snd))
in (x, _70_25003, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_25004))
in (let _70_25010 = (let _70_25009 = (let _70_25008 = (let _70_25007 = (let _70_25006 = (let _70_25005 = (Microsoft_FStar_ToSMT_Term.mkEq (t1, body))
in ((t1)::[], vars, _70_25005))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25006))
in (_70_25007, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25008))
in (_70_25009)::[])
in (vname_decl)::_70_25010)))))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _70_25170 = (let _70_25019 = (let _70_25018 = (let _70_25017 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25017))
in (quant axy _70_25018))
in (Microsoft_FStar_Absyn_Const.op_Eq, _70_25019))
in (let _70_25169 = (let _70_25168 = (let _70_25026 = (let _70_25025 = (let _70_25024 = (let _70_25023 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (Microsoft_FStar_ToSMT_Term.mkNot _70_25023))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25024))
in (quant axy _70_25025))
in (Microsoft_FStar_Absyn_Const.op_notEq, _70_25026))
in (let _70_25167 = (let _70_25166 = (let _70_25035 = (let _70_25034 = (let _70_25033 = (let _70_25032 = (let _70_25031 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25030 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25031, _70_25030)))
in (Microsoft_FStar_ToSMT_Term.mkLT _70_25032))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25033))
in (quant xy _70_25034))
in (Microsoft_FStar_Absyn_Const.op_LT, _70_25035))
in (let _70_25165 = (let _70_25164 = (let _70_25044 = (let _70_25043 = (let _70_25042 = (let _70_25041 = (let _70_25040 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25039 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25040, _70_25039)))
in (Microsoft_FStar_ToSMT_Term.mkLTE _70_25041))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25042))
in (quant xy _70_25043))
in (Microsoft_FStar_Absyn_Const.op_LTE, _70_25044))
in (let _70_25163 = (let _70_25162 = (let _70_25053 = (let _70_25052 = (let _70_25051 = (let _70_25050 = (let _70_25049 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25048 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25049, _70_25048)))
in (Microsoft_FStar_ToSMT_Term.mkGT _70_25050))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25051))
in (quant xy _70_25052))
in (Microsoft_FStar_Absyn_Const.op_GT, _70_25053))
in (let _70_25161 = (let _70_25160 = (let _70_25062 = (let _70_25061 = (let _70_25060 = (let _70_25059 = (let _70_25058 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25057 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25058, _70_25057)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _70_25059))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25060))
in (quant xy _70_25061))
in (Microsoft_FStar_Absyn_Const.op_GTE, _70_25062))
in (let _70_25159 = (let _70_25158 = (let _70_25071 = (let _70_25070 = (let _70_25069 = (let _70_25068 = (let _70_25067 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25066 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25067, _70_25066)))
in (Microsoft_FStar_ToSMT_Term.mkSub _70_25068))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25069))
in (quant xy _70_25070))
in (Microsoft_FStar_Absyn_Const.op_Subtraction, _70_25071))
in (let _70_25157 = (let _70_25156 = (let _70_25078 = (let _70_25077 = (let _70_25076 = (let _70_25075 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (Microsoft_FStar_ToSMT_Term.mkMinus _70_25075))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25076))
in (quant qx _70_25077))
in (Microsoft_FStar_Absyn_Const.op_Minus, _70_25078))
in (let _70_25155 = (let _70_25154 = (let _70_25087 = (let _70_25086 = (let _70_25085 = (let _70_25084 = (let _70_25083 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25082 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25083, _70_25082)))
in (Microsoft_FStar_ToSMT_Term.mkAdd _70_25084))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25085))
in (quant xy _70_25086))
in (Microsoft_FStar_Absyn_Const.op_Addition, _70_25087))
in (let _70_25153 = (let _70_25152 = (let _70_25096 = (let _70_25095 = (let _70_25094 = (let _70_25093 = (let _70_25092 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25091 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25092, _70_25091)))
in (Microsoft_FStar_ToSMT_Term.mkMul _70_25093))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25094))
in (quant xy _70_25095))
in (Microsoft_FStar_Absyn_Const.op_Multiply, _70_25096))
in (let _70_25151 = (let _70_25150 = (let _70_25105 = (let _70_25104 = (let _70_25103 = (let _70_25102 = (let _70_25101 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25100 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25101, _70_25100)))
in (Microsoft_FStar_ToSMT_Term.mkDiv _70_25102))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25103))
in (quant xy _70_25104))
in (Microsoft_FStar_Absyn_Const.op_Division, _70_25105))
in (let _70_25149 = (let _70_25148 = (let _70_25114 = (let _70_25113 = (let _70_25112 = (let _70_25111 = (let _70_25110 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25109 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (_70_25110, _70_25109)))
in (Microsoft_FStar_ToSMT_Term.mkMod _70_25111))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxInt _70_25112))
in (quant xy _70_25113))
in (Microsoft_FStar_Absyn_Const.op_Modulus, _70_25114))
in (let _70_25147 = (let _70_25146 = (let _70_25123 = (let _70_25122 = (let _70_25121 = (let _70_25120 = (let _70_25119 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _70_25118 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_70_25119, _70_25118)))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_25120))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25121))
in (quant xy _70_25122))
in (Microsoft_FStar_Absyn_Const.op_And, _70_25123))
in (let _70_25145 = (let _70_25144 = (let _70_25132 = (let _70_25131 = (let _70_25130 = (let _70_25129 = (let _70_25128 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (let _70_25127 = (Microsoft_FStar_ToSMT_Term.unboxBool y)
in (_70_25128, _70_25127)))
in (Microsoft_FStar_ToSMT_Term.mkOr _70_25129))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25130))
in (quant xy _70_25131))
in (Microsoft_FStar_Absyn_Const.op_Or, _70_25132))
in (let _70_25143 = (let _70_25142 = (let _70_25139 = (let _70_25138 = (let _70_25137 = (let _70_25136 = (Microsoft_FStar_ToSMT_Term.unboxBool x)
in (Microsoft_FStar_ToSMT_Term.mkNot _70_25136))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_25137))
in (quant qx _70_25138))
in (Microsoft_FStar_Absyn_Const.op_Negation, _70_25139))
in (_70_25142)::[])
in (_70_25144)::_70_25143))
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
in (let mk = (fun ( l ) ( v ) -> (let _70_25202 = (Support.All.pipe_right prims (Support.List.filter (fun ( _52_1910 ) -> (match (_52_1910) with
| (l', _52_1909) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))))
in (Support.All.pipe_right _70_25202 (Support.List.collect (fun ( _52_1914 ) -> (match (_52_1914) with
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
in (let _70_25234 = (let _70_25225 = (let _70_25224 = (Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt)
in (_70_25224, Some ("unit typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25225))
in (let _70_25233 = (let _70_25232 = (let _70_25231 = (let _70_25230 = (let _70_25229 = (let _70_25228 = (let _70_25227 = (let _70_25226 = (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _70_25226))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25227))
in ((typing_pred)::[], (xx)::[], _70_25228))
in (mkForall_fuel _70_25229))
in (_70_25230, Some ("unit inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25231))
in (_70_25232)::[])
in (_70_25234)::_70_25233))))
in (let mk_bool = (fun ( _52_1931 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _70_25254 = (let _70_25244 = (let _70_25243 = (let _70_25242 = (let _70_25241 = (let _70_25240 = (let _70_25239 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _70_25239))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25240))
in ((typing_pred)::[], (xx)::[], _70_25241))
in (mkForall_fuel _70_25242))
in (_70_25243, Some ("bool inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25244))
in (let _70_25253 = (let _70_25252 = (let _70_25251 = (let _70_25250 = (let _70_25249 = (let _70_25248 = (let _70_25245 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (_70_25245)::[])
in (let _70_25247 = (let _70_25246 = (Microsoft_FStar_ToSMT_Term.boxBool b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_25246 tt))
in (_70_25248, (bb)::[], _70_25247)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25249))
in (_70_25250, Some ("bool typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25251))
in (_70_25252)::[])
in (_70_25254)::_70_25253))))))
in (let mk_int = (fun ( _52_1938 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _70_25266 = (let _70_25265 = (let _70_25264 = (let _70_25263 = (let _70_25262 = (let _70_25261 = (Microsoft_FStar_ToSMT_Term.boxInt a)
in (let _70_25260 = (let _70_25259 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_70_25259)::[])
in (_70_25261)::_70_25260))
in (tt)::_70_25262)
in (tt)::_70_25263)
in ("Prims.Precedes", _70_25264))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25265))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _70_25266))
in (let precedes_y_x = (let _70_25267 = (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.mk_Valid _70_25267))
in (let _70_25308 = (let _70_25273 = (let _70_25272 = (let _70_25271 = (let _70_25270 = (let _70_25269 = (let _70_25268 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _70_25268))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25269))
in ((typing_pred)::[], (xx)::[], _70_25270))
in (mkForall_fuel _70_25271))
in (_70_25272, Some ("int inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25273))
in (let _70_25307 = (let _70_25306 = (let _70_25280 = (let _70_25279 = (let _70_25278 = (let _70_25277 = (let _70_25274 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (_70_25274)::[])
in (let _70_25276 = (let _70_25275 = (Microsoft_FStar_ToSMT_Term.boxInt b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_25275 tt))
in (_70_25277, (bb)::[], _70_25276)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25278))
in (_70_25279, Some ("int typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25280))
in (let _70_25305 = (let _70_25304 = (let _70_25303 = (let _70_25302 = (let _70_25301 = (let _70_25300 = (let _70_25299 = (let _70_25298 = (let _70_25297 = (let _70_25296 = (let _70_25295 = (let _70_25294 = (let _70_25283 = (let _70_25282 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (let _70_25281 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_70_25282, _70_25281)))
in (Microsoft_FStar_ToSMT_Term.mkGT _70_25283))
in (let _70_25293 = (let _70_25292 = (let _70_25286 = (let _70_25285 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _70_25284 = (Microsoft_FStar_ToSMT_Term.mkInteger' 0)
in (_70_25285, _70_25284)))
in (Microsoft_FStar_ToSMT_Term.mkGTE _70_25286))
in (let _70_25291 = (let _70_25290 = (let _70_25289 = (let _70_25288 = (Microsoft_FStar_ToSMT_Term.unboxInt y)
in (let _70_25287 = (Microsoft_FStar_ToSMT_Term.unboxInt x)
in (_70_25288, _70_25287)))
in (Microsoft_FStar_ToSMT_Term.mkLT _70_25289))
in (_70_25290)::[])
in (_70_25292)::_70_25291))
in (_70_25294)::_70_25293))
in (typing_pred_y)::_70_25295)
in (typing_pred)::_70_25296)
in (Microsoft_FStar_ToSMT_Term.mk_and_l _70_25297))
in (_70_25298, precedes_y_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25299))
in ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], _70_25300))
in (mkForall_fuel _70_25301))
in (_70_25302, Some ("well-founded ordering on nat (alt)")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25303))
in (_70_25304)::[])
in (_70_25306)::_70_25305))
in (_70_25308)::_70_25307)))))))))))
in (let mk_int_alias = (fun ( _52_1950 ) ( tt ) -> (let _70_25317 = (let _70_25316 = (let _70_25315 = (let _70_25314 = (let _70_25313 = (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, []))
in (tt, _70_25313))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25314))
in (_70_25315, Some ("mapping to int; for now")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25316))
in (_70_25317)::[]))
in (let mk_str = (fun ( _52_1954 ) ( tt ) -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let _70_25337 = (let _70_25327 = (let _70_25326 = (let _70_25325 = (let _70_25324 = (let _70_25323 = (let _70_25322 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _70_25322))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25323))
in ((typing_pred)::[], (xx)::[], _70_25324))
in (mkForall_fuel _70_25325))
in (_70_25326, Some ("string inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25327))
in (let _70_25336 = (let _70_25335 = (let _70_25334 = (let _70_25333 = (let _70_25332 = (let _70_25331 = (let _70_25328 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (_70_25328)::[])
in (let _70_25330 = (let _70_25329 = (Microsoft_FStar_ToSMT_Term.boxString b)
in (Microsoft_FStar_ToSMT_Term.mk_HasType _70_25329 tt))
in (_70_25331, (bb)::[], _70_25330)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25332))
in (_70_25333, Some ("string typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25334))
in (_70_25335)::[])
in (_70_25337)::_70_25336))))))
in (let mk_ref = (fun ( reft_name ) ( _52_1962 ) -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (let _70_25344 = (let _70_25343 = (let _70_25342 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (_70_25342)::[])
in (reft_name, _70_25343))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25344))
in (let refb = (let _70_25347 = (let _70_25346 = (let _70_25345 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_70_25345)::[])
in (reft_name, _70_25346))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25347))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (let _70_25366 = (let _70_25353 = (let _70_25352 = (let _70_25351 = (let _70_25350 = (let _70_25349 = (let _70_25348 = (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _70_25348))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25349))
in ((typing_pred)::[], (xx)::(aa)::[], _70_25350))
in (mkForall_fuel _70_25351))
in (_70_25352, Some ("ref inversion")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25353))
in (let _70_25365 = (let _70_25364 = (let _70_25363 = (let _70_25362 = (let _70_25361 = (let _70_25360 = (let _70_25359 = (let _70_25358 = (Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _70_25357 = (let _70_25356 = (let _70_25355 = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let _70_25354 = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (_70_25355, _70_25354)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25356))
in (_70_25358, _70_25357)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25359))
in ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], _70_25360))
in (mkForall_fuel' 2 _70_25361))
in (_70_25362, Some ("ref typing is injective")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25363))
in (_70_25364)::[])
in (_70_25366)::_70_25365))))))))))
in (let mk_false_interp = (fun ( _52_1972 ) ( false_tm ) -> (let valid = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _70_25373 = (let _70_25372 = (let _70_25371 = (Microsoft_FStar_ToSMT_Term.mkIff (Microsoft_FStar_ToSMT_Term.mkFalse, valid))
in (_70_25371, Some ("False interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25372))
in (_70_25373)::[])))
in (let mk_and_interp = (fun ( conj ) ( _52_1978 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25380 = (let _70_25379 = (let _70_25378 = (Microsoft_FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_70_25378)::[])
in ("Valid", _70_25379))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25380))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_25387 = (let _70_25386 = (let _70_25385 = (let _70_25384 = (let _70_25383 = (let _70_25382 = (let _70_25381 = (Microsoft_FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_70_25381, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25382))
in ((valid)::[], (aa)::(bb)::[], _70_25383))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25384))
in (_70_25385, Some ("/\\ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25386))
in (_70_25387)::[])))))))))
in (let mk_or_interp = (fun ( disj ) ( _52_1989 ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25394 = (let _70_25393 = (let _70_25392 = (Microsoft_FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_70_25392)::[])
in ("Valid", _70_25393))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25394))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_25401 = (let _70_25400 = (let _70_25399 = (let _70_25398 = (let _70_25397 = (let _70_25396 = (let _70_25395 = (Microsoft_FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_70_25395, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25396))
in ((valid)::[], (aa)::(bb)::[], _70_25397))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25398))
in (_70_25399, Some ("\\/ interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25400))
in (_70_25401)::[])))))))))
in (let mk_eq2_interp = (fun ( eq2 ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _70_25408 = (let _70_25407 = (let _70_25406 = (Microsoft_FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_70_25406)::[])
in ("Valid", _70_25407))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25408))
in (let _70_25415 = (let _70_25414 = (let _70_25413 = (let _70_25412 = (let _70_25411 = (let _70_25410 = (let _70_25409 = (Microsoft_FStar_ToSMT_Term.mkEq (x, y))
in (_70_25409, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25410))
in ((valid)::[], (aa)::(bb)::(xx)::(yy)::[], _70_25411))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25412))
in (_70_25413, Some ("Eq2 interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25414))
in (_70_25415)::[])))))))))))
in (let mk_imp_interp = (fun ( imp ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25422 = (let _70_25421 = (let _70_25420 = (Microsoft_FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_70_25420)::[])
in ("Valid", _70_25421))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25422))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_25429 = (let _70_25428 = (let _70_25427 = (let _70_25426 = (let _70_25425 = (let _70_25424 = (let _70_25423 = (Microsoft_FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_70_25423, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25424))
in ((valid)::[], (aa)::(bb)::[], _70_25425))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25426))
in (_70_25427, Some ("==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25428))
in (_70_25429)::[])))))))))
in (let mk_iff_interp = (fun ( iff ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25436 = (let _70_25435 = (let _70_25434 = (Microsoft_FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_70_25434)::[])
in ("Valid", _70_25435))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25436))
in (let valid_a = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (Microsoft_FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _70_25443 = (let _70_25442 = (let _70_25441 = (let _70_25440 = (let _70_25439 = (let _70_25438 = (let _70_25437 = (Microsoft_FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_70_25437, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25438))
in ((valid)::[], (aa)::(bb)::[], _70_25439))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25440))
in (_70_25441, Some ("<==> interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25442))
in (_70_25443)::[])))))))))
in (let mk_forall_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _70_25450 = (let _70_25449 = (let _70_25448 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_70_25448)::[])
in ("Valid", _70_25449))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25450))
in (let valid_b_x = (let _70_25453 = (let _70_25452 = (let _70_25451 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_70_25451)::[])
in ("Valid", _70_25452))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25453))
in (let _70_25466 = (let _70_25465 = (let _70_25464 = (let _70_25463 = (let _70_25462 = (let _70_25461 = (let _70_25460 = (let _70_25459 = (let _70_25458 = (let _70_25454 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_25454)::[])
in (let _70_25457 = (let _70_25456 = (let _70_25455 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_25455, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25456))
in (_70_25458, (xx)::[], _70_25457)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25459))
in (_70_25460, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25461))
in ((valid)::[], (aa)::(bb)::[], _70_25462))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25463))
in (_70_25464, Some ("forall interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25465))
in (_70_25466)::[]))))))))))
in (let mk_exists_interp = (fun ( for_all ) ( tt ) -> (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _70_25473 = (let _70_25472 = (let _70_25471 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_70_25471)::[])
in ("Valid", _70_25472))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25473))
in (let valid_b_x = (let _70_25476 = (let _70_25475 = (let _70_25474 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE b x)
in (_70_25474)::[])
in ("Valid", _70_25475))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25476))
in (let _70_25489 = (let _70_25488 = (let _70_25487 = (let _70_25486 = (let _70_25485 = (let _70_25484 = (let _70_25483 = (let _70_25482 = (let _70_25481 = (let _70_25477 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_25477)::[])
in (let _70_25480 = (let _70_25479 = (let _70_25478 = (Microsoft_FStar_ToSMT_Term.mk_HasType x a)
in (_70_25478, valid_b_x))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25479))
in (_70_25481, (xx)::[], _70_25480)))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_25482))
in (_70_25483, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25484))
in ((valid)::[], (aa)::(bb)::[], _70_25485))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25486))
in (_70_25487, Some ("exists interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25488))
in (_70_25489)::[]))))))))))
in (let mk_foralltyp_interp = (fun ( for_all ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25496 = (let _70_25495 = (let _70_25494 = (Microsoft_FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_70_25494)::[])
in ("Valid", _70_25495))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25496))
in (let valid_a_b = (let _70_25499 = (let _70_25498 = (let _70_25497 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_70_25497)::[])
in ("Valid", _70_25498))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25499))
in (let _70_25512 = (let _70_25511 = (let _70_25510 = (let _70_25509 = (let _70_25508 = (let _70_25507 = (let _70_25506 = (let _70_25505 = (let _70_25504 = (let _70_25500 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_25500)::[])
in (let _70_25503 = (let _70_25502 = (let _70_25501 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_25501, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25502))
in (_70_25504, (bb)::[], _70_25503)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25505))
in (_70_25506, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25507))
in ((valid)::[], (kk)::(aa)::[], _70_25508))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25509))
in (_70_25510, Some ("ForallTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25511))
in (_70_25512)::[]))))))))))
in (let mk_existstyp_interp = (fun ( for_some ) ( tt ) -> (let kk = ("k", Microsoft_FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let k = (Microsoft_FStar_ToSMT_Term.mkFreeV kk)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _70_25519 = (let _70_25518 = (let _70_25517 = (Microsoft_FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_70_25517)::[])
in ("Valid", _70_25518))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25519))
in (let valid_a_b = (let _70_25522 = (let _70_25521 = (let _70_25520 = (Microsoft_FStar_ToSMT_Term.mk_ApplyTE a b)
in (_70_25520)::[])
in ("Valid", _70_25521))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25522))
in (let _70_25535 = (let _70_25534 = (let _70_25533 = (let _70_25532 = (let _70_25531 = (let _70_25530 = (let _70_25529 = (let _70_25528 = (let _70_25527 = (let _70_25523 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_25523)::[])
in (let _70_25526 = (let _70_25525 = (let _70_25524 = (Microsoft_FStar_ToSMT_Term.mk_HasKind b k)
in (_70_25524, valid_a_b))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25525))
in (_70_25527, (bb)::[], _70_25526)))
in (Microsoft_FStar_ToSMT_Term.mkExists _70_25528))
in (_70_25529, valid))
in (Microsoft_FStar_ToSMT_Term.mkIff _70_25530))
in ((valid)::[], (kk)::(aa)::[], _70_25531))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25532))
in (_70_25533, Some ("ExistsTyp interpretation")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25534))
in (_70_25535)::[]))))))))))
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
(let _70_25678 = (Microsoft_FStar_Absyn_Print.sigelt_to_string se)
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") _70_25678))
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
(let _70_25681 = (let _70_25680 = (let _70_25679 = (Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_25679))
in (_70_25680)::[])
in (_70_25681, e))
end
| _52_2102 -> begin
(let _70_25688 = (let _70_25687 = (let _70_25683 = (let _70_25682 = (Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_25682))
in (_70_25683)::g)
in (let _70_25686 = (let _70_25685 = (let _70_25684 = (Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)
in Microsoft_FStar_ToSMT_Term.Caption (_70_25684))
in (_70_25685)::[])
in (Support.List.append _70_25687 _70_25686)))
in (_70_25688, e))
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
in (let valid_b2t_x = (let _70_25693 = (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_Valid _70_25693))
in (let decls = (let _70_25701 = (let _70_25700 = (let _70_25699 = (let _70_25698 = (let _70_25697 = (let _70_25696 = (let _70_25695 = (let _70_25694 = (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _70_25694))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25695))
in ((valid_b2t_x)::[], (xx)::[], _70_25696))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25697))
in (_70_25698, Some ("b2t def")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25699))
in (_70_25700)::[])
in (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::_70_25701)
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
(let tok_app = (let _70_25702 = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _70_25702 vars))
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _70_25704 = (let _70_25703 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _70_25703))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25704))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _52_2190 -> begin
(let _70_25706 = (let _70_25705 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _70_25705))
in (_70_25706)::[])
end)
in (let decls = (let _70_25717 = (let _70_25710 = (let _70_25709 = (let _70_25708 = (let _70_25707 = (Support.List.map Support.Prims.snd vars)
in (tname, _70_25707, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_25708))
in (_70_25709)::(tok_decl)::[])
in (Support.List.append _70_25710 fresh_tok))
in (let _70_25716 = (let _70_25715 = (let _70_25714 = (let _70_25713 = (let _70_25712 = (let _70_25711 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app))
in ((tok_app)::[], vars, _70_25711))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25712))
in (_70_25713, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25714))
in (_70_25715)::[])
in (Support.List.append _70_25717 _70_25716)))
in (let t = (whnf env t)
in (let _52_2202 = (match ((Support.All.pipe_right tags (Support.Microsoft.FStar.Util.for_some (fun ( _52_18 ) -> (match (_52_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _52_2197 -> begin
false
end))))) with
| true -> begin
(let _70_25720 = (Microsoft_FStar_ToSMT_Term.mk_Valid app)
in (let _70_25719 = (encode_formula t env')
in (_70_25720, _70_25719)))
end
| false -> begin
(let _70_25721 = (encode_typ_term t env')
in (app, _70_25721))
end)
in (match (_52_2202) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _70_25728 = (let _70_25727 = (let _70_25726 = (let _70_25725 = (let _70_25724 = (let _70_25723 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_25722 = (Microsoft_FStar_ToSMT_Term.mkEq (def, body))
in (_70_25723, _70_25722)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25724))
in ((def)::[], vars, _70_25725))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25726))
in (_70_25727, Some ("abbrev. elimination")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25728))
in (let kindingAx = (let _52_2206 = (let _70_25729 = (Microsoft_FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _70_25729 env' app))
in (match (_52_2206) with
| (k, decls) -> begin
(let _70_25737 = (let _70_25736 = (let _70_25735 = (let _70_25734 = (let _70_25733 = (let _70_25732 = (let _70_25731 = (let _70_25730 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_25730, k))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25731))
in ((app)::[], vars, _70_25732))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25733))
in (_70_25734, Some ("abbrev. kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25735))
in (_70_25736)::[])
in (Support.List.append decls _70_25737))
end))
in (let g = (let _70_25738 = (primitive_type_axioms lid tname app)
in (Support.List.append (Support.List.append (Support.List.append (Support.List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _70_25738))
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
(let _70_25740 = (let _70_25739 = (encode_smt_lemma env lid t)
in (Support.List.append decls _70_25739))
in (_70_25740, env))
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
(let g = (let _70_25745 = (let _70_25744 = (let _70_25743 = (let _70_25742 = (let _70_25741 = (Microsoft_FStar_Absyn_Print.sli l)
in (Support.Microsoft.FStar.Util.format1 "Assumption: %s" _70_25741))
in Some (_70_25742))
in (f, _70_25743))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25744))
in (_70_25745)::[])
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
in (let _70_25747 = (let _70_25746 = (primitive_type_axioms t tname tsym)
in (decl)::_70_25746)
in (_70_25747, (push_free_tvar env t tname (Some (tsym))))))))
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
(let _70_25753 = (let _70_25752 = (let _70_25751 = (Support.All.pipe_right args (Support.List.map Support.Prims.snd))
in (name, _70_25751, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_25752))
in (_70_25753)::[])
end))
end
| false -> begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end))
in (let inversion_axioms = (fun ( tapp ) ( vars ) -> (match ((((Support.List.length datas) = 0) || (Support.All.pipe_right datas (Support.Microsoft.FStar.Util.for_some (fun ( l ) -> (let _70_25759 = (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)
in (Support.All.pipe_right _70_25759 Support.Option.isNone))))))) with
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
(let indices = (match ((let _70_25762 = (Microsoft_FStar_Absyn_Util.compress_typ res)
in _70_25762.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_52_2312, indices)) -> begin
indices
end
| _52_2317 -> begin
[]
end)
in (let env = (Support.All.pipe_right args (Support.List.fold_left (fun ( env ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_25767 = (let _70_25766 = (let _70_25765 = (mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v)
in (_70_25765, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25766))
in (push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v _70_25767))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_25770 = (let _70_25769 = (let _70_25768 = (mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v)
in (_70_25768, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25769))
in (push_term_var env x.Microsoft_FStar_Absyn_Syntax.v _70_25770))
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
in (let eqs = (let _70_25777 = (Support.List.map2 (fun ( v ) ( a ) -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _70_25774 = (let _70_25773 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_70_25773, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25774))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(let _70_25776 = (let _70_25775 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (_70_25775, a))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25776))
end)) vars indices)
in (Support.All.pipe_right _70_25777 Microsoft_FStar_ToSMT_Term.mk_and_l))
in (let _70_25782 = (let _70_25781 = (let _70_25780 = (let _70_25779 = (let _70_25778 = (mk_data_tester env l xx)
in (_70_25778, eqs))
in (Microsoft_FStar_ToSMT_Term.mkAnd _70_25779))
in (out, _70_25780))
in (Microsoft_FStar_ToSMT_Term.mkOr _70_25781))
in (_70_25782, (Support.List.append decls decls')))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])))
in (match (_52_2340) with
| (data_ax, decls) -> begin
(let _52_2343 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_52_2343) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _70_25783 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel _70_25783 xx tapp))
in (let _70_25790 = (let _70_25789 = (let _70_25788 = (let _70_25787 = (let _70_25786 = (let _70_25785 = (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars))
in (let _70_25784 = (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in ((xx_has_type)::[], _70_25785, _70_25784)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25786))
in (_70_25787, Some ("inversion axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25788))
in (_70_25789)::[])
in (Support.List.append decls _70_25790)))
end))
end))
end))
end))
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _52_2355 = (match ((let _70_25791 = (Microsoft_FStar_Absyn_Util.compress_kind k)
in _70_25791.Microsoft_FStar_Absyn_Syntax.n)) with
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
(let dproj_app = (let _70_25805 = (let _70_25804 = (let _70_25803 = (mk_typ_projector_name d a)
in (let _70_25802 = (let _70_25801 = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (_70_25801)::[])
in (_70_25803, _70_25802)))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25804))
in (mk_ApplyT _70_25805 suffix))
in (let _70_25810 = (let _70_25809 = (let _70_25808 = (let _70_25807 = (let _70_25806 = (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in ((tapp)::[], vars, _70_25806))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25807))
in (_70_25808, Some ("projector axiom")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25809))
in (_70_25810)::[]))
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
in (let _70_25823 = (let _70_25822 = (let _70_25821 = (let _70_25820 = (let _70_25819 = (let _70_25818 = (let _70_25817 = (let _70_25816 = (let _70_25815 = (Microsoft_FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _70_25815))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_25816))
in (xx_has_type, _70_25817))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25818))
in ((xx_has_type)::[], ((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars, _70_25819))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25820))
in (_70_25821, Some ("pretyping")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25822))
in (_70_25823)::[]))
end))
end)))
in (let _52_2418 = (new_typ_constant_and_tok_from_lid env t)
in (match (_52_2418) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _70_25825 = (let _70_25824 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (tname, _70_25824))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25825))
in (let _52_2443 = (let tname_decl = (let _70_25829 = (let _70_25828 = (Support.All.pipe_right vars (Support.List.map (fun ( _52_2424 ) -> (match (_52_2424) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))))
in (let _70_25827 = (varops.next_id ())
in (tname, _70_25828, Microsoft_FStar_ToSMT_Term.Type_sort, _70_25827)))
in (constructor_or_logic_type_decl _70_25829))
in (let _52_2440 = (match (vars) with
| [] -> begin
(let _70_25833 = (let _70_25832 = (let _70_25831 = (Microsoft_FStar_ToSMT_Term.mkApp (tname, []))
in (Support.All.pipe_left (fun ( _70_25830 ) -> Some (_70_25830)) _70_25831))
in (push_free_tvar env t tname _70_25832))
in ([], _70_25833))
end
| _52_2428 -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _70_25834 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) _70_25834))
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
in (let name_tok_corr = (let _70_25839 = (let _70_25838 = (let _70_25837 = (let _70_25836 = (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _70_25836))
in (Microsoft_FStar_ToSMT_Term.mkForall' _70_25837))
in (_70_25838, Some ("name-token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25839))
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
(let _70_25843 = (let _70_25842 = (let _70_25841 = (let _70_25840 = (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" _70_25840))
in (_70_25841, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25842))
in (_70_25843)::[])
end
| false -> begin
[]
end)
in (let _70_25849 = (let _70_25848 = (let _70_25847 = (let _70_25846 = (let _70_25845 = (let _70_25844 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, k))
in ((tapp)::[], vars, _70_25844))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25845))
in (_70_25846, Some ("kinding")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25847))
in (_70_25848)::[])
in (Support.List.append (Support.List.append decls karr) _70_25849)))
end))
in (let aux = (match (is_logical) with
| true -> begin
(let _70_25850 = (projection_axioms tapp vars)
in (Support.List.append kindingAx _70_25850))
end
| false -> begin
(let _70_25857 = (let _70_25855 = (let _70_25853 = (let _70_25851 = (primitive_type_axioms t tname tapp)
in (Support.List.append kindingAx _70_25851))
in (let _70_25852 = (inversion_axioms tapp vars)
in (Support.List.append _70_25853 _70_25852)))
in (let _70_25854 = (projection_axioms tapp vars)
in (Support.List.append _70_25855 _70_25854)))
in (let _70_25856 = (pretype_axioms tapp vars)
in (Support.List.append _70_25857 _70_25856)))
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
(let _70_25859 = (mk_typ_projector_name d a)
in (_70_25859, Microsoft_FStar_ToSMT_Term.Type_sort))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _70_25860 = (mk_term_projector_name d x)
in (_70_25860, Microsoft_FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _70_25862 = (let _70_25861 = (varops.next_id ())
in (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, _70_25861))
in (Support.All.pipe_right _70_25862 Microsoft_FStar_ToSMT_Term.constructor_to_decl))
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
(let _70_25864 = (let _70_25863 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) _70_25863))
in (_70_25864)::[])
end)
in (let encode_elim = (fun ( _52_2529 ) -> (match (()) with
| () -> begin
(let _52_2532 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_52_2532) with
| (head, args) -> begin
(match ((let _70_25867 = (Microsoft_FStar_Absyn_Util.compress_typ head)
in _70_25867.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _52_2538 = (encode_args args env')
in (match (_52_2538) with
| (encoded_args, arg_decls) -> begin
(let _52_2562 = (Support.List.fold_left (fun ( _52_2542 ) ( arg ) -> (match (_52_2542) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _52_2550 = (let _70_25870 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _70_25870))
in (match (_52_2550) with
| (_52_2547, tv, env) -> begin
(let _70_25872 = (let _70_25871 = (Microsoft_FStar_ToSMT_Term.mkEq (targ, tv))
in (_70_25871)::eqns)
in (env, (tv)::arg_vars, _70_25872))
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _52_2557 = (let _70_25873 = (Microsoft_FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _70_25873))
in (match (_52_2557) with
| (_52_2554, xv, env) -> begin
(let _70_25875 = (let _70_25874 = (Microsoft_FStar_ToSMT_Term.mkEq (varg, xv))
in (_70_25874)::eqns)
in (env, (xv)::arg_vars, _70_25875))
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
in (let typing_inversion = (let _70_25882 = (let _70_25881 = (let _70_25880 = (let _70_25879 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _70_25878 = (let _70_25877 = (let _70_25876 = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards))
in (ty_pred, _70_25876))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25877))
in ((ty_pred)::[], _70_25879, _70_25878)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25880))
in (_70_25881, Some ("data constructor typing elim")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25882))
in (let subterm_ordering = (match ((Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid)) with
| true -> begin
(let x = (let _70_25883 = (varops.fresh "x")
in (_70_25883, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in (let _70_25892 = (let _70_25891 = (let _70_25890 = (let _70_25889 = (let _70_25884 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_70_25884)::[])
in (let _70_25888 = (let _70_25887 = (let _70_25886 = (Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _70_25885 = (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_70_25886, _70_25885)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25887))
in (_70_25889, (x)::[], _70_25888)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25890))
in (_70_25891, Some ("lextop is top")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25892))))
end
| false -> begin
(let prec = (Support.All.pipe_right vars (Support.List.collect (fun ( v ) -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
(let _70_25895 = (let _70_25894 = (Microsoft_FStar_ToSMT_Term.mkFreeV v)
in (Microsoft_FStar_ToSMT_Term.mk_Precedes _70_25894 dapp))
in (_70_25895)::[])
end
| _52_2577 -> begin
(Support.All.failwith "unexpected sort")
end))))
in (let _70_25902 = (let _70_25901 = (let _70_25900 = (let _70_25899 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders))
in (let _70_25898 = (let _70_25897 = (let _70_25896 = (Microsoft_FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _70_25896))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25897))
in ((ty_pred)::[], _70_25899, _70_25898)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25900))
in (_70_25901, Some ("subterm ordering")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25902)))
end)
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _52_2581 -> begin
(let _52_2582 = (let _70_25905 = (let _70_25904 = (Microsoft_FStar_Absyn_Print.sli d)
in (let _70_25903 = (Microsoft_FStar_Absyn_Print.typ_to_string head)
in (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" _70_25904 _70_25903)))
in (Microsoft_FStar_Tc_Errors.warn drange _70_25905))
in ([], []))
end)
end))
end))
in (let _52_2586 = (encode_elim ())
in (match (_52_2586) with
| (decls2, elim) -> begin
(let g = (let _70_25930 = (let _70_25929 = (let _70_25914 = (let _70_25913 = (let _70_25912 = (let _70_25911 = (let _70_25910 = (let _70_25909 = (let _70_25908 = (let _70_25907 = (let _70_25906 = (Microsoft_FStar_Absyn_Print.sli d)
in (Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" _70_25906))
in Some (_70_25907))
in (ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, _70_25908))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_25909))
in (_70_25910)::[])
in (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) _70_25911))
in (Support.List.append _70_25912 proxy_fresh))
in (Support.List.append _70_25913 decls_formals))
in (Support.List.append _70_25914 decls_pred))
in (let _70_25928 = (let _70_25927 = (let _70_25926 = (let _70_25918 = (let _70_25917 = (let _70_25916 = (let _70_25915 = (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp))
in ((app)::[], vars, _70_25915))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25916))
in (_70_25917, Some ("equality for proxy")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25918))
in (let _70_25925 = (let _70_25924 = (let _70_25923 = (let _70_25922 = (let _70_25921 = (let _70_25920 = (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars')
in (let _70_25919 = (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in ((ty_pred')::[], _70_25920, _70_25919)))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25921))
in (_70_25922, Some ("data constructor typing intro")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25923))
in (_70_25924)::[])
in (_70_25926)::_70_25925))
in (Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_70_25927)
in (Support.List.append _70_25929 _70_25928)))
in (Support.List.append _70_25930 elim))
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
(let _70_25945 = (let _70_25944 = (Microsoft_FStar_Absyn_Util.btvar_to_typ b)
in (a.Microsoft_FStar_Absyn_Syntax.v, _70_25944))
in Support.Microsoft.FStar.Util.Inl (_70_25945))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
(let _70_25947 = (let _70_25946 = (Microsoft_FStar_Absyn_Util.bvar_to_exp y)
in (x.Microsoft_FStar_Absyn_Syntax.v, _70_25946))
in Support.Microsoft.FStar.Util.Inr (_70_25947))
end
| _52_2671 -> begin
(Support.All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _70_25948 = (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals)
in (Support.All.pipe_right _70_25948 Microsoft_FStar_Absyn_Util.name_binders))
in (let body = (let _70_25954 = (let _70_25950 = (let _70_25949 = (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals)
in (Support.All.pipe_left Support.Prims.snd _70_25949))
in (body, _70_25950))
in (let _70_25953 = (let _70_25952 = (Microsoft_FStar_Absyn_Util.subst_typ subst t)
in (Support.All.pipe_left (fun ( _70_25951 ) -> Some (_70_25951)) _70_25952))
in (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat _70_25954 _70_25953 body.Microsoft_FStar_Absyn_Syntax.pos)))
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
(let _70_25963 = (let _70_25962 = (Microsoft_FStar_Absyn_Print.exp_to_string e)
in (let _70_25961 = (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)
in (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str _70_25962 _70_25961)))
in (Support.All.failwith _70_25963))
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
(let _70_25969 = (Support.All.pipe_right bindings (Support.List.collect (fun ( lb ) -> (match ((Microsoft_FStar_Absyn_Util.is_smt_lemma lb.Microsoft_FStar_Absyn_Syntax.lbtyp)) with
| true -> begin
(let _70_25968 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (encode_smt_lemma env _70_25968 lb.Microsoft_FStar_Absyn_Syntax.lbtyp))
end
| false -> begin
(raise (Let_rec_unencodeable))
end))))
in (_70_25969, env))
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
in (let t_norm = (let _70_25972 = (whnf env lb.Microsoft_FStar_Absyn_Syntax.lbtyp)
in (Support.All.pipe_right _70_25972 Microsoft_FStar_Absyn_Util.compress_typ))
in (let _52_2760 = (let _70_25973 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _70_25973 lb.Microsoft_FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_52_2760) with
| (tok, decl, env) -> begin
(let _70_25976 = (let _70_25975 = (let _70_25974 = (Support.Microsoft.FStar.Util.right lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (_70_25974, tok))
in (_70_25975)::toks)
in (_70_25976, (t_norm)::typs, (decl)::decls, env))
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
end)))) || (Support.All.pipe_right typs (Support.Microsoft.FStar.Util.for_some (fun ( t ) -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (let _70_25979 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)
in (Support.All.pipe_left Support.Prims.op_Negation _70_25979)))))))) with
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
(let _70_25981 = (let _70_25980 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (f, _70_25980))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_25981))
end)
in (let _52_2810 = (encode_exp body env')
in (match (_52_2810) with
| (body, decls2) -> begin
(let eqn = (let _70_25990 = (let _70_25989 = (let _70_25986 = (let _70_25985 = (let _70_25984 = (let _70_25983 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_25982 = (Microsoft_FStar_ToSMT_Term.mkEq (app, body))
in (_70_25983, _70_25982)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_25984))
in ((app)::[], vars, _70_25985))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_25986))
in (let _70_25988 = (let _70_25987 = (Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_70_25987))
in (_70_25989, _70_25988)))
in Microsoft_FStar_ToSMT_Term.Assume (_70_25990))
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
(let fuel = (let _70_25991 = (varops.fresh "fuel")
in (_70_25991, Microsoft_FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _52_2830 = (Support.All.pipe_right toks (Support.List.fold_left (fun ( _52_2819 ) ( _52_2824 ) -> (match ((_52_2819, _52_2824)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _70_25996 = (let _70_25995 = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (Support.All.pipe_left (fun ( _70_25994 ) -> Some (_70_25994)) _70_25995))
in (push_free_var env flid gtok _70_25996))
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
(let decl_g = (let _70_26007 = (let _70_26006 = (let _70_26005 = (Support.List.map Support.Prims.snd vars)
in (Microsoft_FStar_ToSMT_Term.Fuel_sort)::_70_26005)
in (g, _70_26006, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_26007))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _70_26010 = (let _70_26009 = (let _70_26008 = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_70_26008)::vars_tm)
in (g, _70_26009))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26010))
in (let gmax = (let _70_26013 = (let _70_26012 = (let _70_26011 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_70_26011)::vars_tm)
in (g, _70_26012))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26013))
in (let _52_2870 = (encode_exp body env')
in (match (_52_2870) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _70_26022 = (let _70_26021 = (let _70_26018 = (let _70_26017 = (let _70_26016 = (let _70_26015 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let _70_26014 = (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_70_26015, _70_26014)))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_26016))
in ((gsapp)::[], (fuel)::vars, _70_26017))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26018))
in (let _70_26020 = (let _70_26019 = (Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str)
in Some (_70_26019))
in (_70_26021, _70_26020)))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26022))
in (let eqn_f = (let _70_26026 = (let _70_26025 = (let _70_26024 = (let _70_26023 = (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax))
in ((app)::[], vars, _70_26023))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26024))
in (_70_26025, Some ("Correspondence of recursive function to instrumented version")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26026))
in (let eqn_g' = (let _70_26035 = (let _70_26034 = (let _70_26033 = (let _70_26032 = (let _70_26031 = (let _70_26030 = (let _70_26029 = (let _70_26028 = (let _70_26027 = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (_70_26027)::vars_tm)
in (g, _70_26028))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26029))
in (gsapp, _70_26030))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26031))
in ((gsapp)::[], (fuel)::vars, _70_26032))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26033))
in (_70_26034, Some ("Fuel irrelevance")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26035))
in (let _52_2893 = (let _52_2880 = (encode_binders None formals env0)
in (match (_52_2880) with
| (vars, v_guards, env, binder_decls, _52_2879) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _70_26036 = (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _70_26036 ((fuel)::vars)))
in (let _70_26040 = (let _70_26039 = (let _70_26038 = (let _70_26037 = (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp))
in ((tok_app)::[], (fuel)::vars, _70_26037))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26038))
in (_70_26039, Some ("Fuel token correspondence")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26040)))
in (let _52_2890 = (let _52_2887 = (encode_typ_pred' None tres env gapp)
in (match (_52_2887) with
| (g_typing, d3) -> begin
(let _70_26048 = (let _70_26047 = (let _70_26046 = (let _70_26045 = (let _70_26044 = (let _70_26043 = (let _70_26042 = (let _70_26041 = (Microsoft_FStar_ToSMT_Term.mk_and_l v_guards)
in (_70_26041, g_typing))
in (Microsoft_FStar_ToSMT_Term.mkImp _70_26042))
in ((gapp)::[], (fuel)::vars, _70_26043))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26044))
in (_70_26045, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26046))
in (_70_26047)::[])
in (d3, _70_26048))
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
in (let _52_2909 = (let _70_26051 = (Support.List.zip3 gtoks typs bindings)
in (Support.List.fold_left (fun ( _52_2897 ) ( _52_2901 ) -> (match ((_52_2897, _52_2901)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _52_2905 = (encode_one_binding env0 gtok ty bs)
in (match (_52_2905) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _70_26051))
in (match (_52_2909) with
| (decls, eqns, env0) -> begin
(let _52_2918 = (let _70_26053 = (Support.All.pipe_right decls Support.List.flatten)
in (Support.All.pipe_right _70_26053 (Support.List.partition (fun ( _52_29 ) -> (match (_52_29) with
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
(let msg = (let _70_26056 = (Support.All.pipe_right bindings (Support.List.map (fun ( lb ) -> (Microsoft_FStar_Absyn_Print.lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname))))
in (Support.All.pipe_right _70_26056 (Support.String.concat " and ")))
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
and encode_free_var = (fun ( env ) ( lid ) ( tt ) ( t_norm ) ( quals ) -> (match (((let _70_26069 = (Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (Support.All.pipe_left Support.Prims.op_Negation _70_26069)) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm))) with
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
(let _70_26071 = (Microsoft_FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _70_26071))
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
in (let _70_26084 = (let _70_26083 = (let _70_26082 = (let _70_26081 = (let _70_26080 = (let _70_26079 = (let _70_26078 = (let _70_26077 = (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)
in (Support.All.pipe_left Microsoft_FStar_ToSMT_Term.boxBool _70_26077))
in (vapp, _70_26078))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26079))
in ((vapp)::[], vars, _70_26080))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26081))
in (_70_26082, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26083))
in (_70_26084)::[]))
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _52_3038 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_52_3038) with
| (_52_3033, (xxsym, _52_3036)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (let _70_26093 = (let _70_26092 = (let _70_26091 = (let _70_26090 = (let _70_26089 = (let _70_26088 = (let _70_26087 = (let _70_26086 = (let _70_26085 = (mk_term_projector_name d f)
in (_70_26085, (xx)::[]))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26086))
in (vapp, _70_26087))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26088))
in ((vapp)::[], vars, _70_26089))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26090))
in (_70_26091, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26092))
in (_70_26093)::[]))
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
(let _70_26094 = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (_70_26094, decls1))
end
| Some (p) -> begin
(let _52_3054 = (encode_formula p env')
in (match (_52_3054) with
| (g, ds) -> begin
(let _70_26095 = (Microsoft_FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_70_26095, (Support.List.append decls1 ds)))
end))
end)
in (match (_52_3057) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _70_26097 = (let _70_26096 = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (vname, _70_26096))
in (Microsoft_FStar_ToSMT_Term.mkApp _70_26097))
in (let _52_3088 = (let vname_decl = (let _70_26100 = (let _70_26099 = (Support.All.pipe_right formals (Support.List.map (fun ( _52_32 ) -> (match (_52_32) with
| (Support.Microsoft.FStar.Util.Inl (_52_3062), _52_3065) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _52_3068 -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))))
in (vname, _70_26099, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_26100))
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
(let _70_26104 = (let _70_26103 = (let _70_26102 = (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Support.All.pipe_left (fun ( _70_26101 ) -> Some (_70_26101)) _70_26102))
in (push_free_var env lid vname _70_26103))
in ((Support.List.append decls2 ((tok_typing)::[])), _70_26104))
end
| _52_3079 -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _70_26105 = (varops.next_id ())
in (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) _70_26105))
in (let name_tok_corr = (let _70_26109 = (let _70_26108 = (let _70_26107 = (let _70_26106 = (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in ((vtok_app)::[], vars, _70_26106))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26107))
in (_70_26108, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26109))
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
(let typingAx = (let _70_26113 = (let _70_26112 = (let _70_26111 = (let _70_26110 = (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred))
in ((vapp)::[], vars, _70_26110))
in (Microsoft_FStar_ToSMT_Term.mkForall _70_26111))
in (_70_26112, Some ("free var typing")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26113))
in (let g = (let _70_26115 = (let _70_26114 = (mk_disc_proj_axioms vapp vars)
in (typingAx)::_70_26114)
in (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) _70_26115))
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
(let t1 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _52_3121 = (encode_typ_pred' None t1 env xx)
in (match (_52_3121) with
| (t, decls') -> begin
(let caption = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_26131 = (let _70_26130 = (Microsoft_FStar_Absyn_Print.strBvd x)
in (let _70_26129 = (Microsoft_FStar_Absyn_Print.typ_to_string t0)
in (let _70_26128 = (Microsoft_FStar_Absyn_Print.typ_to_string t1)
in (Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" _70_26130 _70_26129 _70_26128))))
in Some (_70_26131))
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
(let _52_3131 = (new_typ_constant env a)
in (match (_52_3131) with
| (aasym, aa, env') -> begin
(let _52_3134 = (encode_knd k env aa)
in (match (_52_3134) with
| (k, decls') -> begin
(let g = (let _70_26137 = (let _70_26136 = (let _70_26135 = (let _70_26134 = (let _70_26133 = (let _70_26132 = (Microsoft_FStar_Absyn_Print.strBvd a)
in Some (_70_26132))
in (aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, _70_26133))
in Microsoft_FStar_ToSMT_Term.DeclFun (_70_26134))
in (_70_26135)::[])
in (Support.List.append _70_26136 decls'))
in (Support.List.append _70_26137 ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((Support.List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((x, t)) -> begin
(let t_norm = (whnf env t)
in (let _52_3143 = (encode_free_var env x t t_norm [])
in (match (_52_3143) with
| (g, env') -> begin
((Support.List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _52_3148 = (encode_sigelt env se)
in (match (_52_3148) with
| (g, env') -> begin
((Support.List.append decls g), env')
end))
end)
end))
in (Support.List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun ( labs ) -> (let prefix = (Support.All.pipe_right labs (Support.List.map (fun ( _52_3155 ) -> (match (_52_3155) with
| (l, _52_3152, _52_3154) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Support.Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (Support.All.pipe_right labs (Support.List.collect (fun ( _52_3162 ) -> (match (_52_3162) with
| (l, _52_3159, _52_3161) -> begin
(let _70_26145 = (Support.All.pipe_left (fun ( _70_26141 ) -> Microsoft_FStar_ToSMT_Term.Echo (_70_26141)) (Support.Prims.fst l))
in (let _70_26144 = (let _70_26143 = (let _70_26142 = (Microsoft_FStar_ToSMT_Term.mkFreeV l)
in Microsoft_FStar_ToSMT_Term.Eval (_70_26142))
in (_70_26143)::[])
in (_70_26145)::_70_26144))
end))))
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun ( tcenv ) -> (let _70_26150 = (let _70_26149 = (let _70_26148 = (Support.Microsoft.FStar.Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _70_26148; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_70_26149)::[])
in (Support.ST.op_Colon_Equals last_env _70_26150)))

let get_env = (fun ( tcenv ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "No env; call init first!")
end
| e::_52_3168 -> begin
(let _52_3171 = e
in {bindings = _52_3171.bindings; depth = _52_3171.depth; tcenv = tcenv; warn = _52_3171.warn; cache = _52_3171.cache; nolabels = _52_3171.nolabels; use_zfuel_name = _52_3171.use_zfuel_name; encode_non_total_function_typ = _52_3171.encode_non_total_function_typ})
end))

let set_env = (fun ( env ) -> (match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Empty env stack")
end
| _52_3177::tl -> begin
(Support.ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env = (fun ( _52_3179 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Empty env stack")
end
| hd::tl -> begin
(let _52_3184 = (Microsoft_FStar_ToSMT_Term.push ())
in (let refs = (Support.Microsoft.FStar.Util.smap_copy hd.cache)
in (let top = (let _52_3187 = hd
in {bindings = _52_3187.bindings; depth = _52_3187.depth; tcenv = _52_3187.tcenv; warn = _52_3187.warn; cache = refs; nolabels = _52_3187.nolabels; use_zfuel_name = _52_3187.use_zfuel_name; encode_non_total_function_typ = _52_3187.encode_non_total_function_typ})
in (Support.ST.op_Colon_Equals last_env ((top)::(hd)::tl)))))
end)
end))

let pop_env = (fun ( _52_3190 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read last_env)) with
| [] -> begin
(Support.All.failwith "Popping an empty stack")
end
| _52_3194::tl -> begin
(let _52_3196 = (Microsoft_FStar_ToSMT_Term.pop ())
in (Support.ST.op_Colon_Equals last_env tl))
end)
end))

let mark_env = (fun ( _52_3198 ) -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun ( _52_3199 ) -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun ( _52_3200 ) -> (match (()) with
| () -> begin
(let _52_3201 = (Microsoft_FStar_ToSMT_Term.commit_mark ())
in (match ((Support.ST.read last_env)) with
| hd::_52_3205::tl -> begin
(Support.ST.op_Colon_Equals last_env ((hd)::tl))
end
| _52_3210 -> begin
(Support.All.failwith "Impossible")
end))
end))

let init = (fun ( tcenv ) -> (let _52_3212 = (init_env tcenv)
in (let _52_3214 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun ( msg ) -> (let _52_3217 = (push_env ())
in (let _52_3219 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun ( msg ) -> (let _52_3222 = (let _70_26171 = (pop_env ())
in (Support.All.pipe_left Support.Prims.ignore _70_26171))
in (let _52_3224 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun ( msg ) -> (let _52_3227 = (mark_env ())
in (let _52_3229 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun ( msg ) -> (let _52_3232 = (reset_mark_env ())
in (let _52_3234 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun ( msg ) -> (let _52_3237 = (commit_mark_env ())
in (let _52_3239 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun ( tcenv ) ( se ) -> (let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let _70_26185 = (let _70_26184 = (let _70_26183 = (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se)
in (Support.String.strcat "encoding sigelt " _70_26183))
in Microsoft_FStar_ToSMT_Term.Caption (_70_26184))
in (_70_26185)::decls)
end
| false -> begin
decls
end))
in (let env = (get_env tcenv)
in (let _52_3248 = (encode_sigelt env se)
in (match (_52_3248) with
| (decls, env) -> begin
(let _52_3249 = (set_env env)
in (let _70_26186 = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 _70_26186)))
end)))))

let encode_modul = (fun ( tcenv ) ( modul ) -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (match (modul.Microsoft_FStar_Absyn_Syntax.is_interface) with
| true -> begin
"interface"
end
| false -> begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _52_3254 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_26191 = (Support.All.pipe_right (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports) Support.Microsoft.FStar.Util.string_of_int)
in (Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name _70_26191))
end
| false -> begin
()
end)
in (let env = (get_env tcenv)
in (let _52_3261 = (encode_signature (let _52_3257 = env
in {bindings = _52_3257.bindings; depth = _52_3257.depth; tcenv = _52_3257.tcenv; warn = false; cache = _52_3257.cache; nolabels = _52_3257.nolabels; use_zfuel_name = _52_3257.use_zfuel_name; encode_non_total_function_typ = _52_3257.encode_non_total_function_typ}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_52_3261) with
| (decls, env) -> begin
(let caption = (fun ( decls ) -> (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(let msg = (Support.String.strcat "Externals for " name)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "End " msg)))::[])))
end
| false -> begin
decls
end))
in (let _52_3267 = (set_env (let _52_3265 = env
in {bindings = _52_3265.bindings; depth = _52_3265.depth; tcenv = _52_3265.tcenv; warn = true; cache = _52_3265.cache; nolabels = _52_3265.nolabels; use_zfuel_name = _52_3265.use_zfuel_name; encode_non_total_function_typ = _52_3265.encode_non_total_function_typ}))
in (let _52_3269 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(Support.Microsoft.FStar.Util.fprint1 "Done encoding externals for %s\n" name)
end
| false -> begin
()
end)
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun ( tcenv ) ( q ) -> (let _52_3274 = (let _70_26200 = (let _70_26199 = (let _70_26198 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_26198))
in (Support.Microsoft.FStar.Util.format1 "Starting query at %s" _70_26199))
in (push _70_26200))
in (let pop = (fun ( _52_3277 ) -> (match (()) with
| () -> begin
(let _70_26205 = (let _70_26204 = (let _70_26203 = (Microsoft_FStar_Tc_Env.get_range tcenv)
in (Support.All.pipe_left Support.Microsoft.FStar.Range.string_of_range _70_26203))
in (Support.Microsoft.FStar.Util.format1 "Ending query at %s" _70_26204))
in (pop _70_26205))
end))
in (let _52_3307 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun ( bs ) ( b ) -> (b)::bs) [])
in (let _52_3290 = (let _70_26209 = (Support.List.filter (fun ( _52_33 ) -> (match (_52_33) with
| Microsoft_FStar_Tc_Env.Binding_sig (_52_3284) -> begin
false
end
| _52_3287 -> begin
true
end)) bindings)
in (encode_env_bindings env _70_26209))
in (match (_52_3290) with
| (env_decls, env) -> begin
(let _52_3291 = (match ((Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low)) with
| true -> begin
(let _70_26210 = (Microsoft_FStar_Absyn_Print.formula_to_string q)
in (Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" _70_26210))
end
| false -> begin
()
end)
in (let _52_3296 = (encode_formula_with_labels q env)
in (match (_52_3296) with
| (phi, labels, qdecls) -> begin
(let _52_3299 = (encode_labels labels)
in (match (_52_3299) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Support.List.append (Support.List.append env_decls label_prefix) qdecls)
in (let qry = (let _70_26212 = (let _70_26211 = (Microsoft_FStar_ToSMT_Term.mkNot phi)
in (_70_26211, Some ("query")))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26212))
in (let suffix = (Support.List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_52_3307) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume (({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.False, _52_3314)); Microsoft_FStar_ToSMT_Term.hash = _52_3311; Microsoft_FStar_ToSMT_Term.freevars = _52_3309}, _52_3319)) -> begin
(let _52_3322 = (pop ())
in ())
end
| _52_3325 when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
(let _52_3326 = (pop ())
in ())
end
| Microsoft_FStar_ToSMT_Term.Assume ((q, _52_3330)) -> begin
(let fresh = ((Support.String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _52_3334 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun ( p ) ( _52_3340 ) -> (match (_52_3340) with
| (n, i) -> begin
(let _70_26234 = (let _70_26233 = (let _70_26218 = (let _70_26217 = (Support.Microsoft.FStar.Util.string_of_int n)
in (Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" _70_26217))
in Microsoft_FStar_ToSMT_Term.Caption (_70_26218))
in (let _70_26232 = (let _70_26231 = (let _70_26223 = (let _70_26222 = (let _70_26221 = (let _70_26220 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _70_26219 = (Microsoft_FStar_ToSMT_Term.n_fuel n)
in (_70_26220, _70_26219)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26221))
in (_70_26222, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26223))
in (let _70_26230 = (let _70_26229 = (let _70_26228 = (let _70_26227 = (let _70_26226 = (let _70_26225 = (Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _70_26224 = (Microsoft_FStar_ToSMT_Term.n_fuel i)
in (_70_26225, _70_26224)))
in (Microsoft_FStar_ToSMT_Term.mkEq _70_26226))
in (_70_26227, None))
in Microsoft_FStar_ToSMT_Term.Assume (_70_26228))
in (_70_26229)::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[])
in (_70_26231)::_70_26230))
in (_70_26233)::_70_26232))
in (Support.List.append _70_26234 suffix))
end))
in (let check = (fun ( p ) -> (let initial_config = (let _70_26238 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _70_26237 = (Support.ST.read Microsoft_FStar_Options.initial_ifuel)
in (_70_26238, _70_26237)))
in (let alt_configs = (let _70_26257 = (let _70_26256 = (match (((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel))) with
| true -> begin
(let _70_26241 = (let _70_26240 = (Support.ST.read Microsoft_FStar_Options.initial_fuel)
in (let _70_26239 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_26240, _70_26239)))
in (_70_26241)::[])
end
| false -> begin
[]
end)
in (let _70_26255 = (let _70_26254 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2) > (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _70_26244 = (let _70_26243 = ((Support.ST.read Microsoft_FStar_Options.max_fuel) / 2)
in (let _70_26242 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_26243, _70_26242)))
in (_70_26244)::[])
end
| false -> begin
[]
end)
in (let _70_26253 = (let _70_26252 = (match ((((Support.ST.read Microsoft_FStar_Options.max_fuel) > (Support.ST.read Microsoft_FStar_Options.initial_fuel)) && ((Support.ST.read Microsoft_FStar_Options.max_ifuel) > (Support.ST.read Microsoft_FStar_Options.initial_ifuel)))) with
| true -> begin
(let _70_26247 = (let _70_26246 = (Support.ST.read Microsoft_FStar_Options.max_fuel)
in (let _70_26245 = (Support.ST.read Microsoft_FStar_Options.max_ifuel)
in (_70_26246, _70_26245)))
in (_70_26247)::[])
end
| false -> begin
[]
end)
in (let _70_26251 = (let _70_26250 = (match (((Support.ST.read Microsoft_FStar_Options.min_fuel) < (Support.ST.read Microsoft_FStar_Options.initial_fuel))) with
| true -> begin
(let _70_26249 = (let _70_26248 = (Support.ST.read Microsoft_FStar_Options.min_fuel)
in (_70_26248, 1))
in (_70_26249)::[])
end
| false -> begin
[]
end)
in (_70_26250)::[])
in (_70_26252)::_70_26251))
in (_70_26254)::_70_26253))
in (_70_26256)::_70_26255))
in (Support.List.flatten _70_26257))
in (let report = (fun ( _52_3348 ) -> (match (_52_3348) with
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
| _52_3351 -> begin
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
(let _70_26269 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_26269 (cb p [])))
end
| _52_3363 -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(let _70_26271 = (with_fuel p mi)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_26271 (fun ( _52_3369 ) -> (match (_52_3369) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb p tl (ok, errs'))
end
| _52_3372 -> begin
(cb p tl (ok, errs))
end)
end))))
end))
and cb = (fun ( p ) ( alt ) ( _52_3377 ) -> (match (_52_3377) with
| (ok, errs) -> begin
(match (ok) with
| true -> begin
()
end
| false -> begin
(try_alt_configs p errs alt)
end)
end))
in (let _70_26275 = (with_fuel p initial_config)
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels _70_26275 (cb p alt_configs))))))))
in (let process_query = (fun ( q ) -> (match (((Support.ST.read Microsoft_FStar_Options.split_cases) > 0)) with
| true -> begin
(let _52_3382 = (let _70_26281 = (Support.ST.read Microsoft_FStar_Options.split_cases)
in (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query _70_26281 q))
in (match (_52_3382) with
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
in (let _52_3383 = (match ((Support.ST.read Microsoft_FStar_Options.admit_smt_queries)) with
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
in (let _52_3388 = (push "query")
in (let _52_3395 = (encode_formula_with_labels q env)
in (match (_52_3395) with
| (f, _52_3392, _52_3394) -> begin
(let _52_3396 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _52_3400)) -> begin
true
end
| _52_3404 -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = commit_mark; Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun ( _52_3405 ) -> ()); Microsoft_FStar_Tc_Env.push = (fun ( _52_3407 ) -> ()); Microsoft_FStar_Tc_Env.pop = (fun ( _52_3409 ) -> ()); Microsoft_FStar_Tc_Env.mark = (fun ( _52_3411 ) -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun ( _52_3413 ) -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun ( _52_3415 ) -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun ( _52_3417 ) ( _52_3419 ) -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun ( _52_3421 ) ( _52_3423 ) -> ()); Microsoft_FStar_Tc_Env.solve = (fun ( _52_3425 ) ( _52_3427 ) -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun ( _52_3429 ) ( _52_3431 ) -> false); Microsoft_FStar_Tc_Env.finish = (fun ( _52_3433 ) -> ()); Microsoft_FStar_Tc_Env.refresh = (fun ( _52_3434 ) -> ())}





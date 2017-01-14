
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _53_6 -> (match (_53_6) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun uu___207 -> (match (uu___207) with
| (FStar_Util.Inl (_53_10), _53_13) -> begin
false
end
| _53_16 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText a.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)


let mk_typ_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.string = (fun lid a -> (let _154_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _154_14)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.string = (fun lid a -> (

let a = (let _154_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _154_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _154_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _154_20))))


let primitive_projector_by_pos : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _53_28 -> (match (()) with
| () -> begin
(let _154_30 = (let _154_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _154_29 lid.FStar_Ident.str))
in (failwith _154_30))
end))
in (

let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _154_31 = (FStar_Absyn_Util.compress_typ t)
in _154_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_32) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(mk_typ_projector_name lid a.FStar_Absyn_Syntax.v)
end
| FStar_Util.Inr (x) -> begin
(mk_term_projector_name lid x.FStar_Absyn_Syntax.v)
end))
end
end
| _53_41 -> begin
(fail ())
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _154_37 = (let _154_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _154_36))
in (FStar_All.pipe_left escape _154_37)))


let mk_typ_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _154_43 = (let _154_42 = (mk_typ_projector_name lid a)
in ((_154_42), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Type_sort))))))
in (FStar_ToSMT_Term.mkFreeV _154_43)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _154_49 = (let _154_48 = (mk_term_projector_name lid a)
in ((_154_48), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Term_sort))))))
in (FStar_ToSMT_Term.mkFreeV _154_49)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_ToSMT_Term.term = (fun lid i -> (let _154_55 = (let _154_54 = (mk_term_projector_name_by_pos lid i)
in ((_154_54), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Term_sort))))))
in (FStar_ToSMT_Term.mkFreeV _154_55)))


let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  FStar_Ident.ident  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "10")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _53_67 -> (match (()) with
| () -> begin
(let _154_159 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _154_158 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_154_159), (_154_158))))
end))
in (

let scopes = (let _154_161 = (let _154_160 = (new_scope ())
in (_154_160)::[])
in (FStar_Util.mk_ref _154_161))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _154_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _154_165 (fun _53_75 -> (match (_53_75) with
| (names, _53_74) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_53_78) -> begin
(

let _53_80 = (FStar_Util.incr ctr)
in (let _154_168 = (let _154_167 = (let _154_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _154_166))
in (Prims.strcat "__" _154_167))
in (Prims.strcat y _154_168)))
end)
in (

let top_scope = (let _154_170 = (let _154_169 = (FStar_ST.read scopes)
in (FStar_List.hd _154_169))
in (FStar_All.pipe_left Prims.fst _154_170))
in (

let _53_84 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" rn.FStar_Ident.idText))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _53_92 -> (match (()) with
| () -> begin
(

let _53_93 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _154_182 = (let _154_181 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _154_181))
in (FStar_Util.format2 "%s_%s" pfx _154_182)))
in (

let string_const = (fun s -> (match ((let _154_186 = (FStar_ST.read scopes)
in (FStar_Util.find_map _154_186 (fun _53_102 -> (match (_53_102) with
| (_53_100, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _154_187 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _154_187))
in (

let top_scope = (let _154_189 = (let _154_188 = (FStar_ST.read scopes)
in (FStar_List.hd _154_188))
in (FStar_All.pipe_left Prims.snd _154_189))
in (

let _53_109 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _53_112 -> (match (()) with
| () -> begin
(let _154_194 = (let _154_193 = (new_scope ())
in (let _154_192 = (FStar_ST.read scopes)
in (_154_193)::_154_192))
in (FStar_ST.op_Colon_Equals scopes _154_194))
end))
in (

let pop = (fun _53_114 -> (match (()) with
| () -> begin
(let _154_198 = (let _154_197 = (FStar_ST.read scopes)
in (FStar_List.tl _154_197))
in (FStar_ST.op_Colon_Equals scopes _154_198))
end))
in (

let mark = (fun _53_116 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _53_118 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _53_120 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _53_133 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _53_138 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _53_141 -> begin
(failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))


let unmangle = (fun x -> (let _154_214 = (let _154_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _154_212 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in ((_154_213), (_154_212))))
in (FStar_Absyn_Util.mkbvd _154_214)))


type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term)
| Binding_tvar of (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option)
| Binding_ftvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option)


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
| Binding_var (_53_146) -> begin
_53_146
end))


let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_53_149) -> begin
_53_149
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_53_152) -> begin
_53_152
end))


let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_53_155) -> begin
_53_155
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _154_300 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___208 -> (match (uu___208) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _53_180) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _154_300 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string Prims.option = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _154_310 = (FStar_Absyn_Print.typ_to_string t)
in Some (_154_310))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_ToSMT_Term.sort  ->  (Prims.string * FStar_ToSMT_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _154_315 = (FStar_ToSMT_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_154_315)))))


let gen_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (let _154_320 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _154_320))
in (

let y = (FStar_ToSMT_Term.mkFreeV ((ysym), (FStar_ToSMT_Term.Term_sort)))
in ((ysym), (y), ((

let _53_199 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _53_199.tcenv; warn = _53_199.warn; cache = _53_199.cache; nolabels = _53_199.nolabels; use_zfuel_name = _53_199.use_zfuel_name; encode_non_total_function_typ = _53_199.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (

let y = (FStar_ToSMT_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _53_205 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _53_205.depth; tcenv = _53_205.tcenv; warn = _53_205.warn; cache = _53_205.cache; nolabels = _53_205.nolabels; use_zfuel_name = _53_205.use_zfuel_name; encode_non_total_function_typ = _53_205.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (

let _53_210 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _53_210.depth; tcenv = _53_210.tcenv; warn = _53_210.warn; cache = _53_210.cache; nolabels = _53_210.nolabels; use_zfuel_name = _53_210.use_zfuel_name; encode_non_total_function_typ = _53_210.encode_non_total_function_typ}))


let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun uu___209 -> (match (uu___209) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (((b), (t)))
end
| _53_220 -> begin
None
end)))) with
| None -> begin
(let _154_335 = (let _154_334 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _154_334))
in (failwith _154_335))
end
| Some (b, t) -> begin
t
end))


let gen_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (let _154_340 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _154_340))
in (

let y = (FStar_ToSMT_Term.mkFreeV ((ysym), (FStar_ToSMT_Term.Type_sort)))
in ((ysym), (y), ((

let _53_230 = env
in {bindings = (Binding_tvar (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _53_230.tcenv; warn = _53_230.warn; cache = _53_230.cache; nolabels = _53_230.nolabels; use_zfuel_name = _53_230.use_zfuel_name; encode_non_total_function_typ = _53_230.encode_non_total_function_typ}))))))


let new_typ_constant : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (

let y = (FStar_ToSMT_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _53_236 = env
in {bindings = (Binding_tvar (((x), (y))))::env.bindings; depth = _53_236.depth; tcenv = _53_236.tcenv; warn = _53_236.warn; cache = _53_236.cache; nolabels = _53_236.nolabels; use_zfuel_name = _53_236.use_zfuel_name; encode_non_total_function_typ = _53_236.encode_non_total_function_typ}))))))


let push_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (

let _53_241 = env
in {bindings = (Binding_tvar (((x), (t))))::env.bindings; depth = _53_241.depth; tcenv = _53_241.tcenv; warn = _53_241.warn; cache = _53_241.cache; nolabels = _53_241.nolabels; use_zfuel_name = _53_241.use_zfuel_name; encode_non_total_function_typ = _53_241.encode_non_total_function_typ}))


let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun uu___210 -> (match (uu___210) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (((b), (t)))
end
| _53_251 -> begin
None
end)))) with
| None -> begin
(let _154_355 = (let _154_354 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _154_354))
in (failwith _154_355))
end
| Some (b, t) -> begin
t
end))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _154_366 = (

let _53_261 = env
in (let _154_365 = (let _154_364 = (let _154_363 = (let _154_362 = (let _154_361 = (FStar_ToSMT_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _154_360 -> Some (_154_360)) _154_361))
in ((x), (fname), (_154_362), (None)))
in Binding_fvar (_154_363))
in (_154_364)::env.bindings)
in {bindings = _154_365; depth = _53_261.depth; tcenv = _53_261.tcenv; warn = _53_261.warn; cache = _53_261.cache; nolabels = _53_261.nolabels; use_zfuel_name = _53_261.use_zfuel_name; encode_non_total_function_typ = _53_261.encode_non_total_function_typ}))
in ((fname), (ftok), (_154_366))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___211 -> (match (uu___211) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _53_273 -> begin
None
end))))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _154_377 = (let _154_376 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _154_376))
in (failwith _154_377))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _53_283 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _53_283.depth; tcenv = _53_283.tcenv; warn = _53_283.warn; cache = _53_283.cache; nolabels = _53_283.nolabels; use_zfuel_name = _53_283.use_zfuel_name; encode_non_total_function_typ = _53_283.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _53_292 = (lookup_lid env x)
in (match (_53_292) with
| (t1, t2, _53_291) -> begin
(

let t3 = (let _154_394 = (let _154_393 = (let _154_392 = (FStar_ToSMT_Term.mkApp (("ZFuel"), ([])))
in (_154_392)::[])
in ((f), (_154_393)))
in (FStar_ToSMT_Term.mkApp _154_394))
in (

let _53_294 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _53_294.depth; tcenv = _53_294.tcenv; warn = _53_294.warn; cache = _53_294.cache; nolabels = _53_294.nolabels; use_zfuel_name = _53_294.use_zfuel_name; encode_non_total_function_typ = _53_294.encode_non_total_function_typ}))
end)))


let lookup_free_var = (fun env a -> (

let _53_301 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_301) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _53_305 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_53_309, (fuel)::[]) -> begin
if (let _154_398 = (let _154_397 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _154_397 Prims.fst))
in (FStar_Util.starts_with _154_398 "fuel")) then begin
(let _154_399 = (FStar_ToSMT_Term.mkFreeV ((name), (FStar_ToSMT_Term.Term_sort)))
in (FStar_ToSMT_Term.mk_ApplyEF _154_399 fuel))
end else begin
t
end
end
| _53_315 -> begin
t
end)
end
| _53_317 -> begin
(let _154_401 = (let _154_400 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _154_400))
in (failwith _154_401))
end)
end)
end)))


let lookup_free_var_name = (fun env a -> (

let _53_325 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_325) with
| (x, _53_322, _53_324) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _53_331 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_53_331) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _53_335; FStar_ToSMT_Term.freevars = _53_333}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _53_343 -> begin
(match (sym) with
| None -> begin
((FStar_ToSMT_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _53_353 -> begin
((FStar_ToSMT_Term.Var (name)), ([]))
end)
end)
end)
end)))


let new_typ_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _154_416 = (

let _53_358 = env
in (let _154_415 = (let _154_414 = (let _154_413 = (let _154_412 = (let _154_411 = (FStar_ToSMT_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _154_410 -> Some (_154_410)) _154_411))
in ((x), (fname), (_154_412)))
in Binding_ftvar (_154_413))
in (_154_414)::env.bindings)
in {bindings = _154_415; depth = _53_358.depth; tcenv = _53_358.tcenv; warn = _53_358.warn; cache = _53_358.cache; nolabels = _53_358.nolabels; use_zfuel_name = _53_358.use_zfuel_name; encode_non_total_function_typ = _53_358.encode_non_total_function_typ}))
in ((fname), (ftok), (_154_416))))))


let lookup_tlid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((lookup_binding env (fun uu___212 -> (match (uu___212) with
| Binding_ftvar (b, t1, t2) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2)))
end
| _53_369 -> begin
None
end)))) with
| None -> begin
(let _154_423 = (let _154_422 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _154_422))
in (failwith _154_423))
end
| Some (s) -> begin
s
end))


let push_free_tvar : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _53_377 = env
in {bindings = (Binding_ftvar (((x), (fname), (ftok))))::env.bindings; depth = _53_377.depth; tcenv = _53_377.tcenv; warn = _53_377.warn; cache = _53_377.cache; nolabels = _53_377.nolabels; use_zfuel_name = _53_377.use_zfuel_name; encode_non_total_function_typ = _53_377.encode_non_total_function_typ}))


let lookup_free_tvar = (fun env a -> (match ((let _154_434 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _154_434 Prims.snd))) with
| None -> begin
(let _154_436 = (let _154_435 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _154_435))
in (failwith _154_436))
end
| Some (t) -> begin
t
end))


let lookup_free_tvar_name = (fun env a -> (let _154_439 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _154_439 Prims.fst)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___213 -> (match (uu___213) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _53_402 -> begin
None
end))))


let mkForall_fuel' = (fun n _53_407 -> (match (_53_407) with
| (pats, vars, body) -> begin
(

let fallback = (fun _53_409 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _53_412 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_412) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _53_422 -> begin
p
end)))))
in (

let pats = (FStar_List.map add_fuel pats)
in (

let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _154_452 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _154_452))
end
| _53_435 -> begin
(let _154_453 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _154_453 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp ((guard), (body'))))
end
| _53_438 -> begin
body
end)
in (

let vars = (((fsym), (FStar_ToSMT_Term.Fuel_sort)))::vars
in (FStar_ToSMT_Term.mkForall ((pats), (vars), (body)))))))
end))
end)
end))


let mkForall_fuel : (FStar_ToSMT_Term.pat Prims.list Prims.list * FStar_ToSMT_Term.fvs * FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun env t -> (

let t = (FStar_Absyn_Util.unmeta_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (FStar_Absyn_Syntax.Typ_const (v)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (v); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _154_459 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _154_459 FStar_Option.isNone))
end
| _53_476 -> begin
false
end)))


let whnf : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end)


let whnf_e : env_t  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun env e -> (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))


let norm_t : env_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env.tcenv t))


let norm_k : env_t  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (FStar_Tc_Normalize.normalize_kind env.tcenv k))


let trivial_post : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t -> (let _154_481 = (let _154_480 = (let _154_478 = (FStar_Absyn_Syntax.null_v_binder t)
in (_154_478)::[])
in (let _154_479 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((_154_480), (_154_479))))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_481 None t.FStar_Absyn_Syntax.pos)))


let mk_ApplyE : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _154_488 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _154_488))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _154_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _154_489))
end
| _53_493 -> begin
(let _154_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _154_490))
end)) e)))


let mk_ApplyE_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyET out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))


let mk_ApplyT : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun t vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _154_503 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _154_503))
end
| _53_508 -> begin
(let _154_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _154_504))
end)) t)))


let mk_ApplyT_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))


let is_app : FStar_ToSMT_Term.op  ->  Prims.bool = (fun uu___214 -> (match (uu___214) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _53_527 -> begin
false
end))


let is_eta : env_t  ->  FStar_ToSMT_Term.fv Prims.list  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_ToSMT_Term.tm), (xs))) with
| (FStar_ToSMT_Term.App (app, (f)::({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _53_538; FStar_ToSMT_Term.freevars = _53_536})::[]), (x)::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _53_556) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _53_563 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_53_565, []) -> begin
(

let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _53_571 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


type label =
(FStar_ToSMT_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list


type pattern =
{pat_vars : (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t); guard : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term; projections : FStar_ToSMT_Term.term  ->  (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.term) Prims.list}


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkpattern"))))


exception Let_rec_unencodeable


let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))


exception Bad_form


let is_Bad_form = (fun _discr_ -> (match (_discr_) with
| Bad_form (_) -> begin
true
end
| _ -> begin
false
end))


let constructor_string_of_int_qualifier : (FStar_Const.signedness * FStar_Const.width)  ->  Prims.string = (fun uu___215 -> (match (uu___215) with
| (FStar_Const.Unsigned, FStar_Const.Int8) -> begin
"FStar.UInt8.UInt8"
end
| (FStar_Const.Signed, FStar_Const.Int8) -> begin
"FStar.Int8.Int8"
end
| (FStar_Const.Unsigned, FStar_Const.Int16) -> begin
"FStar.UInt16.UInt16"
end
| (FStar_Const.Signed, FStar_Const.Int16) -> begin
"FStar.Int16.Int16"
end
| (FStar_Const.Unsigned, FStar_Const.Int32) -> begin
"FStar.UInt32.UInt32"
end
| (FStar_Const.Signed, FStar_Const.Int32) -> begin
"FStar.Int32.Int32"
end
| (FStar_Const.Unsigned, FStar_Const.Int64) -> begin
"FStar.UInt64.UInt64"
end
| (FStar_Const.Signed, FStar_Const.Int64) -> begin
"FStar.Int64.Int64"
end))


let encode_const : FStar_Const.sconst  ->  FStar_ToSMT_Term.term = (fun uu___216 -> (match (uu___216) with
| FStar_Const.Const_unit -> begin
FStar_ToSMT_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _154_566 = (let _154_565 = (let _154_564 = (let _154_563 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _154_563))
in (_154_564)::[])
in (("FStar.Char.Char"), (_154_565)))
in (FStar_ToSMT_Term.mkApp _154_566))
end
| FStar_Const.Const_int (i, None) -> begin
(let _154_567 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _154_567))
end
| FStar_Const.Const_int (i, Some (q)) -> begin
(let _154_571 = (let _154_570 = (let _154_569 = (let _154_568 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _154_568))
in (_154_569)::[])
in (((constructor_string_of_int_qualifier q)), (_154_570)))
in (FStar_ToSMT_Term.mkApp _154_571))
end
| FStar_Const.Const_string (bytes, _53_621) -> begin
(let _154_572 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _154_572))
end
| c -> begin
(let _154_574 = (let _154_573 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _154_573))
in (failwith _154_574))
end))


let as_function_typ : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_53_632) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_53_635) -> begin
(let _154_583 = (FStar_Absyn_Util.unrefine t)
in (aux true _154_583))
end
| _53_638 -> begin
if norm then begin
(let _154_584 = (whnf env t)
in (aux false _154_584))
end else begin
(let _154_587 = (let _154_586 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _154_585 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _154_586 _154_585)))
in (failwith _154_587))
end
end)))
in (aux true t0)))


let rec encode_knd_term : FStar_Absyn_Syntax.knd  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun k env -> (match ((let _154_624 = (FStar_Absyn_Util.compress_kind k)
in _154_624.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
((FStar_ToSMT_Term.mk_Kind_type), ([]))
end
| FStar_Absyn_Syntax.Kind_abbrev (_53_643, k0) -> begin
(

let _53_647 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _154_626 = (FStar_Absyn_Print.kind_to_string k)
in (let _154_625 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.print2 "Encoding kind abbrev %s, expanded to %s\n" _154_626 _154_625)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _53_651) -> begin
(let _154_628 = (let _154_627 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _154_627))
in ((_154_628), ([])))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(

let tsym = (let _154_629 = (varops.fresh "t")
in ((_154_629), (FStar_ToSMT_Term.Type_sort)))
in (

let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (

let _53_666 = (encode_binders None bs env)
in (match (_53_666) with
| (vars, guards, env', decls, _53_665) -> begin
(

let app = (mk_ApplyT t vars)
in (

let _53_670 = (encode_knd kbody env' app)
in (match (_53_670) with
| (kbody, decls') -> begin
(

let rec aux = (fun app vars guards -> (match (((vars), (guards))) with
| ([], []) -> begin
kbody
end
| ((x)::vars, (g)::guards) -> begin
(

let app = (mk_ApplyT app ((x)::[]))
in (

let body = (aux app vars guards)
in (

let body = (match (vars) with
| [] -> begin
body
end
| _53_689 -> begin
(let _154_638 = (let _154_637 = (let _154_636 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _154_636))
in ((_154_637), (body)))
in (FStar_ToSMT_Term.mkAnd _154_638))
end)
in (let _154_640 = (let _154_639 = (FStar_ToSMT_Term.mkImp ((g), (body)))
in ((((app)::[])::[]), ((x)::[]), (_154_639)))
in (FStar_ToSMT_Term.mkForall _154_640)))))
end
| _53_692 -> begin
(failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (

let k_interp = (aux t vars guards)
in (

let cvars = (let _154_642 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _154_642 (FStar_List.filter (fun _53_697 -> (match (_53_697) with
| (x, _53_696) -> begin
(x <> (Prims.fst tsym))
end)))))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((tsym)::cvars), (k_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _53_703) -> begin
(let _154_645 = (let _154_644 = (let _154_643 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((k'), (_154_643)))
in (FStar_ToSMT_Term.mkApp _154_644))
in ((_154_645), ([])))
end
| None -> begin
(

let ksym = (varops.fresh "Kind_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _154_646 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_154_646))
end else begin
None
end
in (

let kdecl = FStar_ToSMT_Term.DeclFun (((ksym), (cvar_sorts), (FStar_ToSMT_Term.Kind_sort), (caption)))
in (

let k = (let _154_648 = (let _154_647 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((ksym), (_154_647)))
in (FStar_ToSMT_Term.mkApp _154_648))
in (

let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (

let k_interp = (let _154_657 = (let _154_656 = (let _154_655 = (let _154_654 = (let _154_653 = (let _154_652 = (let _154_651 = (let _154_650 = (let _154_649 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _154_649))
in ((_154_650), (k_interp)))
in (FStar_ToSMT_Term.mkAnd _154_651))
in ((t_has_k), (_154_652)))
in (FStar_ToSMT_Term.mkIff _154_653))
in ((((t_has_k)::[])::[]), ((tsym)::cvars), (_154_654)))
in (FStar_ToSMT_Term.mkForall _154_655))
in ((_154_656), (Some ((Prims.strcat ksym " interpretation")))))
in FStar_ToSMT_Term.Assume (_154_657))
in (

let k_decls = (FStar_List.append decls (FStar_List.append decls' ((kdecl)::(k_interp)::[])))
in (

let _53_715 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((ksym), (cvar_sorts), (k_decls)))
in ((k), (k_decls)))))))))))
end)))))
end)))
end))))
end
| _53_718 -> begin
(let _154_659 = (let _154_658 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _154_658))
in (failwith _154_659))
end))
and encode_knd : FStar_Absyn_Syntax.knd  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decl Prims.list) = (fun k env t -> (

let _53_724 = (encode_knd_term k env)
in (match (_53_724) with
| (k, decls) -> begin
(let _154_663 = (FStar_ToSMT_Term.mk_HasKind t k)
in ((_154_663), (decls)))
end)))
and encode_binders : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.binders  ->  env_t  ->  (FStar_ToSMT_Term.fv Prims.list * FStar_ToSMT_Term.term Prims.list * env_t * FStar_ToSMT_Term.decls_t * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list) = (fun fuel_opt bs env -> (

let _53_728 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _154_667 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _154_667))
end else begin
()
end
in (

let _53_778 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_735 b -> (match (_53_735) with
| (vars, guards, env, decls, names) -> begin
(

let _53_772 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _53_738}) -> begin
(

let a = (unmangle a)
in (

let _53_747 = (gen_typ_var env a)
in (match (_53_747) with
| (aasym, aa, env') -> begin
(

let _53_748 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _154_671 = (FStar_Absyn_Print.strBvd a)
in (let _154_670 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print3 "Encoding type binder %s (%s) at kind %s\n" _154_671 aasym _154_670)))
end else begin
()
end
in (

let _53_752 = (encode_knd k env aa)
in (match (_53_752) with
| (guard_a_k, decls') -> begin
((((aasym), (FStar_ToSMT_Term.Type_sort))), (guard_a_k), (env'), (decls'), (FStar_Util.Inl (a)))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _53_754}) -> begin
(

let x = (unmangle x)
in (

let _53_763 = (gen_term_var env x)
in (match (_53_763) with
| (xxsym, xx, env') -> begin
(

let _53_766 = (let _154_672 = (norm_t env t)
in (encode_typ_pred fuel_opt _154_672 env xx))
in (match (_53_766) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_ToSMT_Term.Term_sort))), (guard_x_t), (env'), (decls'), (FStar_Util.Inr (x)))
end))
end)))
end)
in (match (_53_772) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_53_778) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_typ_pred : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let _53_786 = (encode_typ_term t env)
in (match (_53_786) with
| (t, decls) -> begin
(let _154_677 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_154_677), (decls)))
end))))
and encode_typ_pred' : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let _53_794 = (encode_typ_term t env)
in (match (_53_794) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _154_682 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in ((_154_682), (decls)))
end
| Some (f) -> begin
(let _154_683 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in ((_154_683), (decls)))
end)
end))))
and encode_typ_term : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _154_686 = (lookup_typ_var env a)
in ((_154_686), ([])))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _154_687 = (lookup_free_tvar env fv)
in ((_154_687), ([])))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(

let _53_815 = (encode_binders None binders env)
in (match (_53_815) with
| (vars, guards, env', decls, _53_814) -> begin
(

let fsym = (let _154_688 = (varops.fresh "f")
in ((_154_688), (FStar_ToSMT_Term.Term_sort)))
in (

let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (

let app = (mk_ApplyE f vars)
in (

let _53_821 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_53_821) with
| (pre_opt, res_t) -> begin
(

let _53_824 = (encode_typ_pred None res_t env' app)
in (match (_53_824) with
| (res_pred, decls') -> begin
(

let _53_833 = (match (pre_opt) with
| None -> begin
(let _154_689 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_154_689), (decls)))
end
| Some (pre) -> begin
(

let _53_830 = (encode_formula pre env')
in (match (_53_830) with
| (guard, decls0) -> begin
(let _154_690 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in ((_154_690), ((FStar_List.append decls decls0))))
end))
end)
in (match (_53_833) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _154_692 = (let _154_691 = (FStar_ToSMT_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_154_691)))
in (FStar_ToSMT_Term.mkForall _154_692))
in (

let cvars = (let _154_694 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _154_694 (FStar_List.filter (fun _53_838 -> (match (_53_838) with
| (x, _53_837) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _53_844) -> begin
(let _154_697 = (let _154_696 = (let _154_695 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((t'), (_154_695)))
in (FStar_ToSMT_Term.mkApp _154_696))
in ((_154_697), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Typ_fun")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _154_698 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_154_698))
end else begin
None
end
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (caption)))
in (

let t = (let _154_700 = (let _154_699 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_154_699)))
in (FStar_ToSMT_Term.mkApp _154_700))
in (

let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (

let k_assumption = (let _154_702 = (let _154_701 = (FStar_ToSMT_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_154_701), (Some ((Prims.strcat tsym " kinding")))))
in FStar_ToSMT_Term.Assume (_154_702))
in (

let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (

let pre_typing = (let _154_709 = (let _154_708 = (let _154_707 = (let _154_706 = (let _154_705 = (let _154_704 = (let _154_703 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _154_703))
in ((f_has_t), (_154_704)))
in (FStar_ToSMT_Term.mkImp _154_705))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_154_706)))
in (mkForall_fuel _154_707))
in ((_154_708), (Some ("pre-typing for functions"))))
in FStar_ToSMT_Term.Assume (_154_709))
in (

let t_interp = (let _154_713 = (let _154_712 = (let _154_711 = (let _154_710 = (FStar_ToSMT_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_154_710)))
in (FStar_ToSMT_Term.mkForall _154_711))
in ((_154_712), (Some ((Prims.strcat tsym " interpretation")))))
in FStar_ToSMT_Term.Assume (_154_713))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[])))
in (

let _53_860 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(

let tsym = (varops.fresh "Non_total_Typ_fun")
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (FStar_ToSMT_Term.mkApp ((tsym), ([])))
in (

let t_kinding = (let _154_715 = (let _154_714 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in ((_154_714), (None)))
in FStar_ToSMT_Term.Assume (_154_715))
in (

let fsym = (("f"), (FStar_ToSMT_Term.Term_sort))
in (

let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (

let t_interp = (let _154_722 = (let _154_721 = (let _154_720 = (let _154_719 = (let _154_718 = (let _154_717 = (let _154_716 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _154_716))
in ((f_has_t), (_154_717)))
in (FStar_ToSMT_Term.mkImp _154_718))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_154_719)))
in (mkForall_fuel _154_720))
in ((_154_721), (Some ("pre-typing"))))
in FStar_ToSMT_Term.Assume (_154_722))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_53_871) -> begin
(

let _53_890 = (match ((FStar_Tc_Normalize.normalize_refinement [] env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _53_880; FStar_Absyn_Syntax.pos = _53_878; FStar_Absyn_Syntax.fvs = _53_876; FStar_Absyn_Syntax.uvs = _53_874} -> begin
((x), (f))
end
| _53_887 -> begin
(failwith "impossible")
end)
in (match (_53_890) with
| (x, f) -> begin
(

let _53_893 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_53_893) with
| (base_t, decls) -> begin
(

let _53_897 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_53_897) with
| (x, xtm, env') -> begin
(

let _53_900 = (encode_formula f env')
in (match (_53_900) with
| (refinement, decls') -> begin
(

let _53_903 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_903) with
| (fsym, fterm) -> begin
(

let encoding = (let _154_724 = (let _154_723 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_154_723), (refinement)))
in (FStar_ToSMT_Term.mkAnd _154_724))
in (

let cvars = (let _154_726 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _154_726 (FStar_List.filter (fun _53_908 -> (match (_53_908) with
| (y, _53_907) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_ToSMT_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_ToSMT_Term.Fuel_sort))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_915, _53_917) -> begin
(let _154_729 = (let _154_728 = (let _154_727 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((t), (_154_727)))
in (FStar_ToSMT_Term.mkApp _154_728))
in ((_154_729), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Typ_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (let _154_731 = (let _154_730 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_154_730)))
in (FStar_ToSMT_Term.mkApp _154_731))
in (

let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (

let t_kinding = (FStar_ToSMT_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in (

let assumption = (let _154_733 = (let _154_732 = (FStar_ToSMT_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_154_732)))
in (FStar_ToSMT_Term.mkForall _154_733))
in (

let t_decls = (let _154_741 = (let _154_740 = (let _154_739 = (let _154_738 = (let _154_737 = (let _154_736 = (let _154_735 = (let _154_734 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_154_734))
in ((assumption), (_154_735)))
in FStar_ToSMT_Term.Assume (_154_736))
in (_154_737)::[])
in (FStar_ToSMT_Term.Assume (((t_kinding), (None))))::_154_738)
in (tdecl)::_154_739)
in (FStar_List.append decls' _154_740))
in (FStar_List.append decls _154_741))
in (

let _53_930 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls))))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(

let ttm = (let _154_742 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _154_742))
in (

let _53_939 = (encode_knd k env ttm)
in (match (_53_939) with
| (t_has_k, decls) -> begin
(

let d = FStar_ToSMT_Term.Assume (((t_has_k), (None)))
in ((ttm), ((d)::decls)))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let is_full_app = (fun _53_946 -> (match (()) with
| () -> begin
(

let kk = (FStar_Tc_Recheck.recompute_kind head)
in (

let _53_951 = (FStar_Absyn_Util.kind_formals kk)
in (match (_53_951) with
| (formals, _53_950) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (

let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(

let head = (lookup_typ_var env a)
in (

let _53_958 = (encode_args args env)
in (match (_53_958) with
| (args, decls) -> begin
(

let t = (mk_ApplyT_args head args)
in ((t), (decls)))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let _53_964 = (encode_args args env)
in (match (_53_964) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(

let head = (lookup_free_tvar_name env fv)
in (

let t = (let _154_747 = (let _154_746 = (FStar_List.map (fun uu___217 -> (match (uu___217) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in ((head), (_154_746)))
in (FStar_ToSMT_Term.mkApp _154_747))
in ((t), (decls))))
end else begin
(

let head = (lookup_free_tvar env fv)
in (

let t = (mk_ApplyT_args head args)
in ((t), (decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(

let ttm = (let _154_748 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _154_748))
in (

let _53_980 = (encode_knd k env ttm)
in (match (_53_980) with
| (t_has_k, decls) -> begin
(

let d = FStar_ToSMT_Term.Assume (((t_has_k), (None)))
in ((ttm), ((d)::decls)))
end)))
end
| _53_983 -> begin
(

let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(

let _53_995 = (encode_binders None bs env)
in (match (_53_995) with
| (vars, guards, env, decls, _53_994) -> begin
(

let _53_998 = (encode_typ_term body env)
in (match (_53_998) with
| (body, decls') -> begin
(

let key_body = (let _154_752 = (let _154_751 = (let _154_750 = (let _154_749 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_154_749), (body)))
in (FStar_ToSMT_Term.mkImp _154_750))
in (([]), (vars), (_154_751)))
in (FStar_ToSMT_Term.mkForall _154_752))
in (

let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1004, _53_1006) -> begin
(let _154_755 = (let _154_754 = (let _154_753 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((t), (_154_753)))
in (FStar_ToSMT_Term.mkApp _154_754))
in ((_154_755), ([])))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
((head), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tsym = (varops.fresh "Typ_lam")
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (let _154_757 = (let _154_756 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_154_756)))
in (FStar_ToSMT_Term.mkApp _154_757))
in (

let app = (mk_ApplyT t vars)
in (

let interp = (let _154_764 = (let _154_763 = (let _154_762 = (let _154_761 = (let _154_760 = (let _154_759 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _154_758 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_154_759), (_154_758))))
in (FStar_ToSMT_Term.mkImp _154_760))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_154_761)))
in (FStar_ToSMT_Term.mkForall _154_762))
in ((_154_763), (Some ("Typ_lam interpretation"))))
in FStar_ToSMT_Term.Assume (_154_764))
in (

let kinding = (

let _53_1021 = (let _154_765 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _154_765 env t))
in (match (_53_1021) with
| (ktm, decls'') -> begin
(let _154_769 = (let _154_768 = (let _154_767 = (let _154_766 = (FStar_ToSMT_Term.mkForall ((((t)::[])::[]), (cvars), (ktm)))
in ((_154_766), (Some ("Typ_lam kinding"))))
in FStar_ToSMT_Term.Assume (_154_767))
in (_154_768)::[])
in (FStar_List.append decls'' _154_769))
end))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(interp)::kinding)))
in (

let _53_1024 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _53_1028) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_53_1032) -> begin
(let _154_770 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _154_770 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _154_775 = (let _154_774 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _154_773 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _154_772 = (FStar_Absyn_Print.typ_to_string t0)
in (let _154_771 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _154_774 _154_773 _154_772 _154_771)))))
in (failwith _154_775))
end)))
and encode_exp : FStar_Absyn_Syntax.exp  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun e env -> (

let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (

let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_53_1043) -> begin
(let _154_778 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _154_778 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _53_1050) -> begin
(let _154_779 = (lookup_free_var env v)
in ((_154_779), ([])))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _154_780 = (encode_const c)
in ((_154_780), ([])))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _53_1058) -> begin
(

let _53_1061 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _53_1065)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _53_1071) -> begin
(

let e = (let _154_781 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _154_781))
in ((e), ([])))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let fallback = (fun _53_1080 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Exp_abs")
in (

let decl = FStar_ToSMT_Term.DeclFun (((f), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (let _154_784 = (FStar_ToSMT_Term.mkFreeV ((f), (FStar_ToSMT_Term.Term_sort)))
in ((_154_784), ((decl)::[])))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(

let _53_1084 = (FStar_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _154_785 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _154_785)) then begin
(fallback ())
end else begin
(

let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(

let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(

let _53_1096 = (FStar_Util.first_N nformals bs)
in (match (_53_1096) with
| (bs0, rest) -> begin
(

let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _53_1100 -> begin
(failwith "Impossible")
end)
in (

let e = (let _154_787 = (let _154_786 = (FStar_Absyn_Syntax.mk_Exp_abs ((rest), (body)) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in ((bs0), (_154_786)))
in (FStar_Absyn_Syntax.mk_Exp_abs _154_787 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(

let _53_1109 = (encode_binders None bs env)
in (match (_53_1109) with
| (vars, guards, envbody, decls, _53_1108) -> begin
(

let _53_1112 = (encode_exp body envbody)
in (match (_53_1112) with
| (body, decls') -> begin
(

let key_body = (let _154_791 = (let _154_790 = (let _154_789 = (let _154_788 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_154_788), (body)))
in (FStar_ToSMT_Term.mkImp _154_789))
in (([]), (vars), (_154_790)))
in (FStar_ToSMT_Term.mkForall _154_791))
in (

let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _53_1118, _53_1120) -> begin
(let _154_794 = (let _154_793 = (let _154_792 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((t), (_154_792)))
in (FStar_ToSMT_Term.mkApp _154_793))
in ((_154_794), ([])))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (varops.fresh "Exp_abs")
in (

let fdecl = FStar_ToSMT_Term.DeclFun (((fsym), (cvar_sorts), (FStar_ToSMT_Term.Term_sort), (None)))
in (

let f = (let _154_796 = (let _154_795 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((fsym), (_154_795)))
in (FStar_ToSMT_Term.mkApp _154_796))
in (

let app = (mk_ApplyE f vars)
in (

let _53_1134 = (encode_typ_pred None tfun env f)
in (match (_53_1134) with
| (f_has_t, decls'') -> begin
(

let typing_f = (let _154_798 = (let _154_797 = (FStar_ToSMT_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_154_797), (Some ((Prims.strcat fsym " typing")))))
in FStar_ToSMT_Term.Assume (_154_798))
in (

let interp_f = (let _154_805 = (let _154_804 = (let _154_803 = (let _154_802 = (let _154_801 = (let _154_800 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _154_799 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_154_800), (_154_799))))
in (FStar_ToSMT_Term.mkImp _154_801))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_154_802)))
in (FStar_ToSMT_Term.mkForall _154_803))
in ((_154_804), (Some ((Prims.strcat fsym " interpretation")))))
in FStar_ToSMT_Term.Assume (_154_805))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::decls'') ((typing_f)::(interp_f)::[]))))
in (

let _53_1138 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls))))))
end)))))))
end)
end))))
end))
end))
end)
end
| _53_1141 -> begin
(failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _53_1152); FStar_Absyn_Syntax.tk = _53_1149; FStar_Absyn_Syntax.pos = _53_1147; FStar_Absyn_Syntax.fvs = _53_1145; FStar_Absyn_Syntax.uvs = _53_1143}, ((FStar_Util.Inl (_53_1167), _53_1170))::((FStar_Util.Inr (v1), _53_1164))::((FStar_Util.Inr (v2), _53_1159))::[]) when (FStar_Ident.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(

let _53_1177 = (encode_exp v1 env)
in (match (_53_1177) with
| (v1, decls1) -> begin
(

let _53_1180 = (encode_exp v2 env)
in (match (_53_1180) with
| (v2, decls2) -> begin
(let _154_806 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in ((_154_806), ((FStar_List.append decls1 decls2))))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_53_1190); FStar_Absyn_Syntax.tk = _53_1188; FStar_Absyn_Syntax.pos = _53_1186; FStar_Absyn_Syntax.fvs = _53_1184; FStar_Absyn_Syntax.uvs = _53_1182}, _53_1194) -> begin
(let _154_807 = (whnf_e env e)
in (encode_exp _154_807 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(

let _53_1203 = (encode_args args_e env)
in (match (_53_1203) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _53_1208 = (encode_exp head env)
in (match (_53_1208) with
| (head, decls') -> begin
(

let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _53_1217 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_53_1217) with
| (formals, rest) -> begin
(

let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (

let ty = (let _154_810 = (FStar_Absyn_Syntax.mk_Typ_fun ((rest), (c)) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _154_810 (FStar_Absyn_Util.subst_typ subst)))
in (

let _53_1222 = (encode_typ_pred None ty env app_tm)
in (match (_53_1222) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (

let e_typing = (let _154_812 = (let _154_811 = (FStar_ToSMT_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in ((_154_811), (None)))
in FStar_ToSMT_Term.Assume (_154_812))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _53_1229 = (lookup_free_var_sym env fv)
in (match (_53_1229) with
| (fname, fuel_args) -> begin
(

let tm = (let _154_818 = (let _154_817 = (let _154_816 = (FStar_List.map (fun uu___218 -> (match (uu___218) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _154_816))
in ((fname), (_154_817)))
in (FStar_ToSMT_Term.mkApp' _154_818))
in ((tm), (decls)))
end)))
in (

let head = (FStar_Absyn_Util.compress_exp head)
in (

let _53_1236 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _154_820 = (FStar_Absyn_Print.exp_to_string head)
in (let _154_819 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print2 "Recomputing type for %s\nFull term is %s\n" _154_820 _154_819)))
end else begin
()
end
in (

let head_type = (let _154_823 = (let _154_822 = (let _154_821 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _154_821))
in (whnf env _154_822))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _154_823))
in (

let _53_1239 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _154_826 = (FStar_Absyn_Print.exp_to_string head)
in (let _154_825 = (FStar_Absyn_Print.tag_of_exp head)
in (let _154_824 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _154_826 _154_825 _154_824))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _154_830 = (let _154_829 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _154_828 = (FStar_Absyn_Print.exp_to_string e0)
in (let _154_827 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _154_829 _154_828 _154_827))))
in (failwith _154_830))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _53_1248) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _53_1252 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some (((formals), (c)))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_53_1261); FStar_Absyn_Syntax.lbtyp = _53_1259; FStar_Absyn_Syntax.lbeff = _53_1257; FStar_Absyn_Syntax.lbdef = _53_1255})::[]), _53_1267) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _53_1273; FStar_Absyn_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _53_1285 = (encode_exp e1 env)
in (match (_53_1285) with
| (ee1, decls1) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _53_1289 = (encode_exp e2 env')
in (match (_53_1289) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_53_1291) -> begin
(

let _53_1293 = (FStar_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_ToSMT_Term.DeclFun (((e), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (let _154_831 = (FStar_ToSMT_Term.mkFreeV ((e), (FStar_ToSMT_Term.Term_sort)))
in ((_154_831), ((decl_e)::[]))))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(

let _53_1303 = (encode_exp e env)
in (match (_53_1303) with
| (scr, decls) -> begin
(

let _53_1343 = (FStar_List.fold_right (fun _53_1307 _53_1310 -> (match (((_53_1307), (_53_1310))) with
| ((p, w, br), (else_case, decls)) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _53_1314 _53_1317 -> (match (((_53_1314), (_53_1317))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _53_1323 -> (match (_53_1323) with
| (x, t) -> begin
(match (x) with
| FStar_Util.Inl (a) -> begin
(push_typ_var env a.FStar_Absyn_Syntax.v t)
end
| FStar_Util.Inr (x) -> begin
(push_term_var env x.FStar_Absyn_Syntax.v t)
end)
end)) env))
in (

let _53_1337 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _53_1334 = (encode_exp w env)
in (match (_53_1334) with
| (w, decls2) -> begin
(let _154_842 = (let _154_841 = (let _154_840 = (let _154_839 = (let _154_838 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in ((w), (_154_838)))
in (FStar_ToSMT_Term.mkEq _154_839))
in ((guard), (_154_840)))
in (FStar_ToSMT_Term.mkAnd _154_841))
in ((_154_842), (decls2)))
end))
end)
in (match (_53_1337) with
| (guard, decls2) -> begin
(

let _53_1340 = (encode_exp br env)
in (match (_53_1340) with
| (br, decls3) -> begin
(let _154_843 = (FStar_ToSMT_Term.mkITE ((guard), (br), (else_case)))
in ((_154_843), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end)) pats ((FStar_ToSMT_Term.mk_Term_unit), (decls)))
in (match (_53_1343) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_53_1345) -> begin
(let _154_846 = (let _154_845 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _154_844 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _154_845 _154_844)))
in (failwith _154_846))
end))))
and encode_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _53_1352 -> begin
(let _154_849 = (encode_one_pat env pat)
in (_154_849)::[])
end))
and encode_one_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _53_1355 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _154_852 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _154_852))
end else begin
()
end
in (

let _53_1359 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_53_1359) with
| (vars, pat_exp_or_typ) -> begin
(

let _53_1380 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _53_1362 v -> (match (_53_1362) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(

let _53_1370 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_53_1370) with
| (aa, _53_1368, env) -> begin
((env), ((((v), (((aa), (FStar_ToSMT_Term.Type_sort)))))::vars))
end))
end
| FStar_Util.Inr (x) -> begin
(

let _53_1377 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_53_1377) with
| (xx, _53_1375, env) -> begin
((env), ((((v), (((xx), (FStar_ToSMT_Term.Term_sort)))))::vars))
end))
end)
end)) ((env), ([]))))
in (match (_53_1380) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_1385) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _154_860 = (let _154_859 = (encode_const c)
in ((scrutinee), (_154_859)))
in (FStar_ToSMT_Term.mkEq _154_860))
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1409, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1418 -> (match (_53_1418) with
| (arg, _53_1417) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _154_863 = (FStar_ToSMT_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _154_863)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_53_1425) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
(((FStar_Util.Inr (x)), (scrutinee)))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
(((FStar_Util.Inl (a)), (scrutinee)))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_53_1442) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _53_1446, args) -> begin
(let _154_871 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _53_1454 -> (match (_53_1454) with
| (arg, _53_1453) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _154_870 = (FStar_ToSMT_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _154_870)))
end))))
in (FStar_All.pipe_right _154_871 FStar_List.flatten))
end))
in (

let pat_term = (fun _53_1457 -> (match (()) with
| () -> begin
(match (pat_exp_or_typ) with
| FStar_Util.Inl (t) -> begin
(encode_typ_term t env)
end
| FStar_Util.Inr (e) -> begin
(encode_exp e env)
end)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Absyn_Syntax.args  ->  env_t  ->  ((FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list * FStar_ToSMT_Term.decls_t) = (fun l env -> (

let _53_1487 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _53_1467 x -> (match (_53_1467) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _53_1472) -> begin
(

let _53_1476 = (encode_typ_term t env)
in (match (_53_1476) with
| (t, decls') -> begin
(((FStar_Util.Inl (t))::tms), ((FStar_List.append decls decls')))
end))
end
| (FStar_Util.Inr (e), _53_1480) -> begin
(

let _53_1484 = (encode_exp e env)
in (match (_53_1484) with
| (t, decls') -> begin
(((FStar_Util.Inr (t))::tms), ((FStar_List.append decls decls')))
end))
end)
end)) (([]), ([]))))
in (match (_53_1487) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_formula : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun phi env -> (

let _53_1493 = (encode_formula_with_labels phi env)
in (match (_53_1493) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
((t), (decls))
end
| _53_1496 -> begin
(failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (match ((let _154_886 = (FStar_Absyn_Util.unmeta_exp e)
in _154_886.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1513); FStar_Absyn_Syntax.tk = _53_1510; FStar_Absyn_Syntax.pos = _53_1508; FStar_Absyn_Syntax.fvs = _53_1506; FStar_Absyn_Syntax.uvs = _53_1504}, _53_1518) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1531); FStar_Absyn_Syntax.tk = _53_1528; FStar_Absyn_Syntax.pos = _53_1526; FStar_Absyn_Syntax.fvs = _53_1524; FStar_Absyn_Syntax.uvs = _53_1522}, (_53_1546)::((FStar_Util.Inr (hd), _53_1543))::((FStar_Util.Inr (tl), _53_1538))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _154_887 = (list_elements tl)
in (hd)::_154_887)
end
| _53_1551 -> begin
(

let _53_1552 = (FStar_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let v_or_t_pat = (fun p -> (match ((let _154_890 = (FStar_Absyn_Util.unmeta_exp p)
in _154_890.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1566); FStar_Absyn_Syntax.tk = _53_1563; FStar_Absyn_Syntax.pos = _53_1561; FStar_Absyn_Syntax.fvs = _53_1559; FStar_Absyn_Syntax.uvs = _53_1557}, ((FStar_Util.Inl (_53_1576), _53_1579))::((FStar_Util.Inr (e), _53_1573))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1594); FStar_Absyn_Syntax.tk = _53_1591; FStar_Absyn_Syntax.pos = _53_1589; FStar_Absyn_Syntax.fvs = _53_1587; FStar_Absyn_Syntax.uvs = _53_1585}, ((FStar_Util.Inl (t), _53_1601))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _53_1607 -> begin
(failwith "Unexpected pattern term")
end))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (match (elts) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1629); FStar_Absyn_Syntax.tk = _53_1626; FStar_Absyn_Syntax.pos = _53_1624; FStar_Absyn_Syntax.fvs = _53_1622; FStar_Absyn_Syntax.uvs = _53_1620}, ((FStar_Util.Inr (e), _53_1636))::[]); FStar_Absyn_Syntax.tk = _53_1618; FStar_Absyn_Syntax.pos = _53_1616; FStar_Absyn_Syntax.fvs = _53_1614; FStar_Absyn_Syntax.uvs = _53_1612})::[] when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _154_895 = (list_elements e)
in (FStar_All.pipe_right _154_895 (FStar_List.map (fun branch -> (let _154_894 = (list_elements branch)
in (FStar_All.pipe_right _154_894 (FStar_List.map v_or_t_pat)))))))
end
| _53_1645 -> begin
(let _154_896 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_154_896)::[])
end)))
in (

let _53_1688 = (match ((let _154_897 = (FStar_Absyn_Util.compress_typ t)
in _154_897.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _53_1654; FStar_Absyn_Syntax.pos = _53_1652; FStar_Absyn_Syntax.fvs = _53_1650; FStar_Absyn_Syntax.uvs = _53_1648}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (pre), _53_1673))::((FStar_Util.Inl (post), _53_1668))::((FStar_Util.Inr (pats), _53_1663))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _154_898 = (lemma_pats pats')
in ((binders), (pre), (post), (_154_898))))
end
| _53_1681 -> begin
(failwith "impos")
end)
end
| _53_1683 -> begin
(failwith "Impos")
end)
in (match (_53_1688) with
| (binders, pre, post, patterns) -> begin
(

let _53_1695 = (encode_binders None binders env)
in (match (_53_1695) with
| (vars, guards, env, decls, _53_1694) -> begin
(

let _53_1715 = (let _154_902 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _53_1712 = (let _154_901 = (FStar_All.pipe_right branch (FStar_List.map (fun uu___219 -> (match (uu___219) with
| (FStar_Util.Inl (t), _53_1701) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _53_1706) -> begin
(encode_exp e (

let _53_1708 = env
in {bindings = _53_1708.bindings; depth = _53_1708.depth; tcenv = _53_1708.tcenv; warn = _53_1708.warn; cache = _53_1708.cache; nolabels = _53_1708.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1708.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _154_901 FStar_List.unzip))
in (match (_53_1712) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _154_902 FStar_List.unzip))
in (match (_53_1715) with
| (pats, decls') -> begin
(

let decls' = (FStar_List.flatten decls')
in (

let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| (l)::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _154_905 = (let _154_904 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _154_904 e))
in (_154_905)::p))))
end
| _53_1725 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _154_911 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_154_911)::p))))
end
| ((x, FStar_ToSMT_Term.Term_sort))::vars -> begin
(let _154_913 = (let _154_912 = (FStar_ToSMT_Term.mkFreeV ((x), (FStar_ToSMT_Term.Term_sort)))
in (FStar_ToSMT_Term.mk_LexCons _154_912 tl))
in (aux _154_913 vars))
end
| _53_1737 -> begin
pats
end))
in (let _154_914 = (FStar_ToSMT_Term.mkFreeV (("Prims.LexTop"), (FStar_ToSMT_Term.Term_sort)))
in (aux _154_914 vars)))
end)
end)
in (

let env = (

let _53_1739 = env
in {bindings = _53_1739.bindings; depth = _53_1739.depth; tcenv = _53_1739.tcenv; warn = _53_1739.warn; cache = _53_1739.cache; nolabels = true; use_zfuel_name = _53_1739.use_zfuel_name; encode_non_total_function_typ = _53_1739.encode_non_total_function_typ})
in (

let _53_1744 = (let _154_915 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _154_915 env))
in (match (_53_1744) with
| (pre, decls'') -> begin
(

let _53_1747 = (let _154_916 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _154_916 env))
in (match (_53_1747) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _154_921 = (let _154_920 = (let _154_919 = (let _154_918 = (let _154_917 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in ((_154_917), (post)))
in (FStar_ToSMT_Term.mkImp _154_918))
in ((pats), (vars), (_154_919)))
in (FStar_ToSMT_Term.mkForall _154_920))
in ((_154_921), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * labels * FStar_ToSMT_Term.decls_t) = (fun phi env -> (

let enc = (fun f l -> (

let _53_1768 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(

let _53_1760 = (encode_typ_term t env)
in (match (_53_1760) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))
end
| FStar_Util.Inr (e) -> begin
(

let _53_1765 = (encode_exp e env)
in (match (_53_1765) with
| (e, decls') -> begin
(((FStar_List.append decls decls')), (e))
end))
end)) [] l)
in (match (_53_1768) with
| (decls, args) -> begin
(let _154_939 = (f args)
in ((_154_939), ([]), (decls)))
end)))
in (

let enc_prop_c = (fun f l -> (

let _53_1788 = (FStar_List.fold_right (fun t _53_1776 -> (match (_53_1776) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(

let _53_1782 = (encode_formula_with_labels t env)
in (match (_53_1782) with
| (phi, labs', decls') -> begin
(((phi)::phis), ((FStar_List.append labs' labs)), ((FStar_List.append decls' decls)))
end))
end
| _53_1784 -> begin
(failwith "Expected a formula")
end)
end)) l (([]), ([]), ([])))
in (match (_53_1788) with
| (phis, labs, decls) -> begin
(let _154_955 = (f phis)
in ((_154_955), (labs), (decls)))
end)))
in (

let const_op = (fun f _53_1791 -> ((f), ([]), ([])))
in (

let un_op = (fun f l -> (let _154_969 = (FStar_List.hd l)
in (FStar_All.pipe_left f _154_969)))
in (

let bin_op = (fun f uu___220 -> (match (uu___220) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _53_1802 -> begin
(failwith "Impossible")
end))
in (

let eq_op = (fun uu___221 -> (match (uu___221) with
| (_53_1810)::(_53_1808)::(e1)::(e2)::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (

let mk_imp = (fun uu___222 -> (match (uu___222) with
| ((FStar_Util.Inl (lhs), _53_1823))::((FStar_Util.Inl (rhs), _53_1818))::[] -> begin
(

let _53_1829 = (encode_formula_with_labels rhs env)
in (match (_53_1829) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_1832) -> begin
((l1), (labs1), (decls1))
end
| _53_1836 -> begin
(

let _53_1840 = (encode_formula_with_labels lhs env)
in (match (_53_1840) with
| (l2, labs2, decls2) -> begin
(let _154_983 = (FStar_ToSMT_Term.mkImp ((l2), (l1)))
in ((_154_983), ((FStar_List.append labs1 labs2)), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _53_1842 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun uu___223 -> (match (uu___223) with
| ((FStar_Util.Inl (guard), _53_1858))::((FStar_Util.Inl (_then), _53_1853))::((FStar_Util.Inl (_else), _53_1848))::[] -> begin
(

let _53_1864 = (encode_formula_with_labels guard env)
in (match (_53_1864) with
| (g, labs1, decls1) -> begin
(

let _53_1868 = (encode_formula_with_labels _then env)
in (match (_53_1868) with
| (t, labs2, decls2) -> begin
(

let _53_1872 = (encode_formula_with_labels _else env)
in (match (_53_1872) with
| (e, labs3, decls3) -> begin
(

let res = (FStar_ToSMT_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append labs1 (FStar_List.append labs2 labs3))), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _53_1875 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _154_995 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _154_995)))
in (

let connectives = (let _154_1056 = (let _154_1004 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in ((FStar_Absyn_Const.and_lid), (_154_1004)))
in (let _154_1055 = (let _154_1054 = (let _154_1010 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in ((FStar_Absyn_Const.or_lid), (_154_1010)))
in (let _154_1053 = (let _154_1052 = (let _154_1051 = (let _154_1019 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in ((FStar_Absyn_Const.iff_lid), (_154_1019)))
in (let _154_1050 = (let _154_1049 = (let _154_1048 = (let _154_1028 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in ((FStar_Absyn_Const.not_lid), (_154_1028)))
in (let _154_1047 = (let _154_1046 = (let _154_1034 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in ((FStar_Absyn_Const.eqT_lid), (_154_1034)))
in (_154_1046)::(((FStar_Absyn_Const.eq2_lid), (eq_op)))::(((FStar_Absyn_Const.true_lid), ((const_op FStar_ToSMT_Term.mkTrue))))::(((FStar_Absyn_Const.false_lid), ((const_op FStar_ToSMT_Term.mkFalse))))::[])
in (_154_1048)::_154_1047))
in (((FStar_Absyn_Const.ite_lid), (mk_ite)))::_154_1049)
in (_154_1051)::_154_1050))
in (((FStar_Absyn_Const.imp_lid), (mk_imp)))::_154_1052)
in (_154_1054)::_154_1053))
in (_154_1056)::_154_1055))
in (

let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(

let _53_1893 = (encode_formula_with_labels phi' env)
in (match (_53_1893) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
((phi), ([]), (decls))
end else begin
(

let lvar = (let _154_1059 = (varops.fresh "label")
in ((_154_1059), (FStar_ToSMT_Term.Bool_sort)))
in (

let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (

let lphi = (FStar_ToSMT_Term.mkOr ((lterm), (phi)))
in ((lphi), ((((lvar), (msg), (r)))::labs), (decls)))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1904; FStar_Absyn_Syntax.pos = _53_1902; FStar_Absyn_Syntax.fvs = _53_1900; FStar_Absyn_Syntax.uvs = _53_1898}, (_53_1919)::((FStar_Util.Inr (l), _53_1916))::((FStar_Util.Inl (phi), _53_1911))::[]) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(

let _53_1925 = (encode_exp l env)
in (match (_53_1925) with
| (e, decls) -> begin
(

let _53_1928 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_53_1928) with
| (f, decls') -> begin
((f), ([]), ((FStar_List.append decls decls')))
end))
end))
end else begin
((FStar_ToSMT_Term.mkTrue), ([]), ([]))
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _53_1936; FStar_Absyn_Syntax.pos = _53_1934; FStar_Absyn_Syntax.fvs = _53_1932; FStar_Absyn_Syntax.uvs = _53_1930}, (_53_1948)::((FStar_Util.Inl (phi), _53_1944))::tl) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(

let pat = (match (tl) with
| [] -> begin
None
end
| ((FStar_Util.Inr (pat), _53_1956))::[] -> begin
Some (pat)
end
| _53_1960 -> begin
(Prims.raise Bad_form)
end)
in (

let _53_1964 = (encode_function_type_as_formula None pat phi env)
in (match (_53_1964) with
| (f, decls) -> begin
((f), ([]), (decls))
end)))
end else begin
((FStar_ToSMT_Term.mkTrue), ([]), ([]))
end
end
| _53_1966 -> begin
(

let _53_1969 = (encode_typ_term phi env)
in (match (_53_1969) with
| (tt, decls) -> begin
(let _154_1060 = (FStar_ToSMT_Term.mk_Valid tt)
in ((_154_1060), ([]), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _53_1981 = (encode_binders None bs env)
in (match (_53_1981) with
| (vars, guards, env, decls, _53_1980) -> begin
(

let _53_2001 = (let _154_1072 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _53_1998 = (let _154_1071 = (FStar_All.pipe_right p (FStar_List.map (fun uu___224 -> (match (uu___224) with
| (FStar_Util.Inl (t), _53_1987) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _53_1992) -> begin
(encode_exp e (

let _53_1994 = env
in {bindings = _53_1994.bindings; depth = _53_1994.depth; tcenv = _53_1994.tcenv; warn = _53_1994.warn; cache = _53_1994.cache; nolabels = _53_1994.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _53_1994.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _154_1071 FStar_List.unzip))
in (match (_53_1998) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _154_1072 FStar_List.unzip))
in (match (_53_2001) with
| (pats, decls') -> begin
(

let _53_2005 = (encode_formula_with_labels body env)
in (match (_53_2005) with
| (body, labs, decls'') -> begin
(let _154_1073 = (FStar_ToSMT_Term.mk_and_l guards)
in ((vars), (pats), (_154_1073), (body), (labs), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls'')))))
end))
end))
end)))
in (

let _53_2006 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _154_1074 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _154_1074))
end else begin
()
end
in (

let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _53_2018 -> (match (_53_2018) with
| (l, _53_2017) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_53_2021, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(

let _53_2031 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _154_1091 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _154_1091))
end else begin
()
end
in (

let _53_2039 = (encode_q_body env vars pats body)
in (match (_53_2039) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _154_1094 = (let _154_1093 = (let _154_1092 = (FStar_ToSMT_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_154_1092)))
in (FStar_ToSMT_Term.mkForall _154_1093))
in ((_154_1094), (labs), (decls)))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(

let _53_2052 = (encode_q_body env vars pats body)
in (match (_53_2052) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _154_1097 = (let _154_1096 = (let _154_1095 = (FStar_ToSMT_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_154_1095)))
in (FStar_ToSMT_Term.mkExists _154_1096))
in ((_154_1097), (labs), (decls)))
end))
end))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _53_2058 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_53_2058) with
| (asym, a) -> begin
(

let _53_2061 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2061) with
| (xsym, x) -> begin
(

let _53_2064 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_53_2064) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (let _154_1132 = (let _154_1131 = (let _154_1130 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _154_1129 = (FStar_ToSMT_Term.abstr vars body)
in ((x), (_154_1130), (FStar_ToSMT_Term.Term_sort), (_154_1129), (None))))
in FStar_ToSMT_Term.DefineFun (_154_1131))
in (_154_1132)::[]))
in (

let quant = (fun vars body x -> (

let t1 = (let _154_1144 = (let _154_1143 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((x), (_154_1143)))
in (FStar_ToSMT_Term.mkApp _154_1144))
in (

let vname_decl = (let _154_1146 = (let _154_1145 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_154_1145), (FStar_ToSMT_Term.Term_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_154_1146))
in (let _154_1152 = (let _154_1151 = (let _154_1150 = (let _154_1149 = (let _154_1148 = (let _154_1147 = (FStar_ToSMT_Term.mkEq ((t1), (body)))
in ((((t1)::[])::[]), (vars), (_154_1147)))
in (FStar_ToSMT_Term.mkForall _154_1148))
in ((_154_1149), (None)))
in FStar_ToSMT_Term.Assume (_154_1150))
in (_154_1151)::[])
in (vname_decl)::_154_1152))))
in (

let def_or_quant = (fun vars body x -> if (FStar_Options.inline_arith ()) then begin
(deffun vars body x)
end else begin
(quant vars body x)
end)
in (

let axy = (((asym), (FStar_ToSMT_Term.Type_sort)))::(((xsym), (FStar_ToSMT_Term.Term_sort)))::(((ysym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_ToSMT_Term.Term_sort)))::(((ysym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let prims = (let _154_1318 = (let _154_1167 = (let _154_1166 = (let _154_1165 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1165))
in (def_or_quant axy _154_1166))
in ((FStar_Absyn_Const.op_Eq), (_154_1167)))
in (let _154_1317 = (let _154_1316 = (let _154_1174 = (let _154_1173 = (let _154_1172 = (let _154_1171 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in (FStar_ToSMT_Term.mkNot _154_1171))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1172))
in (def_or_quant axy _154_1173))
in ((FStar_Absyn_Const.op_notEq), (_154_1174)))
in (let _154_1315 = (let _154_1314 = (let _154_1183 = (let _154_1182 = (let _154_1181 = (let _154_1180 = (let _154_1179 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1178 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1179), (_154_1178))))
in (FStar_ToSMT_Term.mkLT _154_1180))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1181))
in (def_or_quant xy _154_1182))
in ((FStar_Absyn_Const.op_LT), (_154_1183)))
in (let _154_1313 = (let _154_1312 = (let _154_1192 = (let _154_1191 = (let _154_1190 = (let _154_1189 = (let _154_1188 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1187 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1188), (_154_1187))))
in (FStar_ToSMT_Term.mkLTE _154_1189))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1190))
in (def_or_quant xy _154_1191))
in ((FStar_Absyn_Const.op_LTE), (_154_1192)))
in (let _154_1311 = (let _154_1310 = (let _154_1201 = (let _154_1200 = (let _154_1199 = (let _154_1198 = (let _154_1197 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1196 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1197), (_154_1196))))
in (FStar_ToSMT_Term.mkGT _154_1198))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1199))
in (def_or_quant xy _154_1200))
in ((FStar_Absyn_Const.op_GT), (_154_1201)))
in (let _154_1309 = (let _154_1308 = (let _154_1210 = (let _154_1209 = (let _154_1208 = (let _154_1207 = (let _154_1206 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1205 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1206), (_154_1205))))
in (FStar_ToSMT_Term.mkGTE _154_1207))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1208))
in (def_or_quant xy _154_1209))
in ((FStar_Absyn_Const.op_GTE), (_154_1210)))
in (let _154_1307 = (let _154_1306 = (let _154_1219 = (let _154_1218 = (let _154_1217 = (let _154_1216 = (let _154_1215 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1214 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1215), (_154_1214))))
in (FStar_ToSMT_Term.mkSub _154_1216))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _154_1217))
in (def_or_quant xy _154_1218))
in ((FStar_Absyn_Const.op_Subtraction), (_154_1219)))
in (let _154_1305 = (let _154_1304 = (let _154_1226 = (let _154_1225 = (let _154_1224 = (let _154_1223 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _154_1223))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _154_1224))
in (def_or_quant qx _154_1225))
in ((FStar_Absyn_Const.op_Minus), (_154_1226)))
in (let _154_1303 = (let _154_1302 = (let _154_1235 = (let _154_1234 = (let _154_1233 = (let _154_1232 = (let _154_1231 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1230 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1231), (_154_1230))))
in (FStar_ToSMT_Term.mkAdd _154_1232))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _154_1233))
in (def_or_quant xy _154_1234))
in ((FStar_Absyn_Const.op_Addition), (_154_1235)))
in (let _154_1301 = (let _154_1300 = (let _154_1244 = (let _154_1243 = (let _154_1242 = (let _154_1241 = (let _154_1240 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1239 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1240), (_154_1239))))
in (FStar_ToSMT_Term.mkMul _154_1241))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _154_1242))
in (def_or_quant xy _154_1243))
in ((FStar_Absyn_Const.op_Multiply), (_154_1244)))
in (let _154_1299 = (let _154_1298 = (let _154_1253 = (let _154_1252 = (let _154_1251 = (let _154_1250 = (let _154_1249 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1248 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1249), (_154_1248))))
in (FStar_ToSMT_Term.mkDiv _154_1250))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _154_1251))
in (def_or_quant xy _154_1252))
in ((FStar_Absyn_Const.op_Division), (_154_1253)))
in (let _154_1297 = (let _154_1296 = (let _154_1262 = (let _154_1261 = (let _154_1260 = (let _154_1259 = (let _154_1258 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1257 = (FStar_ToSMT_Term.unboxInt y)
in ((_154_1258), (_154_1257))))
in (FStar_ToSMT_Term.mkMod _154_1259))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _154_1260))
in (def_or_quant xy _154_1261))
in ((FStar_Absyn_Const.op_Modulus), (_154_1262)))
in (let _154_1295 = (let _154_1294 = (let _154_1271 = (let _154_1270 = (let _154_1269 = (let _154_1268 = (let _154_1267 = (FStar_ToSMT_Term.unboxBool x)
in (let _154_1266 = (FStar_ToSMT_Term.unboxBool y)
in ((_154_1267), (_154_1266))))
in (FStar_ToSMT_Term.mkAnd _154_1268))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1269))
in (def_or_quant xy _154_1270))
in ((FStar_Absyn_Const.op_And), (_154_1271)))
in (let _154_1293 = (let _154_1292 = (let _154_1280 = (let _154_1279 = (let _154_1278 = (let _154_1277 = (let _154_1276 = (FStar_ToSMT_Term.unboxBool x)
in (let _154_1275 = (FStar_ToSMT_Term.unboxBool y)
in ((_154_1276), (_154_1275))))
in (FStar_ToSMT_Term.mkOr _154_1277))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1278))
in (def_or_quant xy _154_1279))
in ((FStar_Absyn_Const.op_Or), (_154_1280)))
in (let _154_1291 = (let _154_1290 = (let _154_1287 = (let _154_1286 = (let _154_1285 = (let _154_1284 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _154_1284))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_1285))
in (def_or_quant qx _154_1286))
in ((FStar_Absyn_Const.op_Negation), (_154_1287)))
in (_154_1290)::[])
in (_154_1292)::_154_1291))
in (_154_1294)::_154_1293))
in (_154_1296)::_154_1295))
in (_154_1298)::_154_1297))
in (_154_1300)::_154_1299))
in (_154_1302)::_154_1301))
in (_154_1304)::_154_1303))
in (_154_1306)::_154_1305))
in (_154_1308)::_154_1307))
in (_154_1310)::_154_1309))
in (_154_1312)::_154_1311))
in (_154_1314)::_154_1313))
in (_154_1316)::_154_1315))
in (_154_1318)::_154_1317))
in (

let mk = (fun l v -> (let _154_1350 = (FStar_All.pipe_right prims (FStar_List.filter (fun _53_2088 -> (match (_53_2088) with
| (l', _53_2087) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _154_1350 (FStar_List.collect (fun _53_2092 -> (match (_53_2092) with
| (_53_2090, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _53_2098 -> (match (_53_2098) with
| (l', _53_2097) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))))
end))
end))
end))


let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.decl Prims.list = (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let yy = (("y"), (FStar_ToSMT_Term.Term_sort))
in (

let y = (FStar_ToSMT_Term.mkFreeV yy)
in (

let mk_unit = (fun _53_2104 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _154_1382 = (let _154_1373 = (let _154_1372 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in ((_154_1372), (Some ("unit typing"))))
in FStar_ToSMT_Term.Assume (_154_1373))
in (let _154_1381 = (let _154_1380 = (let _154_1379 = (let _154_1378 = (let _154_1377 = (let _154_1376 = (let _154_1375 = (let _154_1374 = (FStar_ToSMT_Term.mkEq ((x), (FStar_ToSMT_Term.mk_Term_unit)))
in ((typing_pred), (_154_1374)))
in (FStar_ToSMT_Term.mkImp _154_1375))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_154_1376)))
in (mkForall_fuel _154_1377))
in ((_154_1378), (Some ("unit inversion"))))
in FStar_ToSMT_Term.Assume (_154_1379))
in (_154_1380)::[])
in (_154_1382)::_154_1381))))
in (

let mk_bool = (fun _53_2109 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_ToSMT_Term.Bool_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _154_1403 = (let _154_1392 = (let _154_1391 = (let _154_1390 = (let _154_1389 = (let _154_1388 = (let _154_1387 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_154_1387)))
in (FStar_ToSMT_Term.mkImp _154_1388))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_154_1389)))
in (mkForall_fuel _154_1390))
in ((_154_1391), (Some ("bool inversion"))))
in FStar_ToSMT_Term.Assume (_154_1392))
in (let _154_1402 = (let _154_1401 = (let _154_1400 = (let _154_1399 = (let _154_1398 = (let _154_1397 = (let _154_1394 = (let _154_1393 = (FStar_ToSMT_Term.boxBool b)
in (_154_1393)::[])
in (_154_1394)::[])
in (let _154_1396 = (let _154_1395 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _154_1395 tt))
in ((_154_1397), ((bb)::[]), (_154_1396))))
in (FStar_ToSMT_Term.mkForall _154_1398))
in ((_154_1399), (Some ("bool typing"))))
in FStar_ToSMT_Term.Assume (_154_1400))
in (_154_1401)::[])
in (_154_1403)::_154_1402))))))
in (

let mk_int = (fun _53_2116 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_ToSMT_Term.Int_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let bb = (("b"), (FStar_ToSMT_Term.Int_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let precedes = (let _154_1415 = (let _154_1414 = (let _154_1413 = (let _154_1412 = (let _154_1411 = (let _154_1410 = (FStar_ToSMT_Term.boxInt a)
in (let _154_1409 = (let _154_1408 = (FStar_ToSMT_Term.boxInt b)
in (_154_1408)::[])
in (_154_1410)::_154_1409))
in (tt)::_154_1411)
in (tt)::_154_1412)
in (("Prims.Precedes"), (_154_1413)))
in (FStar_ToSMT_Term.mkApp _154_1414))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _154_1415))
in (

let precedes_y_x = (let _154_1416 = (FStar_ToSMT_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _154_1416))
in (let _154_1458 = (let _154_1422 = (let _154_1421 = (let _154_1420 = (let _154_1419 = (let _154_1418 = (let _154_1417 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_154_1417)))
in (FStar_ToSMT_Term.mkImp _154_1418))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_154_1419)))
in (mkForall_fuel _154_1420))
in ((_154_1421), (Some ("int inversion"))))
in FStar_ToSMT_Term.Assume (_154_1422))
in (let _154_1457 = (let _154_1456 = (let _154_1430 = (let _154_1429 = (let _154_1428 = (let _154_1427 = (let _154_1424 = (let _154_1423 = (FStar_ToSMT_Term.boxInt b)
in (_154_1423)::[])
in (_154_1424)::[])
in (let _154_1426 = (let _154_1425 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _154_1425 tt))
in ((_154_1427), ((bb)::[]), (_154_1426))))
in (FStar_ToSMT_Term.mkForall _154_1428))
in ((_154_1429), (Some ("int typing"))))
in FStar_ToSMT_Term.Assume (_154_1430))
in (let _154_1455 = (let _154_1454 = (let _154_1453 = (let _154_1452 = (let _154_1451 = (let _154_1450 = (let _154_1449 = (let _154_1448 = (let _154_1447 = (let _154_1446 = (let _154_1445 = (let _154_1444 = (let _154_1433 = (let _154_1432 = (FStar_ToSMT_Term.unboxInt x)
in (let _154_1431 = (FStar_ToSMT_Term.mkInteger' (Prims.parse_int "0"))
in ((_154_1432), (_154_1431))))
in (FStar_ToSMT_Term.mkGT _154_1433))
in (let _154_1443 = (let _154_1442 = (let _154_1436 = (let _154_1435 = (FStar_ToSMT_Term.unboxInt y)
in (let _154_1434 = (FStar_ToSMT_Term.mkInteger' (Prims.parse_int "0"))
in ((_154_1435), (_154_1434))))
in (FStar_ToSMT_Term.mkGTE _154_1436))
in (let _154_1441 = (let _154_1440 = (let _154_1439 = (let _154_1438 = (FStar_ToSMT_Term.unboxInt y)
in (let _154_1437 = (FStar_ToSMT_Term.unboxInt x)
in ((_154_1438), (_154_1437))))
in (FStar_ToSMT_Term.mkLT _154_1439))
in (_154_1440)::[])
in (_154_1442)::_154_1441))
in (_154_1444)::_154_1443))
in (typing_pred_y)::_154_1445)
in (typing_pred)::_154_1446)
in (FStar_ToSMT_Term.mk_and_l _154_1447))
in ((_154_1448), (precedes_y_x)))
in (FStar_ToSMT_Term.mkImp _154_1449))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_154_1450)))
in (mkForall_fuel _154_1451))
in ((_154_1452), (Some ("well-founded ordering on nat (alt)"))))
in FStar_ToSMT_Term.Assume (_154_1453))
in (_154_1454)::[])
in (_154_1456)::_154_1455))
in (_154_1458)::_154_1457)))))))))))
in (

let mk_int_alias = (fun _53_2128 tt -> (let _154_1467 = (let _154_1466 = (let _154_1465 = (let _154_1464 = (let _154_1463 = (FStar_ToSMT_Term.mkApp ((FStar_Absyn_Const.int_lid.FStar_Ident.str), ([])))
in ((tt), (_154_1463)))
in (FStar_ToSMT_Term.mkEq _154_1464))
in ((_154_1465), (Some ("mapping to int; for now"))))
in FStar_ToSMT_Term.Assume (_154_1466))
in (_154_1467)::[]))
in (

let mk_str = (fun _53_2132 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_ToSMT_Term.String_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _154_1488 = (let _154_1477 = (let _154_1476 = (let _154_1475 = (let _154_1474 = (let _154_1473 = (let _154_1472 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in ((typing_pred), (_154_1472)))
in (FStar_ToSMT_Term.mkImp _154_1473))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_154_1474)))
in (mkForall_fuel _154_1475))
in ((_154_1476), (Some ("string inversion"))))
in FStar_ToSMT_Term.Assume (_154_1477))
in (let _154_1487 = (let _154_1486 = (let _154_1485 = (let _154_1484 = (let _154_1483 = (let _154_1482 = (let _154_1479 = (let _154_1478 = (FStar_ToSMT_Term.boxString b)
in (_154_1478)::[])
in (_154_1479)::[])
in (let _154_1481 = (let _154_1480 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _154_1480 tt))
in ((_154_1482), ((bb)::[]), (_154_1481))))
in (FStar_ToSMT_Term.mkForall _154_1483))
in ((_154_1484), (Some ("string typing"))))
in FStar_ToSMT_Term.Assume (_154_1485))
in (_154_1486)::[])
in (_154_1488)::_154_1487))))))
in (

let mk_ref = (fun reft_name _53_2140 -> (

let r = (("r"), (FStar_ToSMT_Term.Ref_sort))
in (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let refa = (let _154_1495 = (let _154_1494 = (let _154_1493 = (FStar_ToSMT_Term.mkFreeV aa)
in (_154_1493)::[])
in ((reft_name), (_154_1494)))
in (FStar_ToSMT_Term.mkApp _154_1495))
in (

let refb = (let _154_1498 = (let _154_1497 = (let _154_1496 = (FStar_ToSMT_Term.mkFreeV bb)
in (_154_1496)::[])
in ((reft_name), (_154_1497)))
in (FStar_ToSMT_Term.mkApp _154_1498))
in (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _154_1517 = (let _154_1504 = (let _154_1503 = (let _154_1502 = (let _154_1501 = (let _154_1500 = (let _154_1499 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_154_1499)))
in (FStar_ToSMT_Term.mkImp _154_1500))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_154_1501)))
in (mkForall_fuel _154_1502))
in ((_154_1503), (Some ("ref inversion"))))
in FStar_ToSMT_Term.Assume (_154_1504))
in (let _154_1516 = (let _154_1515 = (let _154_1514 = (let _154_1513 = (let _154_1512 = (let _154_1511 = (let _154_1510 = (let _154_1509 = (FStar_ToSMT_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _154_1508 = (let _154_1507 = (let _154_1506 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _154_1505 = (FStar_ToSMT_Term.mkFreeV bb)
in ((_154_1506), (_154_1505))))
in (FStar_ToSMT_Term.mkEq _154_1507))
in ((_154_1509), (_154_1508))))
in (FStar_ToSMT_Term.mkImp _154_1510))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_154_1511)))
in (mkForall_fuel' (Prims.parse_int "2") _154_1512))
in ((_154_1513), (Some ("ref typing is injective"))))
in FStar_ToSMT_Term.Assume (_154_1514))
in (_154_1515)::[])
in (_154_1517)::_154_1516))))))))))
in (

let mk_false_interp = (fun _53_2150 false_tm -> (

let valid = (FStar_ToSMT_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _154_1524 = (let _154_1523 = (let _154_1522 = (FStar_ToSMT_Term.mkIff ((FStar_ToSMT_Term.mkFalse), (valid)))
in ((_154_1522), (Some ("False interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1523))
in (_154_1524)::[])))
in (

let mk_and_interp = (fun conj _53_2156 -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _154_1531 = (let _154_1530 = (let _154_1529 = (FStar_ToSMT_Term.mkApp ((conj), ((a)::(b)::[])))
in (_154_1529)::[])
in (("Valid"), (_154_1530)))
in (FStar_ToSMT_Term.mkApp _154_1531))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _154_1538 = (let _154_1537 = (let _154_1536 = (let _154_1535 = (let _154_1534 = (let _154_1533 = (let _154_1532 = (FStar_ToSMT_Term.mkAnd ((valid_a), (valid_b)))
in ((_154_1532), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1533))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_154_1534)))
in (FStar_ToSMT_Term.mkForall _154_1535))
in ((_154_1536), (Some ("/\\ interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1537))
in (_154_1538)::[])))))))))
in (

let mk_or_interp = (fun disj _53_2167 -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _154_1545 = (let _154_1544 = (let _154_1543 = (FStar_ToSMT_Term.mkApp ((disj), ((a)::(b)::[])))
in (_154_1543)::[])
in (("Valid"), (_154_1544)))
in (FStar_ToSMT_Term.mkApp _154_1545))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _154_1552 = (let _154_1551 = (let _154_1550 = (let _154_1549 = (let _154_1548 = (let _154_1547 = (let _154_1546 = (FStar_ToSMT_Term.mkOr ((valid_a), (valid_b)))
in ((_154_1546), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1547))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_154_1548)))
in (FStar_ToSMT_Term.mkForall _154_1549))
in ((_154_1550), (Some ("\\/ interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1551))
in (_154_1552)::[])))))))))
in (

let mk_eq2_interp = (fun eq2 tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let yy = (("y"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let y = (FStar_ToSMT_Term.mkFreeV yy)
in (

let valid = (let _154_1559 = (let _154_1558 = (let _154_1557 = (FStar_ToSMT_Term.mkApp ((eq2), ((a)::(b)::(x)::(y)::[])))
in (_154_1557)::[])
in (("Valid"), (_154_1558)))
in (FStar_ToSMT_Term.mkApp _154_1559))
in (let _154_1566 = (let _154_1565 = (let _154_1564 = (let _154_1563 = (let _154_1562 = (let _154_1561 = (let _154_1560 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in ((_154_1560), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1561))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_154_1562)))
in (FStar_ToSMT_Term.mkForall _154_1563))
in ((_154_1564), (Some ("Eq2 interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1565))
in (_154_1566)::[])))))))))))
in (

let mk_imp_interp = (fun imp tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _154_1573 = (let _154_1572 = (let _154_1571 = (FStar_ToSMT_Term.mkApp ((imp), ((a)::(b)::[])))
in (_154_1571)::[])
in (("Valid"), (_154_1572)))
in (FStar_ToSMT_Term.mkApp _154_1573))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _154_1580 = (let _154_1579 = (let _154_1578 = (let _154_1577 = (let _154_1576 = (let _154_1575 = (let _154_1574 = (FStar_ToSMT_Term.mkImp ((valid_a), (valid_b)))
in ((_154_1574), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1575))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_154_1576)))
in (FStar_ToSMT_Term.mkForall _154_1577))
in ((_154_1578), (Some ("==> interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1579))
in (_154_1580)::[])))))))))
in (

let mk_iff_interp = (fun iff tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _154_1587 = (let _154_1586 = (let _154_1585 = (FStar_ToSMT_Term.mkApp ((iff), ((a)::(b)::[])))
in (_154_1585)::[])
in (("Valid"), (_154_1586)))
in (FStar_ToSMT_Term.mkApp _154_1587))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _154_1594 = (let _154_1593 = (let _154_1592 = (let _154_1591 = (let _154_1590 = (let _154_1589 = (let _154_1588 = (FStar_ToSMT_Term.mkIff ((valid_a), (valid_b)))
in ((_154_1588), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1589))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_154_1590)))
in (FStar_ToSMT_Term.mkForall _154_1591))
in ((_154_1592), (Some ("<==> interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1593))
in (_154_1594)::[])))))))))
in (

let mk_forall_interp = (fun for_all tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid = (let _154_1601 = (let _154_1600 = (let _154_1599 = (FStar_ToSMT_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_154_1599)::[])
in (("Valid"), (_154_1600)))
in (FStar_ToSMT_Term.mkApp _154_1601))
in (

let valid_b_x = (let _154_1604 = (let _154_1603 = (let _154_1602 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_154_1602)::[])
in (("Valid"), (_154_1603)))
in (FStar_ToSMT_Term.mkApp _154_1604))
in (let _154_1618 = (let _154_1617 = (let _154_1616 = (let _154_1615 = (let _154_1614 = (let _154_1613 = (let _154_1612 = (let _154_1611 = (let _154_1610 = (let _154_1606 = (let _154_1605 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_154_1605)::[])
in (_154_1606)::[])
in (let _154_1609 = (let _154_1608 = (let _154_1607 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in ((_154_1607), (valid_b_x)))
in (FStar_ToSMT_Term.mkImp _154_1608))
in ((_154_1610), ((xx)::[]), (_154_1609))))
in (FStar_ToSMT_Term.mkForall _154_1611))
in ((_154_1612), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1613))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_154_1614)))
in (FStar_ToSMT_Term.mkForall _154_1615))
in ((_154_1616), (Some ("forall interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1617))
in (_154_1618)::[]))))))))))
in (

let mk_exists_interp = (fun for_all tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid = (let _154_1625 = (let _154_1624 = (let _154_1623 = (FStar_ToSMT_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_154_1623)::[])
in (("Valid"), (_154_1624)))
in (FStar_ToSMT_Term.mkApp _154_1625))
in (

let valid_b_x = (let _154_1628 = (let _154_1627 = (let _154_1626 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_154_1626)::[])
in (("Valid"), (_154_1627)))
in (FStar_ToSMT_Term.mkApp _154_1628))
in (let _154_1642 = (let _154_1641 = (let _154_1640 = (let _154_1639 = (let _154_1638 = (let _154_1637 = (let _154_1636 = (let _154_1635 = (let _154_1634 = (let _154_1630 = (let _154_1629 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_154_1629)::[])
in (_154_1630)::[])
in (let _154_1633 = (let _154_1632 = (let _154_1631 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in ((_154_1631), (valid_b_x)))
in (FStar_ToSMT_Term.mkImp _154_1632))
in ((_154_1634), ((xx)::[]), (_154_1633))))
in (FStar_ToSMT_Term.mkExists _154_1635))
in ((_154_1636), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1637))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_154_1638)))
in (FStar_ToSMT_Term.mkForall _154_1639))
in ((_154_1640), (Some ("exists interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1641))
in (_154_1642)::[]))))))))))
in (

let mk_foralltyp_interp = (fun for_all tt -> (

let kk = (("k"), (FStar_ToSMT_Term.Kind_sort))
in (

let aa = (("aa"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("bb"), (FStar_ToSMT_Term.Term_sort))
in (

let k = (FStar_ToSMT_Term.mkFreeV kk)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _154_1649 = (let _154_1648 = (let _154_1647 = (FStar_ToSMT_Term.mkApp ((for_all), ((k)::(a)::[])))
in (_154_1647)::[])
in (("Valid"), (_154_1648)))
in (FStar_ToSMT_Term.mkApp _154_1649))
in (

let valid_a_b = (let _154_1652 = (let _154_1651 = (let _154_1650 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_154_1650)::[])
in (("Valid"), (_154_1651)))
in (FStar_ToSMT_Term.mkApp _154_1652))
in (let _154_1666 = (let _154_1665 = (let _154_1664 = (let _154_1663 = (let _154_1662 = (let _154_1661 = (let _154_1660 = (let _154_1659 = (let _154_1658 = (let _154_1654 = (let _154_1653 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_154_1653)::[])
in (_154_1654)::[])
in (let _154_1657 = (let _154_1656 = (let _154_1655 = (FStar_ToSMT_Term.mk_HasKind b k)
in ((_154_1655), (valid_a_b)))
in (FStar_ToSMT_Term.mkImp _154_1656))
in ((_154_1658), ((bb)::[]), (_154_1657))))
in (FStar_ToSMT_Term.mkForall _154_1659))
in ((_154_1660), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1661))
in ((((valid)::[])::[]), ((kk)::(aa)::[]), (_154_1662)))
in (FStar_ToSMT_Term.mkForall _154_1663))
in ((_154_1664), (Some ("ForallTyp interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1665))
in (_154_1666)::[]))))))))))
in (

let mk_existstyp_interp = (fun for_some tt -> (

let kk = (("k"), (FStar_ToSMT_Term.Kind_sort))
in (

let aa = (("aa"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("bb"), (FStar_ToSMT_Term.Term_sort))
in (

let k = (FStar_ToSMT_Term.mkFreeV kk)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _154_1673 = (let _154_1672 = (let _154_1671 = (FStar_ToSMT_Term.mkApp ((for_some), ((k)::(a)::[])))
in (_154_1671)::[])
in (("Valid"), (_154_1672)))
in (FStar_ToSMT_Term.mkApp _154_1673))
in (

let valid_a_b = (let _154_1676 = (let _154_1675 = (let _154_1674 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_154_1674)::[])
in (("Valid"), (_154_1675)))
in (FStar_ToSMT_Term.mkApp _154_1676))
in (let _154_1690 = (let _154_1689 = (let _154_1688 = (let _154_1687 = (let _154_1686 = (let _154_1685 = (let _154_1684 = (let _154_1683 = (let _154_1682 = (let _154_1678 = (let _154_1677 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_154_1677)::[])
in (_154_1678)::[])
in (let _154_1681 = (let _154_1680 = (let _154_1679 = (FStar_ToSMT_Term.mk_HasKind b k)
in ((_154_1679), (valid_a_b)))
in (FStar_ToSMT_Term.mkImp _154_1680))
in ((_154_1682), ((bb)::[]), (_154_1681))))
in (FStar_ToSMT_Term.mkExists _154_1683))
in ((_154_1684), (valid)))
in (FStar_ToSMT_Term.mkIff _154_1685))
in ((((valid)::[])::[]), ((kk)::(aa)::[]), (_154_1686)))
in (FStar_ToSMT_Term.mkForall _154_1687))
in ((_154_1688), (Some ("ExistsTyp interpretation"))))
in FStar_ToSMT_Term.Assume (_154_1689))
in (_154_1690)::[]))))))))))
in (

let prims = (((FStar_Absyn_Const.unit_lid), (mk_unit)))::(((FStar_Absyn_Const.bool_lid), (mk_bool)))::(((FStar_Absyn_Const.int_lid), (mk_int)))::(((FStar_Absyn_Const.string_lid), (mk_str)))::(((FStar_Absyn_Const.ref_lid), (mk_ref)))::(((FStar_Absyn_Const.false_lid), (mk_false_interp)))::(((FStar_Absyn_Const.and_lid), (mk_and_interp)))::(((FStar_Absyn_Const.or_lid), (mk_or_interp)))::(((FStar_Absyn_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Absyn_Const.imp_lid), (mk_imp_interp)))::(((FStar_Absyn_Const.iff_lid), (mk_iff_interp)))::(((FStar_Absyn_Const.forall_lid), (mk_forall_interp)))::(((FStar_Absyn_Const.exists_lid), (mk_exists_interp)))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _53_2260 -> (match (_53_2260) with
| (l, _53_2259) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_53_2263, f) -> begin
(f s tt)
end)))))))))))))))))))))))


let rec encode_sigelt : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (

let _53_2269 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _154_1821 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _154_1821))
end else begin
()
end
in (

let nm = (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (

let _53_2277 = (encode_sigelt' env se)
in (match (_53_2277) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _154_1824 = (let _154_1823 = (let _154_1822 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_154_1822))
in (_154_1823)::[])
in ((_154_1824), (e)))
end
| _53_2280 -> begin
(let _154_1831 = (let _154_1830 = (let _154_1826 = (let _154_1825 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_154_1825))
in (_154_1826)::g)
in (let _154_1829 = (let _154_1828 = (let _154_1827 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_154_1827))
in (_154_1828)::[])
in (FStar_List.append _154_1830 _154_1829)))
in ((_154_1831), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Ident.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Ident.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.all_")))
in (

let encode_top_level_val = (fun env lid t quals -> (

let tt = (whnf env t)
in (

let _53_2293 = (encode_free_var env lid t tt quals)
in (match (_53_2293) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _154_1845 = (let _154_1844 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _154_1844))
in ((_154_1845), (env)))
end else begin
((decls), (env))
end
end))))
in (

let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _53_2300 lb -> (match (_53_2300) with
| (decls, env) -> begin
(

let _53_2304 = (let _154_1854 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _154_1854 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_53_2304) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_53_2306, _53_2308, _53_2310, _53_2312, (FStar_Absyn_Syntax.Effect)::[], _53_2316) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2321, _53_2323, _53_2325, _53_2327, _53_2329) when (should_skip lid) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _53_2334, _53_2336, _53_2338, _53_2340, _53_2342) when (FStar_Ident.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(

let _53_2348 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2348) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _154_1857 = (let _154_1856 = (let _154_1855 = (FStar_ToSMT_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_154_1855)::[])
in (("Valid"), (_154_1856)))
in (FStar_ToSMT_Term.mkApp _154_1857))
in (

let decls = (let _154_1865 = (let _154_1864 = (let _154_1863 = (let _154_1862 = (let _154_1861 = (let _154_1860 = (let _154_1859 = (let _154_1858 = (FStar_ToSMT_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_154_1858)))
in (FStar_ToSMT_Term.mkEq _154_1859))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_154_1860)))
in (FStar_ToSMT_Term.mkForall _154_1861))
in ((_154_1862), (Some ("b2t def"))))
in FStar_ToSMT_Term.Assume (_154_1863))
in (_154_1864)::[])
in (FStar_ToSMT_Term.DeclFun (((tname), ((FStar_ToSMT_Term.Term_sort)::[]), (FStar_ToSMT_Term.Type_sort), (None))))::_154_1865)
in ((decls), (env))))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _53_2356, t, tags, _53_2360) -> begin
(

let _53_2366 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_53_2366) with
| (tname, ttok, env) -> begin
(

let _53_2375 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
(((FStar_List.append tps tps')), (body))
end
| _53_2372 -> begin
((tps), (t))
end)
in (match (_53_2375) with
| (tps, t) -> begin
(

let _53_2382 = (encode_binders None tps env)
in (match (_53_2382) with
| (vars, guards, env', binder_decls, _53_2381) -> begin
(

let tok_app = (let _154_1866 = (FStar_ToSMT_Term.mkApp ((ttok), ([])))
in (mk_ApplyT _154_1866 vars))
in (

let tok_decl = FStar_ToSMT_Term.DeclFun (((ttok), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let app = (let _154_1868 = (let _154_1867 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((tname), (_154_1867)))
in (FStar_ToSMT_Term.mkApp _154_1868))
in (

let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _53_2388 -> begin
(let _154_1870 = (let _154_1869 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ttok), (FStar_ToSMT_Term.Type_sort)) _154_1869))
in (_154_1870)::[])
end)
in (

let decls = (let _154_1881 = (let _154_1873 = (let _154_1872 = (let _154_1871 = (FStar_List.map Prims.snd vars)
in ((tname), (_154_1871), (FStar_ToSMT_Term.Type_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_154_1872))
in (_154_1873)::(tok_decl)::[])
in (let _154_1880 = (let _154_1879 = (let _154_1878 = (let _154_1877 = (let _154_1876 = (let _154_1875 = (let _154_1874 = (FStar_ToSMT_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (vars), (_154_1874)))
in (FStar_ToSMT_Term.mkForall _154_1875))
in ((_154_1876), (Some ("name-token correspondence"))))
in FStar_ToSMT_Term.Assume (_154_1877))
in (_154_1878)::[])
in (FStar_List.append fresh_tok _154_1879))
in (FStar_List.append _154_1881 _154_1880)))
in (

let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (

let _53_2400 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun uu___225 -> (match (uu___225) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _53_2395 -> begin
false
end)))) then begin
(let _154_1884 = (FStar_ToSMT_Term.mk_Valid app)
in (let _154_1883 = (encode_formula t env')
in ((_154_1884), (_154_1883))))
end else begin
(let _154_1885 = (encode_typ_term t env')
in ((app), (_154_1885)))
end
in (match (_53_2400) with
| (def, (body, decls1)) -> begin
(

let abbrev_def = (let _154_1892 = (let _154_1891 = (let _154_1890 = (let _154_1889 = (let _154_1888 = (let _154_1887 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _154_1886 = (FStar_ToSMT_Term.mkEq ((def), (body)))
in ((_154_1887), (_154_1886))))
in (FStar_ToSMT_Term.mkImp _154_1888))
in ((((def)::[])::[]), (vars), (_154_1889)))
in (FStar_ToSMT_Term.mkForall _154_1890))
in ((_154_1891), (Some ("abbrev. elimination"))))
in FStar_ToSMT_Term.Assume (_154_1892))
in (

let kindingAx = (

let _53_2404 = (let _154_1893 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _154_1893 env' app))
in (match (_53_2404) with
| (k, decls) -> begin
(let _154_1901 = (let _154_1900 = (let _154_1899 = (let _154_1898 = (let _154_1897 = (let _154_1896 = (let _154_1895 = (let _154_1894 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_154_1894), (k)))
in (FStar_ToSMT_Term.mkImp _154_1895))
in ((((app)::[])::[]), (vars), (_154_1896)))
in (FStar_ToSMT_Term.mkForall _154_1897))
in ((_154_1898), (Some ("abbrev. kinding"))))
in FStar_ToSMT_Term.Assume (_154_1899))
in (_154_1900)::[])
in (FStar_List.append decls _154_1901))
end))
in (

let g = (let _154_1905 = (let _154_1904 = (let _154_1903 = (let _154_1902 = (primitive_type_axioms lid tname app)
in (FStar_List.append ((abbrev_def)::kindingAx) _154_1902))
in (FStar_List.append decls1 _154_1903))
in (FStar_List.append decls _154_1904))
in (FStar_List.append binder_decls _154_1905))
in ((g), (env)))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _53_2411) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
(([]), (env))
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _53_2417, _53_2419) -> begin
(

let _53_2424 = (encode_formula f env)
in (match (_53_2424) with
| (f, decls) -> begin
(

let g = (let _154_1910 = (let _154_1909 = (let _154_1908 = (let _154_1907 = (let _154_1906 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _154_1906))
in Some (_154_1907))
in ((f), (_154_1908)))
in FStar_ToSMT_Term.Assume (_154_1909))
in (_154_1910)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2430, datas, quals, _53_2434) when (FStar_Ident.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(

let _53_2440 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2440) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _53_2443, _53_2445, _53_2447, _53_2449, _53_2451, _53_2453) when ((FStar_Ident.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Ident.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(

let tname = t.FStar_Ident.str
in (

let tsym = (FStar_ToSMT_Term.mkFreeV ((tname), (FStar_ToSMT_Term.Type_sort)))
in (

let decl = FStar_ToSMT_Term.DeclFun (((tname), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (let _154_1912 = (let _154_1911 = (primitive_type_axioms t tname tsym)
in (decl)::_154_1911)
in ((_154_1912), ((push_free_tvar env t tname (Some (tsym)))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _53_2463, datas, quals, _53_2467) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___226 -> (match (uu___226) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _53_2474 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _53_2484 = c
in (match (_53_2484) with
| (name, args, _53_2481, _53_2483) -> begin
(let _154_1918 = (let _154_1917 = (let _154_1916 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_154_1916), (FStar_ToSMT_Term.Type_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_154_1917))
in (_154_1918)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = (Prims.parse_int "0")) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _154_1924 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _154_1924 FStar_Option.isNone)))))) then begin
[]
end else begin
(

let _53_2491 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2491) with
| (xxsym, xx) -> begin
(

let _53_2534 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _53_2494 l -> (match (_53_2494) with
| (out, decls) -> begin
(

let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (

let _53_2504 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
((formals), ((FStar_Absyn_Util.comp_result res)))
end
| None -> begin
(([]), (data_t))
end)
in (match (_53_2504) with
| (args, res) -> begin
(

let indices = (match ((let _154_1927 = (FStar_Absyn_Util.compress_typ res)
in _154_1927.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_53_2506, indices) -> begin
indices
end
| _53_2511 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _154_1932 = (let _154_1931 = (let _154_1930 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in ((_154_1930), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _154_1931))
in (push_typ_var env a.FStar_Absyn_Syntax.v _154_1932))
end
| FStar_Util.Inr (x) -> begin
(let _154_1935 = (let _154_1934 = (let _154_1933 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in ((_154_1933), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _154_1934))
in (push_term_var env x.FStar_Absyn_Syntax.v _154_1935))
end)) env))
in (

let _53_2522 = (encode_args indices env)
in (match (_53_2522) with
| (indices, decls') -> begin
(

let _53_2523 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _154_1942 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _154_1939 = (let _154_1938 = (FStar_ToSMT_Term.mkFreeV v)
in ((_154_1938), (a)))
in (FStar_ToSMT_Term.mkEq _154_1939))
end
| FStar_Util.Inr (a) -> begin
(let _154_1941 = (let _154_1940 = (FStar_ToSMT_Term.mkFreeV v)
in ((_154_1940), (a)))
in (FStar_ToSMT_Term.mkEq _154_1941))
end)) vars indices)
in (FStar_All.pipe_right _154_1942 FStar_ToSMT_Term.mk_and_l))
in (let _154_1947 = (let _154_1946 = (let _154_1945 = (let _154_1944 = (let _154_1943 = (mk_data_tester env l xx)
in ((_154_1943), (eqs)))
in (FStar_ToSMT_Term.mkAnd _154_1944))
in ((out), (_154_1945)))
in (FStar_ToSMT_Term.mkOr _154_1946))
in ((_154_1947), ((FStar_List.append decls decls'))))))
end))))
end)))
end)) ((FStar_ToSMT_Term.mkFalse), ([]))))
in (match (_53_2534) with
| (data_ax, decls) -> begin
(

let _53_2537 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2537) with
| (ffsym, ff) -> begin
(

let xx_has_type = (let _154_1948 = (FStar_ToSMT_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_ToSMT_Term.mk_HasTypeFuel _154_1948 xx tapp))
in (let _154_1955 = (let _154_1954 = (let _154_1953 = (let _154_1952 = (let _154_1951 = (let _154_1950 = (add_fuel ((ffsym), (FStar_ToSMT_Term.Fuel_sort)) ((((xxsym), (FStar_ToSMT_Term.Term_sort)))::vars))
in (let _154_1949 = (FStar_ToSMT_Term.mkImp ((xx_has_type), (data_ax)))
in ((((xx_has_type)::[])::[]), (_154_1950), (_154_1949))))
in (FStar_ToSMT_Term.mkForall _154_1951))
in ((_154_1952), (Some ("inversion axiom"))))
in FStar_ToSMT_Term.Assume (_154_1953))
in (_154_1954)::[])
in (FStar_List.append decls _154_1955)))
end))
end))
end))
end)
in (

let k = (FStar_Absyn_Util.close_kind tps k)
in (

let _53_2549 = (match ((let _154_1956 = (FStar_Absyn_Util.compress_kind k)
in _154_1956.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
((true), (bs), (res))
end
| _53_2545 -> begin
((false), ([]), (k))
end)
in (match (_53_2549) with
| (is_kind_arrow, formals, res) -> begin
(

let _53_2556 = (encode_binders None formals env)
in (match (_53_2556) with
| (vars, guards, env', binder_decls, _53_2555) -> begin
(

let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun uu___227 -> (match (uu___227) with
| FStar_Absyn_Syntax.Projector (_53_2562) -> begin
true
end
| _53_2565 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(

let rec projectee = (fun i uu___228 -> (match (uu___228) with
| [] -> begin
i
end
| (f)::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_53_2580) -> begin
(projectee (i + (Prims.parse_int "1")) tl)
end
| FStar_Util.Inr (x) -> begin
if (x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "projectee") then begin
i
end else begin
(projectee (i + (Prims.parse_int "1")) tl)
end
end)
end))
in (

let projectee_pos = (projectee (Prims.parse_int "0") formals)
in (

let _53_2595 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_53_2586, (xx)::suffix) -> begin
((xx), (suffix))
end
| _53_2592 -> begin
(failwith "impossible")
end)
in (match (_53_2595) with
| (xx, suffix) -> begin
(

let dproj_app = (let _154_1970 = (let _154_1969 = (let _154_1968 = (mk_typ_projector_name d a)
in (let _154_1967 = (let _154_1966 = (FStar_ToSMT_Term.mkFreeV xx)
in (_154_1966)::[])
in ((_154_1968), (_154_1967))))
in (FStar_ToSMT_Term.mkApp _154_1969))
in (mk_ApplyT _154_1970 suffix))
in (let _154_1975 = (let _154_1974 = (let _154_1973 = (let _154_1972 = (let _154_1971 = (FStar_ToSMT_Term.mkEq ((tapp), (dproj_app)))
in ((((tapp)::[])::[]), (vars), (_154_1971)))
in (FStar_ToSMT_Term.mkForall _154_1972))
in ((_154_1973), (Some ("projector axiom"))))
in FStar_ToSMT_Term.Assume (_154_1974))
in (_154_1975)::[]))
end))))
end
| _53_2598 -> begin
[]
end))
in (

let pretype_axioms = (fun tapp vars -> (

let _53_2604 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_53_2604) with
| (xxsym, xx) -> begin
(

let _53_2607 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2607) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _154_1988 = (let _154_1987 = (let _154_1986 = (let _154_1985 = (let _154_1984 = (let _154_1983 = (let _154_1982 = (let _154_1981 = (let _154_1980 = (FStar_ToSMT_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_154_1980)))
in (FStar_ToSMT_Term.mkEq _154_1981))
in ((xx_has_type), (_154_1982)))
in (FStar_ToSMT_Term.mkImp _154_1983))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_ToSMT_Term.Term_sort)))::(((ffsym), (FStar_ToSMT_Term.Fuel_sort)))::vars), (_154_1984)))
in (FStar_ToSMT_Term.mkForall _154_1985))
in ((_154_1986), (Some ("pretyping"))))
in FStar_ToSMT_Term.Assume (_154_1987))
in (_154_1988)::[]))
end))
end)))
in (

let _53_2612 = (new_typ_constant_and_tok_from_lid env t)
in (match (_53_2612) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_ToSMT_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (

let tapp = (let _154_1990 = (let _154_1989 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((tname), (_154_1989)))
in (FStar_ToSMT_Term.mkApp _154_1990))
in (

let _53_2633 = (

let tname_decl = (let _154_1994 = (let _154_1993 = (FStar_All.pipe_right vars (FStar_List.map (fun _53_2618 -> (match (_53_2618) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _154_1992 = (varops.next_id ())
in ((tname), (_154_1993), (FStar_ToSMT_Term.Type_sort), (_154_1992))))
in (constructor_or_logic_type_decl _154_1994))
in (

let _53_2630 = (match (vars) with
| [] -> begin
(let _154_1998 = (let _154_1997 = (let _154_1996 = (FStar_ToSMT_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _154_1995 -> Some (_154_1995)) _154_1996))
in (push_free_tvar env t tname _154_1997))
in (([]), (_154_1998)))
end
| _53_2622 -> begin
(

let ttok_decl = FStar_ToSMT_Term.DeclFun (((ttok), ([]), (FStar_ToSMT_Term.Type_sort), (Some ("token"))))
in (

let ttok_fresh = (let _154_1999 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ttok), (FStar_ToSMT_Term.Type_sort)) _154_1999))
in (

let ttok_app = (mk_ApplyT ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _154_2003 = (let _154_2002 = (let _154_2001 = (let _154_2000 = (FStar_ToSMT_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_154_2000)))
in (FStar_ToSMT_Term.mkForall' _154_2001))
in ((_154_2002), (Some ("name-token correspondence"))))
in FStar_ToSMT_Term.Assume (_154_2003))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_53_2630) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_53_2633) with
| (decls, env) -> begin
(

let kindingAx = (

let _53_2636 = (encode_knd res env' tapp)
in (match (_53_2636) with
| (k, decls) -> begin
(

let karr = if is_kind_arrow then begin
(let _154_2007 = (let _154_2006 = (let _154_2005 = (let _154_2004 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _154_2004))
in ((_154_2005), (Some ("kinding"))))
in FStar_ToSMT_Term.Assume (_154_2006))
in (_154_2007)::[])
end else begin
[]
end
in (let _154_2014 = (let _154_2013 = (let _154_2012 = (let _154_2011 = (let _154_2010 = (let _154_2009 = (let _154_2008 = (FStar_ToSMT_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_154_2008)))
in (FStar_ToSMT_Term.mkForall _154_2009))
in ((_154_2010), (Some ("kinding"))))
in FStar_ToSMT_Term.Assume (_154_2011))
in (_154_2012)::[])
in (FStar_List.append karr _154_2013))
in (FStar_List.append decls _154_2014)))
end))
in (

let aux = if is_logical then begin
(let _154_2015 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _154_2015))
end else begin
(let _154_2022 = (let _154_2021 = (primitive_type_axioms t tname tapp)
in (let _154_2020 = (let _154_2019 = (inversion_axioms tapp vars)
in (let _154_2018 = (let _154_2017 = (projection_axioms tapp vars)
in (let _154_2016 = (pretype_axioms tapp vars)
in (FStar_List.append _154_2017 _154_2016)))
in (FStar_List.append _154_2019 _154_2018)))
in (FStar_List.append _154_2021 _154_2020)))
in (FStar_List.append kindingAx _154_2022))
end
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _53_2643, _53_2645, _53_2647, _53_2649, _53_2651) when (FStar_Ident.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_53_2657, tps, _53_2660), quals, _53_2664, drange) -> begin
(

let t = (let _154_2024 = (FStar_List.map (fun _53_2671 -> (match (_53_2671) with
| (x, _53_2670) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _154_2024 t))
in (

let _53_2676 = (new_term_constant_and_tok_from_lid env d)
in (match (_53_2676) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_ToSMT_Term.mkApp ((ddtok), ([])))
in (

let _53_2685 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
((f), ((FStar_Absyn_Util.comp_result c)))
end
| None -> begin
(([]), (t))
end)
in (match (_53_2685) with
| (formals, t_res) -> begin
(

let _53_2688 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_53_2688) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_ToSMT_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _53_2695 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2695) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun uu___229 -> (match (uu___229) with
| FStar_Util.Inl (a) -> begin
(let _154_2026 = (mk_typ_projector_name d a)
in ((_154_2026), (FStar_ToSMT_Term.Type_sort)))
end
| FStar_Util.Inr (x) -> begin
(let _154_2027 = (mk_term_projector_name d x)
in ((_154_2027), (FStar_ToSMT_Term.Term_sort)))
end))))
in (

let datacons = (let _154_2029 = (let _154_2028 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_ToSMT_Term.Term_sort), (_154_2028)))
in (FStar_All.pipe_right _154_2029 FStar_ToSMT_Term.constructor_to_decl))
in (

let app = (mk_ApplyE ddtok_tm vars)
in (

let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _53_2709 = (encode_typ_pred None t env ddtok_tm)
in (match (_53_2709) with
| (tok_typing, decls3) -> begin
(

let _53_2716 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_53_2716) with
| (vars', guards', env'', decls_formals, _53_2715) -> begin
(

let _53_2721 = (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_53_2721) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _53_2725 -> begin
(let _154_2031 = (let _154_2030 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ddtok), (FStar_ToSMT_Term.Term_sort)) _154_2030))
in (_154_2031)::[])
end)
in (

let encode_elim = (fun _53_2728 -> (match (()) with
| () -> begin
(

let _53_2731 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_53_2731) with
| (head, args) -> begin
(match ((let _154_2034 = (FStar_Absyn_Util.compress_typ head)
in _154_2034.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let encoded_head = (lookup_free_tvar_name env' fv)
in (

let _53_2737 = (encode_args args env')
in (match (_53_2737) with
| (encoded_args, arg_decls) -> begin
(

let _53_2761 = (FStar_List.fold_left (fun _53_2741 arg -> (match (_53_2741) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(

let _53_2749 = (let _154_2037 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _154_2037))
in (match (_53_2749) with
| (_53_2746, tv, env) -> begin
(let _154_2039 = (let _154_2038 = (FStar_ToSMT_Term.mkEq ((targ), (tv)))
in (_154_2038)::eqns)
in ((env), ((tv)::arg_vars), (_154_2039)))
end))
end
| FStar_Util.Inr (varg) -> begin
(

let _53_2756 = (let _154_2040 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _154_2040))
in (match (_53_2756) with
| (_53_2753, xv, env) -> begin
(let _154_2042 = (let _154_2041 = (FStar_ToSMT_Term.mkEq ((varg), (xv)))
in (_154_2041)::eqns)
in ((env), ((xv)::arg_vars), (_154_2042)))
end))
end)
end)) ((env'), ([]), ([])) encoded_args)
in (match (_53_2761) with
| (_53_2758, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_ToSMT_Term.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _154_2049 = (let _154_2048 = (let _154_2047 = (let _154_2046 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _154_2045 = (let _154_2044 = (let _154_2043 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_154_2043)))
in (FStar_ToSMT_Term.mkImp _154_2044))
in ((((ty_pred)::[])::[]), (_154_2046), (_154_2045))))
in (FStar_ToSMT_Term.mkForall _154_2047))
in ((_154_2048), (Some ("data constructor typing elim"))))
in FStar_ToSMT_Term.Assume (_154_2049))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(

let x = (let _154_2050 = (varops.fresh "x")
in ((_154_2050), (FStar_ToSMT_Term.Term_sort)))
in (

let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _154_2060 = (let _154_2059 = (let _154_2058 = (let _154_2057 = (let _154_2052 = (let _154_2051 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_154_2051)::[])
in (_154_2052)::[])
in (let _154_2056 = (let _154_2055 = (let _154_2054 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _154_2053 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in ((_154_2054), (_154_2053))))
in (FStar_ToSMT_Term.mkImp _154_2055))
in ((_154_2057), ((x)::[]), (_154_2056))))
in (FStar_ToSMT_Term.mkForall _154_2058))
in ((_154_2059), (Some ("lextop is top"))))
in FStar_ToSMT_Term.Assume (_154_2060))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _154_2063 = (let _154_2062 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _154_2062 dapp))
in (_154_2063)::[])
end
| _53_2776 -> begin
(failwith "unexpected sort")
end))))
in (let _154_2070 = (let _154_2069 = (let _154_2068 = (let _154_2067 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _154_2066 = (let _154_2065 = (let _154_2064 = (FStar_ToSMT_Term.mk_and_l prec)
in ((ty_pred), (_154_2064)))
in (FStar_ToSMT_Term.mkImp _154_2065))
in ((((ty_pred)::[])::[]), (_154_2067), (_154_2066))))
in (FStar_ToSMT_Term.mkForall _154_2068))
in ((_154_2069), (Some ("subterm ordering"))))
in FStar_ToSMT_Term.Assume (_154_2070)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _53_2780 -> begin
(

let _53_2781 = (let _154_2073 = (let _154_2072 = (FStar_Absyn_Print.sli d)
in (let _154_2071 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _154_2072 _154_2071)))
in (FStar_Errors.warn drange _154_2073))
in (([]), ([])))
end)
end))
end))
in (

let _53_2785 = (encode_elim ())
in (match (_53_2785) with
| (decls2, elim) -> begin
(

let g = (let _154_2100 = (let _154_2099 = (let _154_2098 = (let _154_2097 = (let _154_2078 = (let _154_2077 = (let _154_2076 = (let _154_2075 = (let _154_2074 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _154_2074))
in Some (_154_2075))
in ((ddtok), ([]), (FStar_ToSMT_Term.Term_sort), (_154_2076)))
in FStar_ToSMT_Term.DeclFun (_154_2077))
in (_154_2078)::[])
in (let _154_2096 = (let _154_2095 = (let _154_2094 = (let _154_2093 = (let _154_2092 = (let _154_2091 = (let _154_2090 = (let _154_2082 = (let _154_2081 = (let _154_2080 = (let _154_2079 = (FStar_ToSMT_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_154_2079)))
in (FStar_ToSMT_Term.mkForall _154_2080))
in ((_154_2081), (Some ("equality for proxy"))))
in FStar_ToSMT_Term.Assume (_154_2082))
in (let _154_2089 = (let _154_2088 = (let _154_2087 = (let _154_2086 = (let _154_2085 = (let _154_2084 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) vars')
in (let _154_2083 = (FStar_ToSMT_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_154_2084), (_154_2083))))
in (FStar_ToSMT_Term.mkForall _154_2085))
in ((_154_2086), (Some ("data constructor typing intro"))))
in FStar_ToSMT_Term.Assume (_154_2087))
in (_154_2088)::[])
in (_154_2090)::_154_2089))
in (FStar_ToSMT_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")))))::_154_2091)
in (FStar_List.append _154_2092 elim))
in (FStar_List.append decls_pred _154_2093))
in (FStar_List.append decls_formals _154_2094))
in (FStar_List.append proxy_fresh _154_2095))
in (FStar_List.append _154_2097 _154_2096)))
in (FStar_List.append decls3 _154_2098))
in (FStar_List.append decls2 _154_2099))
in (FStar_List.append binder_decls _154_2100))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end)))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _53_2789, _53_2791, _53_2793) -> begin
(

let _53_2798 = (encode_signature env ses)
in (match (_53_2798) with
| (g, env) -> begin
(

let _53_2810 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___230 -> (match (uu___230) with
| FStar_ToSMT_Term.Assume (_53_2801, Some ("inversion axiom")) -> begin
false
end
| _53_2807 -> begin
true
end))))
in (match (_53_2810) with
| (g', inversions) -> begin
(

let _53_2819 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___231 -> (match (uu___231) with
| FStar_ToSMT_Term.DeclFun (_53_2813) -> begin
true
end
| _53_2816 -> begin
false
end))))
in (match (_53_2819) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_53_2821, _53_2823, _53_2825, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___232 -> (match (uu___232) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _53_2837 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _53_2842, _53_2844, quals) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _53_2856 = (FStar_Util.first_N nbinders formals)
in (match (_53_2856) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun formal binder -> (match ((((Prims.fst formal)), ((Prims.fst binder)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _154_2115 = (let _154_2114 = (FStar_Absyn_Util.btvar_to_typ b)
in ((a.FStar_Absyn_Syntax.v), (_154_2114)))
in FStar_Util.Inl (_154_2115))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _154_2117 = (let _154_2116 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_154_2116)))
in FStar_Util.Inr (_154_2117))
end
| _53_2870 -> begin
(failwith "Impossible")
end)) formals binders)
in (

let extra_formals = (let _154_2118 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _154_2118 FStar_Absyn_Util.name_binders))
in (

let body = (let _154_2124 = (let _154_2120 = (let _154_2119 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _154_2119))
in ((body), (_154_2120)))
in (let _154_2123 = (let _154_2122 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _154_2121 -> Some (_154_2121)) _154_2122))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _154_2124 _154_2123 body.FStar_Absyn_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_ascribed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (binders, body); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _, _)) | (FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Absyn_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Absyn_Util.is_total_comp c)) then begin
(

let _53_2908 = (FStar_Util.first_N nformals binders)
in (match (_53_2908) with
| (bs0, rest) -> begin
(

let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _53_2912 -> begin
(failwith "impossible")
end)
in (

let body = (FStar_Absyn_Syntax.mk_Exp_abs ((rest), (body)) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in ((bs0), (body), (bs0), (tres))))
end))
end else begin
if (nformals > nbinders) then begin
(

let _53_2917 = (eta_expand binders formals body tres)
in (match (_53_2917) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end
| _53_2919 -> begin
(let _154_2133 = (let _154_2132 = (FStar_Absyn_Print.exp_to_string e)
in (let _154_2131 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _154_2132 _154_2131)))
in (failwith _154_2133))
end)
end
| _53_2921 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(

let tres = (FStar_Absyn_Util.comp_result c)
in (

let _53_2929 = (eta_expand [] formals e tres)
in (match (_53_2929) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end
| _53_2931 -> begin
(([]), (e), ([]), (t_norm))
end)
end))
in try
(match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___233 -> (match (uu___233) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _53_2942 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(

let _53_2961 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _53_2948 lb -> (match (_53_2948) with
| (toks, typs, decls, env) -> begin
(

let _53_2950 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (let _154_2139 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _154_2139 FStar_Absyn_Util.compress_typ))
in (

let _53_2956 = (let _154_2140 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _154_2140 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_53_2956) with
| (tok, decl, env) -> begin
(let _154_2143 = (let _154_2142 = (let _154_2141 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in ((_154_2141), (tok)))
in (_154_2142)::toks)
in ((_154_2143), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_53_2961) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___234 -> (match (uu___234) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _53_2968 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _154_2146 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _154_2146))))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Absyn_Syntax.lbname = _53_2976; FStar_Absyn_Syntax.lbtyp = _53_2974; FStar_Absyn_Syntax.lbeff = _53_2972; FStar_Absyn_Syntax.lbdef = e})::[], (t_norm)::[], ((flid, (f, ftok)))::[]) -> begin
(

let _53_2992 = (destruct_bound_function flid t_norm e)
in (match (_53_2992) with
| (binders, body, formals, tres) -> begin
(

let _53_2999 = (encode_binders None binders env)
in (match (_53_2999) with
| (vars, guards, env', binder_decls, _53_2998) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV ((f), (FStar_ToSMT_Term.Term_sort)))
end
| _53_3002 -> begin
(let _154_2148 = (let _154_2147 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((f), (_154_2147)))
in (FStar_ToSMT_Term.mkApp _154_2148))
end)
in (

let _53_3006 = (encode_exp body env')
in (match (_53_3006) with
| (body, decls2) -> begin
(

let eqn = (let _154_2157 = (let _154_2156 = (let _154_2153 = (let _154_2152 = (let _154_2151 = (let _154_2150 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _154_2149 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_154_2150), (_154_2149))))
in (FStar_ToSMT_Term.mkImp _154_2151))
in ((((app)::[])::[]), (vars), (_154_2152)))
in (FStar_ToSMT_Term.mkForall _154_2153))
in (let _154_2155 = (let _154_2154 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_154_2154))
in ((_154_2156), (_154_2155))))
in FStar_ToSMT_Term.Assume (_154_2157))
in (((FStar_List.append decls (FStar_List.append binder_decls (FStar_List.append decls2 ((eqn)::[]))))), (env)))
end)))
end))
end))
end
| _53_3009 -> begin
(failwith "Impossible")
end)
end else begin
(

let fuel = (let _154_2158 = (varops.fresh "fuel")
in ((_154_2158), (FStar_ToSMT_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _53_3026 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _53_3015 _53_3020 -> (match (((_53_3015), (_53_3020))) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _154_2163 = (let _154_2162 = (FStar_ToSMT_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _154_2161 -> Some (_154_2161)) _154_2162))
in (push_free_var env flid gtok _154_2163))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env)))))
end)) (([]), (env))))
in (match (_53_3026) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _53_3035 t_norm _53_3044 -> (match (((_53_3035), (_53_3044))) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _53_3043; FStar_Absyn_Syntax.lbtyp = _53_3041; FStar_Absyn_Syntax.lbeff = _53_3039; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let _53_3049 = (destruct_bound_function flid t_norm e)
in (match (_53_3049) with
| (binders, body, formals, tres) -> begin
(

let _53_3056 = (encode_binders None binders env)
in (match (_53_3056) with
| (vars, guards, env', binder_decls, _53_3055) -> begin
(

let decl_g = (let _154_2174 = (let _154_2173 = (let _154_2172 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_154_2172)
in ((g), (_154_2173), (FStar_ToSMT_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_ToSMT_Term.DeclFun (_154_2174))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_ToSMT_Term.DeclFun (((gtok), ([]), (FStar_ToSMT_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let app = (FStar_ToSMT_Term.mkApp ((f), (vars_tm)))
in (

let gsapp = (let _154_2177 = (let _154_2176 = (let _154_2175 = (FStar_ToSMT_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_154_2175)::vars_tm)
in ((g), (_154_2176)))
in (FStar_ToSMT_Term.mkApp _154_2177))
in (

let gmax = (let _154_2180 = (let _154_2179 = (let _154_2178 = (FStar_ToSMT_Term.mkApp (("MaxFuel"), ([])))
in (_154_2178)::vars_tm)
in ((g), (_154_2179)))
in (FStar_ToSMT_Term.mkApp _154_2180))
in (

let _53_3066 = (encode_exp body env')
in (match (_53_3066) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _154_2189 = (let _154_2188 = (let _154_2185 = (let _154_2184 = (let _154_2183 = (let _154_2182 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _154_2181 = (FStar_ToSMT_Term.mkEq ((gsapp), (body_tm)))
in ((_154_2182), (_154_2181))))
in (FStar_ToSMT_Term.mkImp _154_2183))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_154_2184)))
in (FStar_ToSMT_Term.mkForall _154_2185))
in (let _154_2187 = (let _154_2186 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_154_2186))
in ((_154_2188), (_154_2187))))
in FStar_ToSMT_Term.Assume (_154_2189))
in (

let eqn_f = (let _154_2193 = (let _154_2192 = (let _154_2191 = (let _154_2190 = (FStar_ToSMT_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_154_2190)))
in (FStar_ToSMT_Term.mkForall _154_2191))
in ((_154_2192), (Some ("Correspondence of recursive function to instrumented version"))))
in FStar_ToSMT_Term.Assume (_154_2193))
in (

let eqn_g' = (let _154_2202 = (let _154_2201 = (let _154_2200 = (let _154_2199 = (let _154_2198 = (let _154_2197 = (let _154_2196 = (let _154_2195 = (let _154_2194 = (FStar_ToSMT_Term.n_fuel (Prims.parse_int "0"))
in (_154_2194)::vars_tm)
in ((g), (_154_2195)))
in (FStar_ToSMT_Term.mkApp _154_2196))
in ((gsapp), (_154_2197)))
in (FStar_ToSMT_Term.mkEq _154_2198))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_154_2199)))
in (FStar_ToSMT_Term.mkForall _154_2200))
in ((_154_2201), (Some ("Fuel irrelevance"))))
in FStar_ToSMT_Term.Assume (_154_2202))
in (

let _53_3089 = (

let _53_3076 = (encode_binders None formals env0)
in (match (_53_3076) with
| (vars, v_guards, env, binder_decls, _53_3075) -> begin
(

let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let gapp = (FStar_ToSMT_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _154_2203 = (FStar_ToSMT_Term.mkFreeV ((gtok), (FStar_ToSMT_Term.Term_sort)))
in (mk_ApplyE _154_2203 ((fuel)::vars)))
in (let _154_2207 = (let _154_2206 = (let _154_2205 = (let _154_2204 = (FStar_ToSMT_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_154_2204)))
in (FStar_ToSMT_Term.mkForall _154_2205))
in ((_154_2206), (Some ("Fuel token correspondence"))))
in FStar_ToSMT_Term.Assume (_154_2207)))
in (

let _53_3086 = (

let _53_3083 = (encode_typ_pred None tres env gapp)
in (match (_53_3083) with
| (g_typing, d3) -> begin
(let _154_2215 = (let _154_2214 = (let _154_2213 = (let _154_2212 = (let _154_2211 = (let _154_2210 = (let _154_2209 = (let _154_2208 = (FStar_ToSMT_Term.mk_and_l v_guards)
in ((_154_2208), (g_typing)))
in (FStar_ToSMT_Term.mkImp _154_2209))
in ((((gapp)::[])::[]), ((fuel)::vars), (_154_2210)))
in (FStar_ToSMT_Term.mkForall _154_2211))
in ((_154_2212), (None)))
in FStar_ToSMT_Term.Assume (_154_2213))
in (_154_2214)::[])
in ((d3), (_154_2215)))
end))
in (match (_53_3086) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_53_3089) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (

let _53_3105 = (let _154_2218 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _53_3093 _53_3097 -> (match (((_53_3093), (_53_3097))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _53_3101 = (encode_one_binding env0 gtok ty bs)
in (match (_53_3101) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _154_2218))
in (match (_53_3105) with
| (decls, eqns, env0) -> begin
(

let _53_3114 = (let _154_2220 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _154_2220 (FStar_List.partition (fun uu___235 -> (match (uu___235) with
| FStar_ToSMT_Term.DeclFun (_53_3108) -> begin
true
end
| _53_3111 -> begin
false
end)))))
in (match (_53_3114) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
end))
end))))
end)))))
end
end)))
end))
end
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (let _154_2223 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _154_2223 (FStar_String.concat " and ")))
in (

let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end)))))
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((Prims.string * FStar_ToSMT_Term.term Prims.option) * FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(

let _53_3141 = (encode_free_var env x t t_norm [])
in (match (_53_3141) with
| (decls, env) -> begin
(

let _53_3146 = (lookup_lid env x)
in (match (_53_3146) with
| (n, x', _53_3145) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _53_3150) -> begin
((((n), (x))), ([]), (env))
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_ToSMT_Term.decl Prims.list = (fun env lid t -> (

let _53_3158 = (encode_function_type_as_formula None None t env)
in (match (_53_3158) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _154_2236 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _154_2236)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(

let _53_3167 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3167) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _53_3170) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu___236 -> (match (uu___236) with
| (FStar_Util.Inl (_53_3175), _53_3178) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3181 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _53_3183 -> begin
[]
end)
in (

let d = FStar_ToSMT_Term.DeclFun (((vname), (arg_sorts), (FStar_ToSMT_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_ToSMT_Term.DeclFun (((vtok), ([]), (FStar_ToSMT_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end else begin
if (prims.is lid) then begin
(

let vname = (varops.new_fvar lid)
in (

let definition = (prims.mk lid vname)
in (

let env = (push_free_var env lid vname None)
in ((definition), (env)))))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _53_3200 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _154_2238 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_154_2238)))
end else begin
((args), (((None), ((FStar_Absyn_Util.comp_result comp)))))
end
end
| None -> begin
(([]), (((None), (t_norm))))
end)
in (match (_53_3200) with
| (formals, (pre_opt, res_t)) -> begin
(

let _53_3204 = (new_term_constant_and_tok_from_lid env lid)
in (match (_53_3204) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV ((vname), (FStar_ToSMT_Term.Term_sort)))
end
| _53_3207 -> begin
(FStar_ToSMT_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___237 -> (match (uu___237) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(

let _53_3223 = (FStar_Util.prefix vars)
in (match (_53_3223) with
| (_53_3218, (xxsym, _53_3221)) -> begin
(

let xx = (FStar_ToSMT_Term.mkFreeV ((xxsym), (FStar_ToSMT_Term.Term_sort)))
in (let _154_2255 = (let _154_2254 = (let _154_2253 = (let _154_2252 = (let _154_2251 = (let _154_2250 = (let _154_2249 = (let _154_2248 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _154_2248))
in ((vapp), (_154_2249)))
in (FStar_ToSMT_Term.mkEq _154_2250))
in ((((vapp)::[])::[]), (vars), (_154_2251)))
in (FStar_ToSMT_Term.mkForall _154_2252))
in ((_154_2253), (Some ("Discriminator equation"))))
in FStar_ToSMT_Term.Assume (_154_2254))
in (_154_2255)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(

let _53_3236 = (FStar_Util.prefix vars)
in (match (_53_3236) with
| (_53_3231, (xxsym, _53_3234)) -> begin
(

let xx = (FStar_ToSMT_Term.mkFreeV ((xxsym), (FStar_ToSMT_Term.Term_sort)))
in (

let prim_app = (let _154_2257 = (let _154_2256 = (mk_term_projector_name d f)
in ((_154_2256), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _154_2257))
in (let _154_2262 = (let _154_2261 = (let _154_2260 = (let _154_2259 = (let _154_2258 = (FStar_ToSMT_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_154_2258)))
in (FStar_ToSMT_Term.mkForall _154_2259))
in ((_154_2260), (Some ("Projector equation"))))
in FStar_ToSMT_Term.Assume (_154_2261))
in (_154_2262)::[])))
end))
end
| _53_3240 -> begin
[]
end)))))
in (

let _53_3247 = (encode_binders None formals env)
in (match (_53_3247) with
| (vars, guards, env', decls1, _53_3246) -> begin
(

let _53_3256 = (match (pre_opt) with
| None -> begin
(let _154_2263 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_154_2263), (decls1)))
end
| Some (p) -> begin
(

let _53_3253 = (encode_formula p env')
in (match (_53_3253) with
| (g, ds) -> begin
(let _154_2264 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in ((_154_2264), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_53_3256) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_ApplyE vtok_tm vars)
in (

let vapp = (let _154_2266 = (let _154_2265 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((vname), (_154_2265)))
in (FStar_ToSMT_Term.mkApp _154_2266))
in (

let _53_3287 = (

let vname_decl = (let _154_2269 = (let _154_2268 = (FStar_All.pipe_right formals (FStar_List.map (fun uu___238 -> (match (uu___238) with
| (FStar_Util.Inl (_53_3261), _53_3264) -> begin
FStar_ToSMT_Term.Type_sort
end
| _53_3267 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in ((vname), (_154_2268), (FStar_ToSMT_Term.Term_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_154_2269))
in (

let _53_3274 = (

let env = (

let _53_3269 = env
in {bindings = _53_3269.bindings; depth = _53_3269.depth; tcenv = _53_3269.tcenv; warn = _53_3269.warn; cache = _53_3269.cache; nolabels = _53_3269.nolabels; use_zfuel_name = _53_3269.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_53_3274) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_ToSMT_Term.Assume (((tok_typing), (Some ("function token typing"))))
in (

let _53_3284 = (match (formals) with
| [] -> begin
(let _154_2273 = (let _154_2272 = (let _154_2271 = (FStar_ToSMT_Term.mkFreeV ((vname), (FStar_ToSMT_Term.Term_sort)))
in (FStar_All.pipe_left (fun _154_2270 -> Some (_154_2270)) _154_2271))
in (push_free_var env lid vname _154_2272))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_154_2273)))
end
| _53_3278 -> begin
(

let vtok_decl = FStar_ToSMT_Term.DeclFun (((vtok), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _154_2274 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((vtok), (FStar_ToSMT_Term.Term_sort)) _154_2274))
in (

let name_tok_corr = (let _154_2278 = (let _154_2277 = (let _154_2276 = (let _154_2275 = (FStar_ToSMT_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::[]), (vars), (_154_2275)))
in (FStar_ToSMT_Term.mkForall _154_2276))
in ((_154_2277), (None)))
in FStar_ToSMT_Term.Assume (_154_2278))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_53_3284) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_53_3287) with
| (decls2, env) -> begin
(

let _53_3295 = (

let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (

let _53_3291 = (encode_typ_term res_t env')
in (match (_53_3291) with
| (encoded_res_t, decls) -> begin
(let _154_2279 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_154_2279), (decls)))
end)))
in (match (_53_3295) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _154_2283 = (let _154_2282 = (let _154_2281 = (let _154_2280 = (FStar_ToSMT_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_154_2280)))
in (FStar_ToSMT_Term.mkForall _154_2281))
in ((_154_2282), (Some ("free var typing"))))
in FStar_ToSMT_Term.Assume (_154_2283))
in (

let g = (let _154_2287 = (let _154_2286 = (let _154_2285 = (let _154_2284 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_154_2284)
in (FStar_List.append decls3 _154_2285))
in (FStar_List.append decls2 _154_2286))
in (FStar_List.append decls1 _154_2287))
in ((g), (env))))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _53_3302 se -> (match (_53_3302) with
| (g, env) -> begin
(

let _53_3306 = (encode_sigelt env se)
in (match (_53_3306) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_Tc_Env.binding Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _53_3313 -> (match (_53_3313) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(

let _53_3321 = (new_term_constant env x)
in (match (_53_3321) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (

let _53_3323 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _154_2302 = (FStar_Absyn_Print.strBvd x)
in (let _154_2301 = (FStar_Absyn_Print.typ_to_string t0)
in (let _154_2300 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _154_2302 _154_2301 _154_2300))))
end else begin
()
end
in (

let _53_3327 = (encode_typ_pred None t1 env xx)
in (match (_53_3327) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _154_2306 = (let _154_2305 = (FStar_Absyn_Print.strBvd x)
in (let _154_2304 = (FStar_Absyn_Print.typ_to_string t0)
in (let _154_2303 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _154_2305 _154_2304 _154_2303))))
in Some (_154_2306))
end else begin
None
end
in (

let g = (FStar_List.append ((FStar_ToSMT_Term.DeclFun (((xxsym), ([]), (FStar_ToSMT_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((FStar_ToSMT_Term.Assume (((t), (None))))::[])))
in (((FStar_List.append decls g)), (env'))))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(

let _53_3337 = (new_typ_constant env a)
in (match (_53_3337) with
| (aasym, aa, env') -> begin
(

let _53_3340 = (encode_knd k env aa)
in (match (_53_3340) with
| (k, decls') -> begin
(

let g = (let _154_2311 = (let _154_2310 = (let _154_2309 = (let _154_2308 = (let _154_2307 = (FStar_Absyn_Print.strBvd a)
in Some (_154_2307))
in ((aasym), ([]), (FStar_ToSMT_Term.Type_sort), (_154_2308)))
in FStar_ToSMT_Term.DeclFun (_154_2309))
in (_154_2310)::[])
in (FStar_List.append _154_2311 (FStar_List.append decls' ((FStar_ToSMT_Term.Assume (((k), (None))))::[]))))
in (((FStar_List.append decls g)), (env')))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(

let t_norm = (whnf env t)
in (

let _53_3349 = (encode_free_var env x t t_norm [])
in (match (_53_3349) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(

let _53_3354 = (encode_sigelt env se)
in (match (_53_3354) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings (([]), (env)))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _53_3361 -> (match (_53_3361) with
| (l, _53_3358, _53_3360) -> begin
FStar_ToSMT_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_ToSMT_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _53_3368 -> (match (_53_3368) with
| (l, _53_3365, _53_3367) -> begin
(let _154_2319 = (FStar_All.pipe_left (fun _154_2315 -> FStar_ToSMT_Term.Echo (_154_2315)) (Prims.fst l))
in (let _154_2318 = (let _154_2317 = (let _154_2316 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_154_2316))
in (_154_2317)::[])
in (_154_2319)::_154_2318))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (let _154_2324 = (let _154_2323 = (let _154_2322 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _154_2322; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_154_2323)::[])
in (FStar_ST.op_Colon_Equals last_env _154_2324)))


let get_env : FStar_Tc_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::_53_3374 -> begin
(

let _53_3377 = e
in {bindings = _53_3377.bindings; depth = _53_3377.depth; tcenv = tcenv; warn = _53_3377.warn; cache = _53_3377.cache; nolabels = _53_3377.nolabels; use_zfuel_name = _53_3377.use_zfuel_name; encode_non_total_function_typ = _53_3377.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(failwith "Empty env stack")
end
| (_53_3383)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _53_3385 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let _53_3391 = hd
in {bindings = _53_3391.bindings; depth = _53_3391.depth; tcenv = _53_3391.tcenv; warn = _53_3391.warn; cache = refs; nolabels = _53_3391.nolabels; use_zfuel_name = _53_3391.use_zfuel_name; encode_non_total_function_typ = _53_3391.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _53_3394 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (_53_3398)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _53_3400 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _53_3401 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _53_3402 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_53_3405)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _53_3410 -> begin
(failwith "Impossible")
end)
end))


let init : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (

let _53_3412 = (init_env tcenv)
in (

let _53_3414 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _53_3417 = (push_env ())
in (

let _53_3419 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _53_3422 = (let _154_2345 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _154_2345))
in (

let _53_3424 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _53_3427 = (mark_env ())
in (

let _53_3429 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _53_3432 = (reset_mark_env ())
in (

let _53_3434 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _53_3437 = (commit_mark_env ())
in (

let _53_3439 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))


let encode_sig : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _154_2359 = (let _154_2358 = (let _154_2357 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _154_2357))
in FStar_ToSMT_Term.Caption (_154_2358))
in (_154_2359)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _53_3448 = (encode_sigelt env se)
in (match (_53_3448) with
| (decls, env) -> begin
(

let _53_3449 = (set_env env)
in (let _154_2360 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _154_2360)))
end)))))


let encode_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (

let _53_3454 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _154_2365 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "Encoding externals for %s ... %s exports\n" name _154_2365))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _53_3461 = (encode_signature (

let _53_3457 = env
in {bindings = _53_3457.bindings; depth = _53_3457.depth; tcenv = _53_3457.tcenv; warn = false; cache = _53_3457.cache; nolabels = _53_3457.nolabels; use_zfuel_name = _53_3457.use_zfuel_name; encode_non_total_function_typ = _53_3457.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_53_3461) with
| (decls, env) -> begin
(

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (

let _53_3467 = (set_env (

let _53_3465 = env
in {bindings = _53_3465.bindings; depth = _53_3465.depth; tcenv = _53_3465.tcenv; warn = true; cache = _53_3465.cache; nolabels = _53_3465.nolabels; use_zfuel_name = _53_3465.use_zfuel_name; encode_non_total_function_typ = _53_3465.encode_non_total_function_typ}))
in (

let _53_3469 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))


let solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (

let _53_3474 = (let _154_2374 = (let _154_2373 = (let _154_2372 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _154_2372))
in (FStar_Util.format1 "Starting query at %s" _154_2373))
in (push _154_2374))
in (

let pop = (fun _53_3477 -> (match (()) with
| () -> begin
(let _154_2379 = (let _154_2378 = (let _154_2377 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _154_2377))
in (FStar_Util.format1 "Ending query at %s" _154_2378))
in (pop _154_2379))
end))
in (

let _53_3536 = (

let env = (get_env tcenv)
in (

let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _53_3510 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_Tc_Env.Binding_var (x, t))::rest -> begin
(

let _53_3492 = (aux rest)
in (match (_53_3492) with
| (out, rest) -> begin
(

let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
in (let _154_2385 = (let _154_2384 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_154_2384)::out)
in ((_154_2385), (rest))))
end))
end
| (FStar_Tc_Env.Binding_typ (a, k))::rest -> begin
(

let _53_3502 = (aux rest)
in (match (_53_3502) with
| (out, rest) -> begin
(let _154_2387 = (let _154_2386 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_154_2386)::out)
in ((_154_2387), (rest)))
end))
end
| _53_3504 -> begin
(([]), (bindings))
end))
in (

let _53_3507 = (aux bindings)
in (match (_53_3507) with
| (closing, bindings) -> begin
(let _154_2388 = (FStar_Absyn_Util.close_forall (FStar_List.rev closing) q)
in ((_154_2388), (bindings)))
end)))
in (match (_53_3510) with
| (q, bindings) -> begin
(

let _53_3519 = (let _154_2390 = (FStar_List.filter (fun uu___239 -> (match (uu___239) with
| FStar_Tc_Env.Binding_sig (_53_3513) -> begin
false
end
| _53_3516 -> begin
true
end)) bindings)
in (encode_env_bindings env _154_2390))
in (match (_53_3519) with
| (env_decls, env) -> begin
(

let _53_3520 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _154_2391 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _154_2391))
end else begin
()
end
in (

let _53_3525 = (encode_formula_with_labels q env)
in (match (_53_3525) with
| (phi, labels, qdecls) -> begin
(

let _53_3528 = (encode_labels labels)
in (match (_53_3528) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _154_2393 = (let _154_2392 = (FStar_ToSMT_Term.mkNot phi)
in ((_154_2392), (Some ("query"))))
in FStar_ToSMT_Term.Assume (_154_2393))
in (

let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end)))
end))
end))))
in (match (_53_3536) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _53_3543); FStar_ToSMT_Term.hash = _53_3540; FStar_ToSMT_Term.freevars = _53_3538}, _53_3548) -> begin
(

let _53_3551 = (pop ())
in ())
end
| _53_3554 when tcenv.FStar_Tc_Env.admit -> begin
(

let _53_3555 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _53_3559) -> begin
(

let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= (Prims.parse_int "2048"))
in (

let _53_3563 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (

let with_fuel = (fun p _53_3569 -> (match (_53_3569) with
| (n, i) -> begin
(let _154_2416 = (let _154_2415 = (let _154_2400 = (let _154_2399 = (FStar_Util.string_of_int n)
in (let _154_2398 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _154_2399 _154_2398)))
in FStar_ToSMT_Term.Caption (_154_2400))
in (let _154_2414 = (let _154_2413 = (let _154_2405 = (let _154_2404 = (let _154_2403 = (let _154_2402 = (FStar_ToSMT_Term.mkApp (("MaxFuel"), ([])))
in (let _154_2401 = (FStar_ToSMT_Term.n_fuel n)
in ((_154_2402), (_154_2401))))
in (FStar_ToSMT_Term.mkEq _154_2403))
in ((_154_2404), (None)))
in FStar_ToSMT_Term.Assume (_154_2405))
in (let _154_2412 = (let _154_2411 = (let _154_2410 = (let _154_2409 = (let _154_2408 = (let _154_2407 = (FStar_ToSMT_Term.mkApp (("MaxIFuel"), ([])))
in (let _154_2406 = (FStar_ToSMT_Term.n_fuel i)
in ((_154_2407), (_154_2406))))
in (FStar_ToSMT_Term.mkEq _154_2408))
in ((_154_2409), (None)))
in FStar_ToSMT_Term.Assume (_154_2410))
in (_154_2411)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_154_2413)::_154_2412))
in (_154_2415)::_154_2414))
in (FStar_List.append _154_2416 suffix))
end))
in (

let check = (fun p -> (

let initial_config = (let _154_2420 = (FStar_Options.initial_fuel ())
in (let _154_2419 = (FStar_Options.initial_ifuel ())
in ((_154_2420), (_154_2419))))
in (

let alt_configs = (let _154_2439 = (let _154_2438 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _154_2423 = (let _154_2422 = (FStar_Options.initial_fuel ())
in (let _154_2421 = (FStar_Options.max_ifuel ())
in ((_154_2422), (_154_2421))))
in (_154_2423)::[])
end else begin
[]
end
in (let _154_2437 = (let _154_2436 = if (((FStar_Options.max_fuel ()) / (Prims.parse_int "2")) > (FStar_Options.initial_fuel ())) then begin
(let _154_2426 = (let _154_2425 = ((FStar_Options.max_fuel ()) / (Prims.parse_int "2"))
in (let _154_2424 = (FStar_Options.max_ifuel ())
in ((_154_2425), (_154_2424))))
in (_154_2426)::[])
end else begin
[]
end
in (let _154_2435 = (let _154_2434 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _154_2429 = (let _154_2428 = (FStar_Options.max_fuel ())
in (let _154_2427 = (FStar_Options.max_ifuel ())
in ((_154_2428), (_154_2427))))
in (_154_2429)::[])
end else begin
[]
end
in (let _154_2433 = (let _154_2432 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _154_2431 = (let _154_2430 = (FStar_Options.min_fuel ())
in ((_154_2430), ((Prims.parse_int "1"))))
in (_154_2431)::[])
end else begin
[]
end
in (_154_2432)::[])
in (_154_2434)::_154_2433))
in (_154_2436)::_154_2435))
in (_154_2438)::_154_2437))
in (FStar_List.flatten _154_2439))
in (

let report = (fun errs -> (

let errs = (match (errs) with
| [] -> begin
((("Unknown assertion failed"), (FStar_Absyn_Syntax.dummyRange)))::[]
end
| _53_3578 -> begin
errs
end)
in (

let _53_3580 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _154_2447 = (let _154_2442 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _154_2442))
in (let _154_2446 = (let _154_2443 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _154_2443 FStar_Util.string_of_int))
in (let _154_2445 = (let _154_2444 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _154_2444 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _154_2447 _154_2446 _154_2445))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (

let rec try_alt_configs = (fun p errs uu___240 -> (match (uu___240) with
| [] -> begin
(report errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _154_2458 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _154_2458 (cb mi p [])))
end
| _53_3592 -> begin
(report errs)
end)
end
| (mi)::tl -> begin
(let _154_2460 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _154_2460 (fun _53_3598 -> (match (_53_3598) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl ((ok), (errs')))
end
| _53_3601 -> begin
(cb mi p tl ((ok), (errs)))
end)
end))))
end))
and cb = (fun _53_3604 p alt _53_3609 -> (match (((_53_3604), (_53_3609))) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _154_2468 = (let _154_2465 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _154_2465))
in (let _154_2467 = (FStar_Util.string_of_int prev_fuel)
in (let _154_2466 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _154_2468 _154_2467 _154_2466))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _154_2469 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _154_2469 (cb initial_config p alt_configs))))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let _53_3614 = (let _154_2475 = (FStar_Options.split_cases ())
in (FStar_ToSMT_SplitQueryCases.can_handle_query _154_2475 q))
in (match (_53_3614) with
| (b, cb) -> begin
if b then begin
(FStar_ToSMT_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in (

let _53_3615 = if (FStar_Options.admit_smt_queries ()) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _53_3618 -> begin
(Prims.raise Bad_form)
end)
end)))))


let is_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _53_3622 = (push "query")
in (

let _53_3629 = (encode_formula_with_labels q env)
in (match (_53_3629) with
| (f, _53_3626, _53_3628) -> begin
(

let _53_3630 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _53_3634) -> begin
true
end
| _53_3638 -> begin
false
end))
end)))))


let solver : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}


let dummy : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = (fun _53_3639 -> ()); FStar_Tc_Env.push = (fun _53_3641 -> ()); FStar_Tc_Env.pop = (fun _53_3643 -> ()); FStar_Tc_Env.mark = (fun _53_3645 -> ()); FStar_Tc_Env.reset_mark = (fun _53_3647 -> ()); FStar_Tc_Env.commit_mark = (fun _53_3649 -> ()); FStar_Tc_Env.encode_modul = (fun _53_3651 _53_3653 -> ()); FStar_Tc_Env.encode_sig = (fun _53_3655 _53_3657 -> ()); FStar_Tc_Env.solve = (fun _53_3659 _53_3661 -> ()); FStar_Tc_Env.is_trivial = (fun _53_3663 _53_3665 -> false); FStar_Tc_Env.finish = (fun _53_3667 -> ()); FStar_Tc_Env.refresh = (fun _53_3668 -> ())}




